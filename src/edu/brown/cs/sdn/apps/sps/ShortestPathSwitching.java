package edu.brown.cs.sdn.apps.sps;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.LinkedList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import edu.brown.cs.sdn.apps.util.Host;

import edu.brown.cs.sdn.apps.util.SwitchCommands;
import net.floodlightcontroller.packet.Ethernet;
import org.openflow.protocol.OFMatch;
import org.openflow.protocol.OFPort;

import org.openflow.protocol.action.OFAction;
import org.openflow.protocol.action.OFActionOutput;
import org.openflow.protocol.instruction.OFInstruction;
import org.openflow.protocol.instruction.OFInstructionApplyActions;

import net.floodlightcontroller.core.IFloodlightProviderService;
import net.floodlightcontroller.core.IOFSwitch;
import net.floodlightcontroller.core.IOFSwitch.PortChangeType;
import net.floodlightcontroller.core.IOFSwitchListener;
import net.floodlightcontroller.core.ImmutablePort;
import net.floodlightcontroller.core.module.FloodlightModuleContext;
import net.floodlightcontroller.core.module.FloodlightModuleException;
import net.floodlightcontroller.core.module.IFloodlightModule;
import net.floodlightcontroller.core.module.IFloodlightService;
import net.floodlightcontroller.devicemanager.IDevice;
import net.floodlightcontroller.devicemanager.IDeviceListener;
import net.floodlightcontroller.devicemanager.IDeviceService;
import net.floodlightcontroller.linkdiscovery.ILinkDiscoveryListener;
import net.floodlightcontroller.linkdiscovery.ILinkDiscoveryService;
import net.floodlightcontroller.routing.Link;

public class ShortestPathSwitching implements IFloodlightModule, IOFSwitchListener, 
		ILinkDiscoveryListener, IDeviceListener, InterfaceShortestPathSwitching
{
	public static final String MODULE_NAME = ShortestPathSwitching.class.getSimpleName();
	
	// Interface to the logging system
    private static Logger log = LoggerFactory.getLogger(MODULE_NAME);
    
    // Interface to Floodlight core for interacting with connected switches
    private IFloodlightProviderService floodlightProv;

    // Interface to link discovery service
    private ILinkDiscoveryService linkDiscProv;

    // Interface to device manager service
    private IDeviceService deviceProv;
    
    // Switch table in which rules should be installed
    private byte table;
    
    // Map of hosts to devices
    private Map<IDevice,Host> knownHosts;


	// Helper: build spanning tree ports for broadcast flooding without loops.

	private Map<Long, Set<Integer>> build_spanning_tree_ports()
	{
		Map<Long, Set<Integer>> treePorts = new HashMap<Long, Set<Integer>>();
		Map<Long, IOFSwitch> switches = this.getSwitches();
		Collection<Link> links = this.getLinks();

		if (switches.isEmpty())
		{
			return treePorts;
		}

		Long root = switches.keySet().iterator().next();

		Set<Long> visited = new HashSet<Long>();
		Queue<Long> queue = new LinkedList<Long>();

		visited.add(root);
		queue.add(root);

		while (!queue.isEmpty())
		{
			Long current = queue.poll();

			for (Link link : links)
			{
				Long neighbor = null;
				Integer currentOutPort = null;
				Integer neighborOutPort = null;

				if (link.getSrc() == current.longValue())
				{
					neighbor = link.getDst();
					currentOutPort = link.getSrcPort();
					neighborOutPort = link.getDstPort();
				}
				else if (link.getDst() == current.longValue())
				{
					neighbor = link.getSrc();
					currentOutPort = link.getDstPort();
					neighborOutPort = link.getSrcPort();
				}
				else
				{
					continue;
				}

				if (!switches.containsKey(neighbor) || visited.contains(neighbor))
				{
					continue;
				}

				if (!treePorts.containsKey(current))
				{
					treePorts.put(current, new HashSet<Integer>());
				}
				treePorts.get(current).add(currentOutPort);

				if (!treePorts.containsKey(neighbor))
				{
					treePorts.put(neighbor, new HashSet<Integer>());
				}
				treePorts.get(neighbor).add(neighborOutPort);

				visited.add(neighbor);
				queue.add(neighbor);
			}
		}

		return treePorts;
	}


	//Helper: get host ports per switch.

	private Map<Long, Set<Integer>> get_host_ports()
	{
		Map<Long, Set<Integer>> hostPorts = new HashMap<Long, Set<Integer>>();
		for (Host host : this.getHosts())
		{
			if (!host.isAttachedToSwitch()) continue;
			Long sw = host.getSwitch().getId();
			Integer port = host.getPort();
			Set<Integer> ports = hostPorts.get(sw);
			if (ports == null) { ports = new HashSet<Integer>(); hostPorts.put(sw, ports); }
			ports.add(port);
		}
		return hostPorts;
	}

	//Helper: remove existing broadcast rules (match on dst ff:ff:ff:ff:ff:ff)
	private void remove_broadcast_rules()
	{
		OFMatch match = new OFMatch();
		match.setDataLayerDestination("ff:ff:ff:ff:ff:ff");

		Map<Long, IOFSwitch> switches = this.getSwitches();
		for (Long switchId : switches.keySet())
		{
			IOFSwitch sw = switches.get(switchId);
			if (sw != null)
			{
				SwitchCommands.removeRules(sw, this.table, match);
			}
		}
	}

	/*
	 * Helper: install broadcast rules only along the spanning tree and to hosts.
	 */
	private void install_broadcast_tree_rules()
	{
		Map<Long, Set<Integer>> treePorts = this.build_spanning_tree_ports();
		Map<Long, Set<Integer>> hostPorts = this.get_host_ports();

		Map<Long, IOFSwitch> switches = this.getSwitches();

		for (Long switchId : switches.keySet())
		{
			IOFSwitch sw = switches.get(switchId);
			if (sw == null) continue;

			Set<Integer> tree = treePorts.get(switchId);
			Set<Integer> hosts = hostPorts.get(switchId);

			// union of tree and host ports
			Set<Integer> allOut = new HashSet<Integer>();
			if (tree != null) allOut.addAll(tree);
			if (hosts != null) allOut.addAll(hosts);

			if (allOut.isEmpty()) {
				continue;
			}

			// for every possible incoming port (tree or host), install a rule
			for (Integer inPort : allOut)
			{
				OFMatch match = new OFMatch();
				match.setDataLayerDestination("ff:ff:ff:ff:ff:ff");
				match.setInPort(inPort.intValue());

				ArrayList<OFAction> actions = new ArrayList<OFAction>();

				// output to all tree ports except inPort
				if (tree != null)
				{
					for (Integer outPort : tree)
					{
						if (outPort.equals(inPort)) continue;
						actions.add(new OFActionOutput(outPort.shortValue()));
					}
				}

				// output to all host ports except inPort
				if (hosts != null)
				{
					for (Integer outPort : hosts)
					{
						if (outPort.equals(inPort)) continue;
						actions.add(new OFActionOutput(outPort.shortValue()));
					}
				}

				// always send to controller for learning
				actions.add(new OFActionOutput(OFPort.OFPP_CONTROLLER.getValue()));

				OFInstruction instruction = new OFInstructionApplyActions(actions);

				SwitchCommands.installRule(sw, this.table, (short)(SwitchCommands.DEFAULT_PRIORITY - 1), match, Arrays.asList(instruction));
			}
		}
	}

	/**
     * Loads dependencies and initializes data structures.
     */
	@Override
	public void init(FloodlightModuleContext context)
			throws FloodlightModuleException 
	{
		log.info(String.format("Initializing %s...", MODULE_NAME));
		Map<String,String> config = context.getConfigParams(this);
        this.table = Byte.parseByte(config.get("table"));
        
		this.floodlightProv = context.getServiceImpl(
				IFloodlightProviderService.class);
        this.linkDiscProv = context.getServiceImpl(ILinkDiscoveryService.class);
        this.deviceProv = context.getServiceImpl(IDeviceService.class);
        
        this.knownHosts = new ConcurrentHashMap<IDevice,Host>();
        
        /*********************************************************************/
        /* TODO: Initialize other class variables, if necessary              */
        
        /*********************************************************************/
	}

	/**
     * Subscribes to events and performs other startup tasks.
     */
	@Override
	public void startUp(FloodlightModuleContext context)
			throws FloodlightModuleException 
	{
		log.info(String.format("Starting %s...", MODULE_NAME));
		this.floodlightProv.addOFSwitchListener(this);
		this.linkDiscProv.addListener(this);
		this.deviceProv.addListener(this);
		
		/*********************************************************************/
		/* TODO: Perform other tasks, if necessary                           */
		
		/*********************************************************************/
	}
	
	/**
	 * Get the table in which this application installs rules.
	 */
	public byte getTable()
	{ return this.table; }
	
    /**
     * Get a list of all known hosts in the network.
     */
    private Collection<Host> getHosts()
    { return this.knownHosts.values(); }
	
    /**
     * Get a map of all active switches in the network. Switch DPID is used as
     * the key.
     */
	private Map<Long, IOFSwitch> getSwitches()
    { return floodlightProv.getAllSwitchMap(); }
	
    /**
     * Get a list of all active links in the network.
     */
    private Collection<Link> getLinks()
    { return linkDiscProv.getLinks().keySet(); }

	/**
     * fix: install table-miss rule so unknown packets are sent to the controller.
     */
	private void install_table_miss(IOFSwitch sw)
	{
		if (sw == null)
		{
			return;
		}

		OFMatch match = new OFMatch();

		OFAction action = new OFActionOutput(OFPort.OFPP_CONTROLLER.getValue());
		OFInstruction instruction =
				new OFInstructionApplyActions(Arrays.asList(action));

		SwitchCommands.installRule(
				sw,
				this.table,
				(short)0,
				match,
				Arrays.asList(instruction));
	}

	/**
     * fix: refresh known hosts from Floodlight device manager.
     */
	private void refresh_known_hosts()
	{
		for (IDevice device : this.deviceProv.getAllDevices())
		{
			Host host = new Host(device, this.floodlightProv);

			if (host.getIPv4Address() != null && host.isAttachedToSwitch())
			{
				this.knownHosts.put(device, host);
			}
		}
	}

    /**
     * Recompute helper.
     */
	private void compute_rules()
	{
		this.refresh_known_hosts();
		// remove any existing broadcast-handling rules and reinstall along spanning tree
		this.remove_broadcast_rules();
		for (Host host : this.getHosts())
		{
			this.remove_rules(host);
			this.update_rules(host);
		}
		this.install_broadcast_tree_rules();
	}

	/**
     * Update helper.
     */
	private void update_rules(Host host) // temp
	{
		if (host != null && host.getIPv4Address() != null && host.isAttachedToSwitch())
		{
			Map<Long, Integer> nextPort = this.shortest_path_bellman_ford(
					host.getSwitch().getId(),
					this.getSwitches(),
					this.getLinks()
					);

			nextPort.put(host.getSwitch().getId(), host.getPort());

			OFMatch match = new OFMatch();
			match.setDataLayerType(Ethernet.TYPE_IPv4);
			match.setNetworkDestination(OFMatch.ETH_TYPE_IPV4, host.getIPv4Address());

			for (Long switchId : nextPort.keySet())
			{
				IOFSwitch sw = this.getSwitches().get(switchId);

				if (sw != null)
				{
					Integer port = nextPort.get(switchId);

					OFAction action = new OFActionOutput(port.shortValue());
					OFInstruction instruction = new OFInstructionApplyActions(Arrays.asList(action));

					SwitchCommands.installRule(
							sw,
							this.table,
							SwitchCommands.DEFAULT_PRIORITY,
							match,
							Arrays.asList(instruction));
				}
			}
		}
	}

    /**
     * Remove helper.
     */
	private void remove_rules(Host host)
	{
		if (host != null)
		{
			Integer hostIp = host.getIPv4Address();

			if (hostIp != null)
			{
				OFMatch match = new OFMatch();
				match.setDataLayerType(Ethernet.TYPE_IPv4);
				match.setNetworkDestination(OFMatch.ETH_TYPE_IPV4, hostIp);

				Map<Long, IOFSwitch> switches = this.getSwitches();

				for (Long switchId : switches.keySet())
				{
					IOFSwitch sw = switches.get(switchId);

					if (sw != null)
					{
						SwitchCommands.removeRules(sw, this.table, match);
					}
				}
			}
		}
	}

	private Map<Long, Integer> shortest_path_bellman_ford(
        Long dstSwitchId,
        Map<Long, IOFSwitch> switches,
        Collection<Link> links)
	{
		Map<Long, Integer> nextPort = new HashMap<Long, Integer>();
		Map<Long, Integer> dist = new HashMap<Long, Integer>();

		int INF = 1000000;
		int weight = 1;   // not sure if true, verify latter

		for (Long switchId : switches.keySet())
		{
			dist.put(switchId, INF);
		}

		dist.put(dstSwitchId, 0);

		for (int i = 0; i < switches.size() - 1; i++)
		{
			for (Link link : links)
			{
				Long src = link.getSrc();
				Long dst = link.getDst();

				if (!switches.containsKey(src) || !switches.containsKey(dst))
				{
					continue;
				}

				if (dist.get(src) + weight < dist.get(dst))
				{
					dist.put(dst, dist.get(src) + weight);
					nextPort.put(dst, link.getDstPort());
				}

				if (dist.get(dst) + weight < dist.get(src))
				{
					dist.put(src, dist.get(dst) + weight);
					nextPort.put(src, link.getSrcPort());
				}
			}
		}

		return nextPort;
	}

    /**
     * Event handler called when a host joins the network.
     * @param device information about the host
     */
	@Override
	public void deviceAdded(IDevice device) 
	{
		Host host = new Host(device, this.floodlightProv);
		// We only care about a new host if we know its IP
		if (host.getIPv4Address() != null)
		{
			log.info(String.format("Host %s added", host.getName()));
			this.knownHosts.put(device, host);
			
			/*****************************************************************/
			/* TODO: Update routing: add rules to route to new host          */
			this.compute_rules();
			/*****************************************************************/
		}
	}

	/**
     * Event handler called when a host is no longer attached to a switch.
     * @param device information about the host
     */
	@Override
	public void deviceRemoved(IDevice device) 
	{
		Host host = this.knownHosts.get(device);
		if (null == host)
		{
			host = new Host(device, this.floodlightProv);
			this.knownHosts.put(device, host);
		}
		
		log.info(String.format("Host %s is no longer attached to a switch", 
				host.getName()));
		
		/*********************************************************************/
		/* TODO: Update routing: remove rules to route to host               */
		this.remove_rules(host);
		this.knownHosts.remove(device);
		this.compute_rules();
		/*********************************************************************/

	}

	/**
     * Event handler called when a host moves within the network.
     * @param device information about the host
     */
	@Override
	public void deviceMoved(IDevice device) 
	{
		Host host = this.knownHosts.get(device);
		if (null == host)
		{
			host = new Host(device, this.floodlightProv);
			this.knownHosts.put(device, host);
		}
		
		if (!host.isAttachedToSwitch())
		{
			this.deviceRemoved(device);
			return;
		}
		log.info(String.format("Host %s moved to s%d:%d", host.getName(),
				host.getSwitch().getId(), host.getPort()));
		
		/*********************************************************************/
		/* TODO: Update routing: change rules to route to host               */
		this.compute_rules();
		/*********************************************************************/

	}
	
    /**
     * Event handler called when a switch joins the network.
     * @param DPID for the switch
     */
	@Override		
	public void switchAdded(long switchId) 
	{
		IOFSwitch sw = this.floodlightProv.getSwitch(switchId);
		log.info(String.format("Switch s%d added", switchId));
		
		/*********************************************************************/
		/* TODO: Update routing: change routing rules for all hosts          */
		this.install_table_miss(sw);
		this.compute_rules();
		/*********************************************************************/
	}

	/**
	 * Event handler called when a switch leaves the network.
	 * @param DPID for the switch
	 */
	@Override
	public void switchRemoved(long switchId) 
	{
		IOFSwitch sw = this.floodlightProv.getSwitch(switchId);
		log.info(String.format("Switch s%d removed", switchId));
		
		/*********************************************************************/
		/* TODO: Update routing: change routing rules for all hosts          */
		this.compute_rules();
		/*********************************************************************/
	}

	/**
	 * Event handler called when multiple links go up or down.
	 * @param updateList information about the change in each link's state
	 */
	@Override
	public void linkDiscoveryUpdate(List<LDUpdate> updateList) 
	{
		for (LDUpdate update : updateList)
		{
			// If we only know the switch & port for one end of the link, then
			// the link must be from a switch to a host
			if (0 == update.getDst())
			{
				log.info(String.format("Link s%s:%d -> host updated", 
					update.getSrc(), update.getSrcPort()));
			}
			// Otherwise, the link is between two switches
			else
			{
				log.info(String.format("Link s%s:%d -> %s:%d updated", 
					update.getSrc(), update.getSrcPort(),
					update.getDst(), update.getDstPort()));
			}
		}
		
		/*********************************************************************/
		/* TODO: Update routing: change routing rules for all hosts          */
		this.compute_rules();
		/*********************************************************************/
	}

	/**
	 * Event handler called when link goes up or down.
	 * @param update information about the change in link state
	 */
	@Override
	public void linkDiscoveryUpdate(LDUpdate update) 
	{ this.linkDiscoveryUpdate(Arrays.asList(update)); }
	
	/**
     * Event handler called when the IP address of a host changes.
     * @param device information about the host
     */
	@Override
	public void deviceIPV4AddrChanged(IDevice device) 
	{ this.deviceAdded(device); }

	/**
     * Event handler called when the VLAN of a host changes.
     * @param device information about the host
     */
	@Override
	public void deviceVlanChanged(IDevice device) 
	{ /* Nothing we need to do, since we're not using VLANs */ }
	
	/**
	 * Event handler called when the controller becomes the master for a switch.
	 * @param DPID for the switch
	 */
	@Override
	public void switchActivated(long switchId) 
	{ /* Nothing we need to do, since we're not switching controller roles */ }

	/**
	 * Event handler called when some attribute of a switch changes.
	 * @param DPID for the switch
	 */
	@Override
	public void switchChanged(long switchId) 
	{ /* Nothing we need to do */ }
	
	/**
	 * Event handler called when a port on a switch goes up or down, or is
	 * added or removed.
	 * @param DPID for the switch
	 * @param port the port on the switch whose status changed
	 * @param type the type of status change (up, down, add, remove)
	 */
	@Override
	public void switchPortChanged(long switchId, ImmutablePort port,
			PortChangeType type) 
	{ /* Nothing we need to do, since we'll get a linkDiscoveryUpdate event */ }

	/**
	 * Gets a name for this module.
	 * @return name for this module
	 */
	@Override
	public String getName() 
	{ return this.MODULE_NAME; }

	/**
	 * Check if events must be passed to another module before this module is
	 * notified of the event.
	 */
	@Override
	public boolean isCallbackOrderingPrereq(String type, String name) 
	{ return false; }

	/**
	 * Check if events must be passed to another module after this module has
	 * been notified of the event.
	 */
	@Override
	public boolean isCallbackOrderingPostreq(String type, String name) 
	{ return false; }
	
    /**
     * Tell the module system which services we provide.
     */
	@Override
	public Collection<Class<? extends IFloodlightService>> getModuleServices() 
	{
		Collection<Class<? extends IFloodlightService>> services =
					new ArrayList<Class<? extends IFloodlightService>>();
		services.add(InterfaceShortestPathSwitching.class);
		return services; 
	}

	/**
     * Tell the module system which services we implement.
     */
	@Override
	public Map<Class<? extends IFloodlightService>, IFloodlightService> 
			getServiceImpls() 
	{ 
        Map<Class<? extends IFloodlightService>, IFloodlightService> services =
        			new HashMap<Class<? extends IFloodlightService>, 
        					IFloodlightService>();
        // We are the class that implements the service
        services.put(InterfaceShortestPathSwitching.class, this);
        return services;
	}

	/**
     * Tell the module system which modules we depend on.
     */
	@Override
	public Collection<Class<? extends IFloodlightService>> 
			getModuleDependencies() 
	{
		Collection<Class<? extends IFloodlightService >> modules =
	            new ArrayList<Class<? extends IFloodlightService>>();
		modules.add(IFloodlightProviderService.class);
		modules.add(ILinkDiscoveryService.class);
		modules.add(IDeviceService.class);
        return modules;
	}
}
