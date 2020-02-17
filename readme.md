portcontrolcd - A PCP client daemon
-----------------------------------

Portcontrolcd is a [Port Control Protocol](https://tools.ietf.org/html/rfc6887) client intended to open NAT port forwards and firewall pinholes for applications which accept incoming connections but do not themselves support PCP or other port opening protocols.

# Configuration
By default configuration paramaters are read from all files named *.conf in ${XDG_CONFIG_HOME}/portcontrolcd or ${HOME}/.config/portcontrolcd if XDG_CONFIG_HOME is not set. An alternative path can be specified with the --config command line parameter.

The configuration file uses an ini format where each section is a port mapping. The section name is an aribrary name for the mapping. Each section may contain the following keys:

Key | Value
--- | -----
Interface | The name of a network inferface on which to map the port. If this key is ommitted the port is mapped on all interfaces.
Port | The port number to map. Required.
Protocol | The name of the protocol to map. E.g. `TCP` or `UDP`. If this key is ommitted the port is mapped for all protocols. Mapping all protocols may not be supported by the PCP server.
