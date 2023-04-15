/*
Copyright 2020 Steven Siloti

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

use clap::{App, Arg};
use directories::ProjectDirs;
use ini::Ini;
use int_enum::IntEnum;
use libc::{c_char, if_indextoname, IF_NAMESIZE};
use mio::net::UdpSocket;
use mio::Poll;
use netlink_packet_core::constants::{NLM_F_DUMP, NLM_F_REQUEST};
use netlink_packet_route::constants::{AF_INET, AF_INET6, RTN_UNICAST};
use netlink_packet_route::nlas;
use netlink_packet_route::{
	AddressHeader, AddressMessage, NetlinkHeader, NetlinkMessage, NetlinkPayload, RouteFlags,
	RouteHeader, RouteMessage, RtnlMessage,
};
use netlink_sys;
use rand::prelude::*;
use std::cmp;
use std::collections::HashMap;
use std::convert::{From, TryInto};
use std::fs::read_dir;
use std::io::ErrorKind;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV6};
use std::path::Path;
use std::time::{Duration, Instant};

// copy-pasted from rtnetlink (why are they not in packet-route?)
const RTMGRP_IPV4_IFADDR: u32 = 16;
const RTMGRP_IPV6_IFADDR: u32 = 256;

const RTNL_TOKEN: mio::Token = mio::Token(0);

fn read_slice<'a>(s: &mut &'a [u8], count: usize) -> Option<&'a [u8]> {
	if s.len() < count {
		return None;
	}
	let (bytes, rest) = s.split_at(count);
	*s = rest;
	Some(bytes)
}

fn read_u8(s: &mut &[u8]) -> Option<u8> {
	let (octet, rest) = s.split_first()?;
	*s = rest;
	Some(*octet)
}

fn read_u16(s: &mut &[u8]) -> Option<u16> {
	Some(u16::from_be_bytes(read_slice(s, 2)?.try_into().ok()?))
}

fn read_u32(s: &mut &[u8]) -> Option<u32> {
	Some(u32::from_be_bytes(read_slice(s, 4)?.try_into().ok()?))
}

// constants and functions defined by RFC 6887
pub mod rfc_6887 {
	use rand::prelude::*;
	use std::cmp;
	use std::time::{Duration, Instant};

	pub enum Version {
		NatPmp = 1,
		Pcp = 2,
	}

	// Section 19.2
	pub enum Opcode {
		Announce = 0,
		Map = 1,
		Peer = 2,
	}

	// Section 7.4
	#[derive(Debug, Copy, Clone, int_enum::IntEnum)]
	#[repr(u8)]
	pub enum ResultCode {
		Success = 0,
		UnsuppVersion = 1,
		NotAuthorized = 2,
		MalformedRequest = 3,
		UnsuppOpcode = 4,
		UnsuppOption = 5,
		MalformedOption = 6,
		NetworkFailure = 7,
		NoResources = 8,
		UnsuppProtocol = 9,
		UserExQuota = 10,
		CannotProvideExternal = 11,
		AddressMismatch = 12,
		ExcessiveRemotePeers = 13,
	}

	// Section 19.1
	pub const CLIENT_PORT: u16 = 5350;
	pub const SERVER_PORT: u16 = 5351;

	// Section 8.1.1
	const IRT: Duration = Duration::from_secs(3); // Initial retransmission time
	const _MRC: u8 = 0; // Maximum retransmission count, 0 = no maximum
	const MRT: Duration = Duration::from_secs(1024); // Maximum retransmission time
	const _MRD: Duration = Duration::from_secs(0); // Maximum retransmission duration, 0 = no maximum

	// RAND is defined as a uniform random number between -0.1 and 0.1
	// to avoid unnecessary floating point, fn Rand returns an integer between -1000 and 1000
	// apply RAND_MULTIPLIER as apprioriate to compensate
	const RAND_MULTIPLIER: u32 = 10000;
	fn rand() -> u32 {
		let distr = rand::distributions::Uniform::new_inclusive(-1000, 1000);
		(RAND_MULTIPLIER as i32 + thread_rng().sample(distr)) as u32
	}

	pub fn initial_rt() -> Duration {
		(rand() * IRT) / RAND_MULTIPLIER
	}
	pub fn subsequent_rt(rt_prev: Duration) -> Duration {
		(rand() * cmp::min(2 * rt_prev, MRT)) / RAND_MULTIPLIER
	}

	// Section 11.2.1
	pub const MIN_RENEWAL_TIME: Duration = Duration::from_secs(4);
	// Section 15
	pub const MAX_LIFETIME: Duration = Duration::from_secs(60 * 60 * 24); // 24 hours

	pub fn initial_renewal_time(lifetime: Duration) -> Duration {
		let lifetime_secs = lifetime.as_secs();
		let distr =
			rand::distributions::Uniform::new_inclusive(lifetime_secs / 2, lifetime_secs * 5 / 8);
		cmp::max(
			MIN_RENEWAL_TIME,
			Duration::from_secs(thread_rng().sample(distr)),
		)
	}
	// request_count includes the request being prepared
	pub fn subsequent_renewal_time(lifetime: Duration, request_count: u32) -> Duration {
		let lifetime_secs = lifetime.as_secs();
		let min_denom = 2_u64.pow(request_count);
		let min_secs = lifetime_secs * (min_denom - 1) / min_denom;
		let range_secs = lifetime_secs / 2_u64.pow(request_count + 2);
		let distr = rand::distributions::Uniform::new_inclusive(min_secs, min_secs + range_secs);
		cmp::max(
			MIN_RENEWAL_TIME,
			Duration::from_secs(thread_rng().sample(distr)),
		)
	}

	// Section 8.5
	pub fn validate_epoch(
		curr_client_time: Instant,
		curr_server_time: u32,
		prev_client_time: Instant,
		prev_server_time: u32,
	) -> bool {
		let server_delta = curr_server_time.saturating_sub(prev_server_time) as u64;
		let client_delta = (curr_client_time - prev_client_time).as_secs();
		!((curr_server_time + 1 < prev_server_time)
			|| (client_delta + 2 < (server_delta - server_delta / 16))
			|| (server_delta + 2 < (client_delta - client_delta / 16)))
	}
}

struct IpAssignedProtocol {
	name: &'static str,
	number: u8,
}

// selected Internet Protocol protocol numbers
// https://www.iana.org/assignments/protocol-numbers/protocol-numbers.xhtml
#[rustfmt::skip]
static IP_ASSIGNED_PROTOCOLS: [IpAssignedProtocol; 18] = [
	IpAssignedProtocol{name: "HOPOPT", number: 0},
	IpAssignedProtocol{name: "ICMP", number: 1},
	IpAssignedProtocol{name: "IGMP", number: 2},
	IpAssignedProtocol{name: "GGP", number: 3},
	IpAssignedProtocol{name: "IPv4", number: 4},
	IpAssignedProtocol{name: "ST", number: 5},
	IpAssignedProtocol{name: "TCP", number: 6},
	IpAssignedProtocol{name: "CBT", number: 7},
	IpAssignedProtocol{name: "EGP", number: 8},
	IpAssignedProtocol{name: "IGP", number: 9},
	IpAssignedProtocol{name: "BBN-RCC-MON", number: 10},
	IpAssignedProtocol{name: "NVP-II", number: 11},
	IpAssignedProtocol{name: "PUP", number: 12},
	IpAssignedProtocol{name: "ARGUS", number: 13},
	IpAssignedProtocol{name: "EMCON", number: 14},
	IpAssignedProtocol{name: "XNET", number: 15},
	IpAssignedProtocol{name: "CHAOS", number: 16},
	IpAssignedProtocol{name: "UDP", number: 17},
];

// default to 1 hour
const DEFAULT_LIFETIME: u32 = 3600;

// user provided specifications for a mapping
struct MappingSpec {
	// name of this mapping
	name: String,
	// name of the interface this mapping should be made on
	// if not provided this mapping is created on all interfaces
	interface: Option<String>,
	internal_port: u16,
	protocol: u8,
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct MappingKey {
	internal_port: u16,
	protocol: u8,
}

struct MappingValue {
	// the last time a request was sent for this mapping
	last_req: Instant,
	// Retransmission timeout, see RFC 6887 Section 8.1.1
	rt: Duration,
	rt_count: u8,
	// When this mapping expires based on the returned lifetime
	// None if no server response has been received for this mapping
	expires: Option<Instant>,
	external_address: Ipv6Addr,
	external_port: u16,
	// set to true if this mapping is in the process of being deleted
	delete: bool,
}

impl MappingValue {
	fn new(suggested_port: u16) -> Self {
		MappingValue {
			last_req: Instant::now(),
			rt: rfc_6887::initial_rt(),
			rt_count: 0,
			expires: None,
			external_address: Ipv6Addr::UNSPECIFIED,
			external_port: suggested_port,
			delete: false,
		}
	}
}

type Mapping<'a> = (MappingKey, &'a MappingValue);
type MutMapping<'a> = (MappingKey, &'a mut MappingValue);

struct LocalAddress {
	interface: String,
	sock: UdpSocket,
	token: mio::Token,
	// the most recent epoch time received from this server
	epoch: u32,
	// local time when the last epoch time was received
	local_epoch: Instant,
	nonce: [u8; 12],
	mappings: HashMap<MappingKey, MappingValue>,
}

struct Client {
	mappings: Vec<MappingSpec>,
	addrs: Vec<LocalAddress>,
}

fn addr_from_vec(v: &Vec<u8>) -> Option<IpAddr> {
	if v.len() == 4 {
		let mut octets = [0u8; 4];
		octets.copy_from_slice(v);
		Some(IpAddr::V4(Ipv4Addr::from(octets)))
	} else if v.len() == 16 {
		let mut octets = [0u8; 16];
		octets.copy_from_slice(v);
		Some(IpAddr::V6(Ipv6Addr::from(octets)))
	} else {
		None
	}
}

fn interface_default_route(interface: u32, address_family: u16) -> Option<IpAddr> {
	let rts = netlink_sys::Socket::new(netlink_sys::Protocol::Route).ok()?;

	let header = RouteHeader {
		address_family: address_family as u8,
		destination_prefix_length: 0,
		source_prefix_length: 0,
		tos: 0,

		table: 0,
		protocol: 0,
		scope: 0,
		kind: RTN_UNICAST,
		flags: RouteFlags::default(),
	};

	let msg = RouteMessage {
		header,
		nlas: vec![],
	};

	let mut packet = NetlinkMessage {
		header: NetlinkHeader::default(),
		payload: NetlinkPayload::from(RtnlMessage::GetRoute(msg)),
	};
	packet.header.flags = NLM_F_DUMP | NLM_F_REQUEST;
	packet.header.sequence_number = 1;
	packet.finalize();

	let mut buf = vec![0; packet.header.length as usize];
	packet.serialize(&mut buf[..]);

	rts.send(&buf[..], 0).ok()?;

	let mut receive_buffer = vec![0; 4096];
	rts.recv(&mut receive_buffer[..], 0).ok()?;

	let mut offset = 0;
	loop {
		if offset >= receive_buffer.len() {
			break;
		}

		let bytes = &receive_buffer[offset..];
		let packet = NetlinkMessage::deserialize(bytes).ok()?;

		if packet.header.length == 0 {
			break;
		}

		offset += packet.header.length as usize;

		match packet.payload {
			NetlinkPayload::InnerMessage(rtnl_msg) => match rtnl_msg {
				RtnlMessage::NewRoute(rt) => {
					if rt.header.destination_prefix_length != 0 {
						continue;
					}

					let mut gw: Option<IpAddr> = None;
					let mut oif: Option<u32> = None;

					for nla in rt.nlas {
						match nla {
							nlas::route::Nla::Gateway(g) => {
								gw = addr_from_vec(&g);
							}
							nlas::route::Nla::Oif(o) => {
								oif = Some(o);
							}
							_ => (),
						};
					}

					match oif {
						Some(o) => {
							if o != interface {
								continue;
							}
						}
						None => (),
					}

					if gw.is_some() {
						return gw;
					}
				}
				_ => (),
			},
			_ => (),
		};
	}
	return None;
}

fn extend_from_pcp_address(addr: &IpAddr, out: &mut Vec<u8>) {
	let addr_v6 = match addr {
		IpAddr::V4(a) => a.to_ipv6_mapped(),
		IpAddr::V6(a) => *a,
	};
	out.extend_from_slice(&addr_v6.octets());
}

fn build_pcp_map_request(
	ttl: u32,
	local_addr: &SocketAddr,
	nonce: &[u8; 12],
	mapping: &Mapping,
) -> Vec<u8> {
	let mut b = Vec::new();
	b.push(rfc_6887::Version::Pcp as u8);
	b.push(rfc_6887::Opcode::Map as u8);
	b.push(0); // reserved
	b.push(0); // reserved
	b.extend_from_slice(&ttl.to_be_bytes());
	extend_from_pcp_address(&local_addr.ip(), &mut b);
	b.extend_from_slice(nonce);
	b.push(mapping.0.protocol);
	b.push(0); // reserved
	b.push(0); // reserved
	b.push(0); // reserved
	b.extend_from_slice(&mapping.0.internal_port.to_be_bytes());
	b.extend_from_slice(&mapping.1.external_port.to_be_bytes());
	if !mapping.1.external_address.is_unspecified() {
		extend_from_pcp_address(&IpAddr::V6(mapping.1.external_address), &mut b);
	}
	// TODO: use IpAddr.is_global() once it is stable
	else if match local_addr.ip() {
		IpAddr::V4(a) => a.is_private(),
		_ => false,
	} {
		extend_from_pcp_address(
			if local_addr.ip().is_ipv4() {
				&IpAddr::V4(Ipv4Addr::UNSPECIFIED)
			} else {
				&IpAddr::V6(Ipv6Addr::UNSPECIFIED)
			},
			&mut b,
		);
	} else {
		extend_from_pcp_address(&local_addr.ip(), &mut b);
	}
	b
}

fn retransmit_mapping(
	map: &mut MutMapping,
	sock: &mut UdpSocket,
	nonce: &[u8; 12],
	now: Instant,
) -> Option<()> {
	let req = build_pcp_map_request(
		DEFAULT_LIFETIME,
		&sock.local_addr().ok()?,
		nonce,
		&(map.0, map.1),
	);
	sock.send(&req).ok()?;
	map.1.rt_count = map.1.rt_count.saturating_add(1);
	map.1.rt = match map.1.expires {
		Some(exp) => {
			let lifetime_remaining = if exp > now {
				exp - now
			} else {
				Duration::from_secs(0)
			};
			rfc_6887::subsequent_renewal_time(lifetime_remaining, map.1.rt_count.into())
		}
		None => rfc_6887::subsequent_rt(map.1.rt),
	};
	map.1.last_req = now;
	Some(())
}

fn poll_client(cli: &mut Client) -> Duration {
	let mut next_poll = Duration::new(u64::max_value(), 0);
	let now = Instant::now();
	for la in cli.addrs.iter_mut() {
		for m in la.mappings.iter_mut() {
			if m.1.last_req + m.1.rt <= now {
				retransmit_mapping(&mut (*m.0, m.1), &mut la.sock, &la.nonce, now);
			}

			next_poll = cmp::min(m.1.last_req + m.1.rt - now, next_poll);
		}
	}
	next_poll
}

fn update_epoch(addr: &mut LocalAddress, epoch: u32) {
	let now = Instant::now();
	let valid = rfc_6887::validate_epoch(now, epoch, addr.local_epoch, addr.epoch);

	if !valid || addr.epoch < epoch {
		addr.epoch = epoch;
		addr.local_epoch = now;
	}

	if !valid {
		// the router seems to have been reset
		// schedule all mappings to retransmit soon
		for m in addr.mappings.iter_mut() {
			m.1.rt = Duration::new(0, 0);
		}
	}
}

fn incoming_msg(addr: &mut LocalAddress, mut msg: &[u8]) -> Option<()> {
	// make a mutable borrow to avoid repeating `&mut` at every read call
	let m = &mut msg;
	let version = read_u8(m)?;
	let opcode = read_u8(m)?;
	let response = (opcode & 0x80) == 0x80;
	let opcode = opcode & 0x7F;
	let _ = read_u8(m)?; // reserved
	let result_code = read_u8(m)?;
	let lifetime = cmp::min(
		Duration::from_secs(read_u32(m)? as u64),
		rfc_6887::MAX_LIFETIME,
	);
	let epoch = read_u32(m)?;
	let _ = read_slice(m, 12)?; // reserved

	if version != rfc_6887::Version::Pcp as u8 {
		// Only support PCP for now
		return None;
	}

	if result_code == rfc_6887::ResultCode::UnsuppVersion as u8 {
		// Only support PCP for now
		return None;
	}

	if opcode == rfc_6887::Opcode::Map as u8 {
		if !response {
			return None;
		}

		let nonce = read_slice(m, 12)?;
		let protocol = read_u8(m)?;
		let _ = read_slice(m, 3)?; // reserved
		let internal_port = read_u16(m)?;
		let external_port = read_u16(m)?;
		let ext_addr: [u8; 16] = read_slice(m, 16)?.try_into().ok()?;
		let external_address = Ipv6Addr::from(ext_addr);

		if nonce != addr.nonce {
			return None;
		}

		update_epoch(addr, epoch);

		let key = MappingKey {
			protocol,
			internal_port,
		};
		let mapping = addr.mappings.get_mut(&key)?;

		let now = Instant::now();

		mapping.last_req = now;
		mapping.expires = Some(now + lifetime);
		mapping.rt_count = 0;
		mapping.rt = rfc_6887::initial_renewal_time(lifetime);

		// TODO error handling

		if result_code != rfc_6887::ResultCode::Success as u8 {
			println!(
				"Error from PCP server: {}",
				rfc_6887::ResultCode::from_int(result_code)
					.map(|c| format!("{:?} ({})", c, result_code))
					.unwrap_or_else(|_| format!("{} (unknown error)", result_code)),
			);
			// miniupnpd returns a lifetime of zero for some errors
			// treat these as long lifetime errors
			if lifetime == Duration::from_secs(0) {
				println!("Warning: Server sent error response with zero lifetime");
				let lifetime = Duration::from_secs(30 * 60);
				mapping.expires = Some(now + lifetime);
				mapping.rt = rfc_6887::initial_renewal_time(lifetime);
			}
			return None;
		}

		if mapping.delete {
			if lifetime == Duration::from_secs(0) {
				addr.mappings.remove(&key);
				return Some(());
			} else {
				// apparently the server didn't remove the mapping, try again later
				mapping.rt_count = mapping.rt_count.saturating_add(1);
				mapping.rt = rfc_6887::subsequent_rt(mapping.rt);
				return None;
			}
		} else {
			println!(
				"Mapping was established, external address is [{}]:{}",
				external_address, external_port
			);
		}

		mapping.external_address = external_address;
		mapping.external_port = external_port;
	}

	Some(())
}

fn parse_conf_file<P: AsRef<Path>>(file_name: P) -> Vec<MappingSpec> {
	match Ini::load_from_file(file_name) {
		Ok(i) => i
			.iter()
			.filter_map(|(sec, prop)| {
				if sec.is_none() {
					return None;
				}

				let mut spec = MappingSpec {
					name: sec.as_ref().unwrap().clone(),
					interface: None,
					internal_port: 0,
					protocol: 0,
				};
				for (k, v) in prop.iter() {
					if k == "Interface" {
						spec.interface = Some(v.to_string());
					} else if k == "Port" {
						spec.internal_port = match v.parse::<u16>() {
							Ok(p) => p,
							Err(_) => 0,
						}
					} else if k == "Protocol" {
						for p in &IP_ASSIGNED_PROTOCOLS {
							if p.name == v {
								spec.protocol = p.number;
								break;
							}
						}
					}
				}

				match spec.internal_port {
					0 => None,
					_ => Some(spec),
				}
			})
			.collect(),
		Err(_) => Vec::new(),
	}
}

fn parse_conf_files<P: AsRef<Path>>(path: P) -> Vec<MappingSpec> {
	if path.as_ref().is_file() {
		parse_conf_file(path)
	} else {
		match read_dir(path) {
			Ok(i) => i
				.filter_map(|x| match x {
					Ok(e) => {
						if e.file_name().to_string_lossy().ends_with(".conf") {
							Some(parse_conf_file(e.path()))
						} else {
							None
						}
					}
					Err(_) => None,
				})
				.flatten()
				.collect(),
			Err(_) => Vec::new(),
		}
	}
}

fn interface_name_from_index(index: u32) -> Option<String> {
	let mut name_vec = Vec::<u8>::with_capacity(IF_NAMESIZE);
	name_vec.resize(IF_NAMESIZE, 0);
	unsafe {
		if_indextoname(index, name_vec.as_mut_ptr() as *mut c_char);
	}
	name_vec.truncate(name_vec.iter().position(|&x| x == 0).unwrap_or(IF_NAMESIZE));
	match String::from_utf8(name_vec) {
		Ok(s) => Some(s),
		Err(e) => {
			println!("Invalid UTF-8 in name of interface number {}: {}", index, e);
			None
		}
	}
}

// compare only the address of a SocketAddr, taking the scope_id into account for IPv6
fn cmp_socket_addr(l: SocketAddr, r: SocketAddr) -> bool {
	if l.ip() != r.ip() {
		return false;
	}

	match l {
		SocketAddr::V6(l6) => match r {
			SocketAddr::V6(r6) => l6.scope_id() == r6.scope_id(),
			SocketAddr::V4(_) => panic!(),
		},
		SocketAddr::V4(_) => false,
	}
}

// TODO replace with Ipv6Addr's is_unicast_link_local once that is stablized
fn is_unicast_link_local(addr: &Ipv6Addr) -> bool {
    // Copied from Ipv6Addr::is_unicast_link_local, whose stabilization has not seen any activity
    // in years
    (addr.segments()[0] & 0xffc0) == 0xfe80
}

fn update_local_addr(addrs: &mut Vec<LocalAddress>, rtnl_msg: &RtnlMessage) -> Option<()> {
	match rtnl_msg {
		RtnlMessage::NewAddress(na_msg) => {
			let nla_addr = na_msg.nlas.iter().find(|&x| match x {
				nlas::address::Nla::Address(_) => true,
				_ => false,
			})?;

			let addr = match nla_addr {
				nlas::address::Nla::Address(a) => {
					let ip_addr = addr_from_vec(a)?;
					match ip_addr {
						IpAddr::V6(a6) => {
							if is_unicast_link_local(&a6) {
								SocketAddr::V6(SocketAddrV6::new(a6, 0, 0, na_msg.header.index))
							} else {
								SocketAddr::new(ip_addr, 0)
							}
						}
						IpAddr::V4(_) => SocketAddr::new(ip_addr, 0),
					}
				}
				_ => return None,
			};

			if addrs
				.iter()
				.find(|x| match x.sock.local_addr() {
					Ok(a) => cmp_socket_addr(a, addr),
					Err(_) => false,
				})
				.is_some()
			{
				return None;
			}

			let sock = match UdpSocket::bind(&addr) {
				Ok(s) => s,
				Err(e) => {
					println!("Error binding socket to {}: {}", &addr, e);
					return None;
				}
			};

			let address_family = match addr {
				SocketAddr::V4(_) => AF_INET,
				SocketAddr::V6(_) => AF_INET6,
			};

			// with IPv6 the default gateway should be a link-local address so the scope ID
			// needs to be specified
			let gateway = match interface_default_route(na_msg.header.index, address_family)? {
				IpAddr::V6(gw) => SocketAddr::V6(SocketAddrV6::new(
					gw,
					rfc_6887::SERVER_PORT,
					0,
					na_msg.header.index,
				)),
				IpAddr::V4(gw) => SocketAddr::new(IpAddr::V4(gw), rfc_6887::SERVER_PORT),
			};

			match sock.connect(gateway) {
				Ok(_) => {}
				Err(e) => {
					println!("Error connecting to default gateway {}: {}", gateway, e);
					return None;
				}
			};

			let bound_port = sock.local_addr().ok()?.port();

			let interface = match interface_name_from_index(na_msg.header.index) {
				Some(s) => s,
				None => "".to_string(),
			};

			let mut nonce: [u8; 12] = [0; 12];
			for x in &mut nonce {
				*x = random();
			}

			println!("Detected new local address {}", &addr);

			addrs.push(LocalAddress {
				interface,
				sock,
				token: mio::Token(bound_port as usize),
				epoch: 0,
				local_epoch: Instant::now(),
				nonce: nonce,
				mappings: HashMap::new(),
			});

			Some(())
		}
		RtnlMessage::DelAddress(da) => {
			let interface = interface_name_from_index(da.header.index)?;

			let nla_addr = da.nlas.iter().find(|&x| match x {
				nlas::address::Nla::Address(_) => true,
				_ => false,
			})?;

			let addr = match nla_addr {
				nlas::address::Nla::Address(a) => addr_from_vec(a)?,
				_ => return None,
			};

			let scope_id = match addr {
				IpAddr::V6(_) => {
					// TODO enable once is_unicast_link_local is stablized
					//if a6.is_unicast_link_local() {
					if false {
						da.header.index
					} else {
						0
					}
				}
				_ => 0,
			};

			let la_idx = addrs.iter().position(|x| {
				if x.interface != interface {
					return false;
				}
				match x.sock.local_addr() {
					Ok(local_addr) => match local_addr {
						SocketAddr::V4(_) => local_addr.ip() == addr,
						SocketAddr::V6(sa6) => {
							local_addr.ip() == addr && sa6.scope_id() == scope_id
						}
					},
					Err(_) => false,
				}
			})?;

			println!("Removed local address {}", &addr);

			addrs.swap_remove(la_idx);
			None
		}
		_ => None,
	}
}

// pass mappings and addr separately instead of passing &Client so that the mappings can be immutable
fn update_local_addrs(
	poll: &Poll,
	mappings: &Vec<MappingSpec>,
	addrs: &mut Vec<LocalAddress>,
	rtnl_packet: &[u8],
) {
	let mut offset = 0;
	loop {
		let bytes = &rtnl_packet[offset..];
		let dser = NetlinkMessage::deserialize(bytes);
		if dser.is_err() {
			break;
		}
		let packet: NetlinkMessage<RtnlMessage> = dser.unwrap();
		match packet.payload {
			NetlinkPayload::InnerMessage(rtnl_msg) => {
				if update_local_addr(addrs, &rtnl_msg).is_some() {
					let addr = addrs.last_mut().unwrap();
					for mapping in mappings {
						let matched = match &mapping.interface {
							// TODO allow mapping interface to be a regex
							Some(iface) => iface == &addr.interface,
							None => true,
						};

						if !matched {
							continue;
						}

						let key = MappingKey {
							internal_port: mapping.internal_port,
							protocol: mapping.protocol,
						};

						let local_addr = match addr.sock.local_addr() {
							Ok(a) => SocketAddr::new(a.ip(), mapping.internal_port),
							Err(_) => continue,
						};

						let mut inserted = false;
						let mapped_mapping = addr.mappings.entry(key).or_insert_with(|| {
							inserted = true;
							MappingValue::new(mapping.internal_port)
						});

						if inserted {
							poll.register(
								&addr.sock,
								addr.token,
								mio::Ready::readable(),
								mio::PollOpt::edge(),
							)
							.expect("Failed to register PCP socket");

							let req = build_pcp_map_request(
								DEFAULT_LIFETIME,
								&local_addr,
								&addr.nonce,
								&(key, mapped_mapping),
							);

							match addr.sock.send(&req) {
								Err(e) => println!("Error writing to PCP socket: {}", e),
								_ => (),
							};
						}
					}
				}
			}
			NetlinkPayload::Error(e) => println!("Netlink error: {}", e.code),
			_ => (),
		};
		offset += packet.header.length as usize;
		if offset >= rtnl_packet.len() || packet.header.length == 0 {
			break;
		}
	}
}

fn main() {
	let dirs = ProjectDirs::from("us", "silotis", "portcontrolcd");

	let config_dir_default = match dirs {
		Some(ref d) => d.config_dir(),
		None => Path::new("/etc/portcontrolcd"),
	};

	let matches = App::new("portcontrolcd")
		.version("0.1.0")
		.author("Steven Siloti <ssiloti@gmail.com>")
		.about("port mapping client")
		.arg(
			Arg::with_name("config")
				.short("c")
				.long("config")
				.value_name("PATH")
				.help("Sets a custom config file or directory")
				.takes_value(true),
		)
		.get_matches();

	let config_path = match matches.value_of("config") {
		Some(p) => Path::new(p),
		None => config_dir_default,
	};

	let mut client = Client {
		mappings: parse_conf_files(config_path),
		addrs: vec![],
	};

	for m in client.mappings.iter() {
		println!("Loaded mapping {}", m.name);
	}

	let poll = Poll::new().expect("Failed to create event poll");

	let mut rtnl_monitor_sock = netlink_sys::Socket::new(netlink_sys::Protocol::Route)
		.expect("Failed to create netlink socket");
	let rtnl_monitor_addr =
		netlink_sys::SocketAddr::new(0, RTMGRP_IPV4_IFADDR | RTMGRP_IPV6_IFADDR);
	rtnl_monitor_sock
		.bind(&rtnl_monitor_addr)
		.expect("Failed to bind netlink socket");

	{
		let dump_header = AddressHeader {
			family: 0,
			prefix_len: 0,
			flags: 0,
			scope: 0,
			index: 0,
		};

		let dump_msg = AddressMessage {
			header: dump_header,
			nlas: vec![],
		};

		let mut packet = NetlinkMessage {
			header: NetlinkHeader::default(),
			payload: NetlinkPayload::from(RtnlMessage::GetAddress(dump_msg)),
		};
		packet.header.flags = NLM_F_DUMP | NLM_F_REQUEST;
		packet.header.sequence_number = 1;
		packet.finalize();

		let mut buf = vec![0; packet.header.length as usize];
		packet.serialize(&mut buf[..]);

		rtnl_monitor_sock
			.send(&buf[..], 0)
			.expect("Failed to get interface list");
	}

	rtnl_monitor_sock
		.set_non_blocking(true)
		.expect("Failed to set netlink socket non-blocking");

	poll.register(
		&rtnl_monitor_sock,
		RTNL_TOKEN,
		mio::Ready::readable(),
		mio::PollOpt::edge(),
	)
	.expect("Failed to register netlink socket");

	let mut events = mio::Events::with_capacity(32);

	loop {
		let timeout = poll_client(&mut client);
		poll.poll(&mut events, Some(timeout))
			.expect("Failed to poll for events");

		for event in &events {
			match event.token() {
				RTNL_TOKEN => loop {
					let mut receive_buffer = vec![0; 4096];
					let r = rtnl_monitor_sock.recv(&mut receive_buffer[..], 0);
					match r {
						Ok(size) => {
							update_local_addrs(
								&poll,
								&client.mappings,
								&mut client.addrs,
								&receive_buffer[..size],
							);
						}
						Err(e) => {
							match e.kind() {
								ErrorKind::WouldBlock => (),
								_ => println!("Error reading from netlink socket {}", e),
							};
							break;
						}
					};
				},
				mio::Token(t) => {
					let local_addr = client.addrs.iter_mut().find(|x| x.token == event.token());

					match local_addr {
						Some(mut addr) => loop {
							let mut receive_buffer = vec![0; 4096];
							let r = addr.sock.recv(&mut receive_buffer[..]);

							match r {
								Ok(size) => {
									incoming_msg(&mut addr, &receive_buffer[..size]);
								}
								Err(e) => {
									match e.kind() {
										ErrorKind::WouldBlock => (),
										_ => println!("Error reading from PCP socket {}", e),
									};
									break;
								}
							};
						},
						None => {
							println!("Event with unknown token: {}", t);
						}
					}
				}
			};
		}
	}
}
