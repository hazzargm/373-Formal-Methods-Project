module RDT10
/*
	CSSE 373 - Sprint 1: Checking RDT 1.0
	Team: Moore Hazzard
	Members: Gordon Hazzard & Jordan Moore
*/
open util/ordering[NetState]

sig Data {}
sig Packet{}

one sig Global {
	dToP: Data one -> one Packet
}

abstract sig NetState {
	senderBuffer: set Data,
	receiverBuffer: set Data,
	packet: lone Packet
}

pred NetState.Init[] {
	all d: Data | d in this.senderBuffer
	no d:Data | d in this.receiverBuffer
}

run Init for exactly 1 NetState, exactly 10 Data, 10 Packet

fact DataInOnlyOneBuffer{
	all s: NetState | no d: Data | d in s.senderBuffer and d in s.receiverBuffer
}

fun NetState.make_pkt[d: Data]: Packet {
	{p:Packet | one Global.dToP[d] implies d->p in Global.dToP}
}

pred NetState.rdt_send[d: Data, s: NetState] {
	this.packet = this.make_pkt[d]
	not d in this.senderBuffer
	this.udt_send[this.packet, s]
}

pred NetState.udt_send[p: Packet, s: NetState] {
	this.packet = p
	s.packet = p
}

pred NetState.rdt_receive[p: Packet, s: NetState] {
	this.packet = p
	one d: Data | this.deliver_data[d] and (d = this.extract[p])
}

fun NetState.extract[p: Packet]: Data {
	{d: Data | one Global.dToP.p implies d->p in Global.dToP}
}

pred NetState.deliver_data[d: Data] {
	d in this.receiverBuffer
}

pred NetState.End[] {
	all d: Data | d in this.receiverBuffer
	no d:Data | d in this.senderBuffer
}
run End for exactly 1 NetState, exactly 10 Data, 10 Packet

pred Trace[] {
	first.Init
	last.End
	all s: NetState - last | let s' = s.next |
	(one d: s.senderBuffer | s.rdt_send[d, s']) and (s'.rdt_receive[s.packet, s])
}

run Trace for 3  NetState, exactly 1 Data, exactly 1 Packet
