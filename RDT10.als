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

/** Start & End States **/
pred NetState.Init[] {
	all d: Data | d in this.senderBuffer
	no d:Data | d in this.receiverBuffer
	no this.packet
}
run Init for exactly 1 NetState, exactly 4 Data, 4 Packet

pred NetState.End[] {
	no d:Data | d in this.senderBuffer	
	all d: Data | d in this.receiverBuffer
	no this.packet
}
run End for exactly 1 NetState, exactly 4 Data, 4 Packet

/** Facts **/
fact DataInOnlyOneBuffer{
	all s: NetState | no d: Data | d in s.senderBuffer and d in s.receiverBuffer
}

/** Functions **/
fun NetState.make_pkt[d: Data]: Packet {
	{p:Packet | one Global.dToP[d] implies d->p in Global.dToP}
}

fun NetState.extract[p: Packet]: Data {
	{d: Data | one Global.dToP.p implies d->p in Global.dToP}
}

/** Preds **/
pred NetState.rdt_send[d: Data, s: NetState] {
	d in this.senderBuffer
	s.senderBuffer = this.senderBuffer - d
	s.receiverBuffer = this.receiverBuffer
	one p: Packet | p = this.make_pkt[d] and s.udt_send[p]
}

pred NetState.udt_send[p: Packet] {
	this.packet = p
}

pred NetState.rdt_receive[p: Packet, s: NetState] {
	no this.packet
	one d: Data | d = this.extract[p] and this.deliver_data[d] and this.receiverBuffer = s.receiverBuffer + d
	s.senderBuffer = this.senderBuffer
}

pred NetState.deliver_data[d: Data] {
	d in this.receiverBuffer
}

pred Skip[s,s': NetState] {
	s.receiverBuffer = s'.receiverBuffer
	s.senderBuffer = s'.senderBuffer
	s.packet = s'.packet
}

pred Trace[] {
	first.Init
	last.End
	all s: NetState - last | let s' = s.next |
		not Skip[s,s'] and 
		(one d: Data | s.rdt_send[d, s']) or s'.rdt_receive[s.packet, s]
}
run Trace for 7 NetState, exactly 3 Data, exactly 3 Packet

assert AlwaysPossibleToTransmitAllData {
	Trace => 
		all d: Data | d in first.senderBuffer and d in last.receiverBuffer and
		all s: NetState | Data = s.senderBuffer + s.receiverBuffer + s.extract[s.packet] and
		some s:NetState | Data = s.receiverBuffer and not Data in s.senderBuffer
}
check AlwaysPossibleToTransmitAllData for 7 but 15 NetState expect 0
