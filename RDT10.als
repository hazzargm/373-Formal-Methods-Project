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
	all d: Data | d in this.receiverBuffer
	no d:Data | d in this.senderBuffer
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
	not (d in this.senderBuffer or d in s.senderBuffer)
	one p: Packet | p = this.make_pkt[d] and this.udt_send[p]
}

pred NetState.udt_send[p: Packet] {
	this.packet = p
}

pred NetState.rdt_receive[p: Packet, s: NetState] {
	one d: Data | d = this.extract[p] and this.deliver_data[d]  
	s.packet = p
}

pred NetState.deliver_data[d: Data] {
	d in this.receiverBuffer
}


pred Trace[] {
	first.Init
//	last.End
	all s: NetState - last | let s' = s.next |
		(one d: Data | s.rdt_send[d, s']) //or s'.rdt_receive[s.packet, s]
}

run Trace for 4 NetState, exactly 4 Data, exactly 4 Packet
