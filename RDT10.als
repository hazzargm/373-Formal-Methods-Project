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


fun NetState.make_pkt[d: Data]: Packet {
	{p:Packet | one Global.dToP[d] implies d->p in Global.dToP }
}

pred NetState.rdt_send[d: Date, s: NetState] {
	this.next = s	
	this.packet = this.make_pkt[d]
	not d in this.senderBuffer
}

pred NetState.udt_oSend[d: Data, s: NetState] {
	this.rdt_send[d, s]
	s.rdt_receive[this.packet, this]
}

pred NetState.rdt_receive[p: Packet, s: NetState] {
	s.next = this
	this.packet = p
	Global.dToP.p in this.receiverBuffer
}

fun NetState.extract[p: Packet]: Data {

}

pred NetState.deliver_data[d: Data] {

}


pred NetState.End[] {
	all d: Data | d in this.receiverBuffer
	no d:Data | d in this.senderBuffer
}
run End for exactly 1 NetState, exactly 10 Data, 10 Packet

pred Trace[] {
	first.Init
	all s: NetState - last | let s' = s.next | 
		(Transition[s,s'] and s.End[]) or (Progress[s, s'])
}

run Trace
