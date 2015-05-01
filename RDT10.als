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
	no d: Data | d in this.receiverBuffer
}

run Init for exactly 2 NetState, exactly 10 Data, exactly 10 Packet

//fun NetState.make_pkt[d: Data]: Packet {
	
//}

pred NetState.send[d: Data, s: NetState] {
	
}

pred Transition[s, s': NetState] {
		s.next = s'

}
run Transition for exactly 2 NetState, exactly 10 Data, exactly 10 Packet

pred Progress[s, s': NetState] {
	s.next = s'
	//Specific thing that signifies 'progress' here
	Transition[s, s']
}

pred NetState.End[] {

}

pred Trace[] {
	first.Init
	all s: NetState - last | let s' = s.next | (Transition[s,s'] and s.End[]) or (Progress[s, s'])
}

run Trace
