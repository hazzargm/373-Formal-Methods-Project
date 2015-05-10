module RDT10
/*
	CSSE 373 - Sprint 1: Checking RDT 1.0
	Team: Moore Hazzard
	Members: Gordon Hazzard & Jordan Moore
*/
open util/ordering[NetState]
sig Data {}
sig Packet{
	c: Checksum
}
sig Checksum{}

one sig Global {
	pToD: Packet one -> one Data,
	dToC: Data one -> one Checksum
}

/*
Need error predicate that generates error
one trace where there is an error, and one trace where there isn't an error
*/

abstract sig NetState {
	senderBuffer: set Data,
	receiverBuffer: set Data,
	packet: lone Packet,
	reply: lone Reply
}

abstract sig Reply{}
one sig Ack, Nak extends Reply{}

/** Start & End States **/
pred NetState.Init[] {
	all d: Data | d in this.senderBuffer and not d in this.receiverBuffer
	no this.packet
	no this.reply
}
run Init for exactly 1 NetState,  exactly 2 Data,  exactly 2 Packet, exactly 2 Checksum

pred NetState.End[] {
	all d: Data | not d in this.senderBuffer and d in this.receiverBuffer  
//	all p:Packet | not p.IsCorrupt[]
	no this.packet
	no this.reply
}
run End for exactly 1 NetState, exactly 2 Data,  exactly 2 Packet, exactly 2 Checksum

/** Facts **/
fact DataInOnlyOneBuffer{
	all s: NetState | no d: Data | d in s.senderBuffer and d in s.receiverBuffer
}

/** Functions **/
fun make_pkt[d: Data, c: Checksum]: Packet {
	{p:Packet | one (Global.pToD).d implies ((p->d in Global.pToD) and (d->c in Global.dToC))}
}

fun extract[p: Packet]: Data {
	{d: Data | one p.(Global.pToD) implies p->d in Global.pToD}
}

/** Preds **/
pred NetState.rdt_send[d: Data, s: NetState] { // this = State A(sending), s = State B (receiving/verifying)
	// some condiitons added to run this instance
	one s
	
	// true in this state
	d in this.senderBuffer
	no this.reply
	
	// true in the next state (verify)
	s.senderBuffer = this.senderBuffer
	s.receiverBuffer = this.receiverBuffer
	one s.reply
	one s.packet
	
	// make a packet for this state
	one p: Packet | one c: Checksum | 
		p = make_pkt[d, c] and this.udt_send[p]
}
run { one s:NetState | one d: Data | 
		let s' = s.next | s.rdt_send[d, s'] } for exactly 2 NetState,  exactly 1 Data,  exactly 1 Packet, exactly 1 Checksum

pred NetState.udt_send[p: Packet] {
	this.packet = p
}

pred NetState.verify[recvP:Packet, recvState:NetState] {
	// some condiitons added to run this instance
	one recvState and one recvP
	Data in this.receiverBuffer + this.senderBuffer
	
	// true in this state
	one this.packet // maybe corrupt
	one this.reply
	
	// true in the next state (receive)
	no recvState.reply
	no recvState.packet
	
	// set the reply
	(this.packet.c = recvP.c and not this.packet.IsCorrupt) implies this.reply = Ack else this.reply = Nak
	// ... and operate based on it
	this.reply = Ack => (
		(one d : this.senderBuffer | 
			d = extract[this.packet] and
			recvState.receiverBuffer = this.receiverBuffer + d and 
			recvState.senderBuffer = this.senderBuffer - d
		) 
//		 	and	(some s'': NetState - (this + s + s') | some d: s'.senderBuffer | s'.rdt_send[d, s''])
	) else this.reply = Nak => (
		this.senderBuffer = recvState.senderBuffer and
		this.receiverBuffer = recvState.receiverBuffer
//		and (some s'': NetState - (this + s + s') | s = s'' and s'.rdt_send[extract[s.packet], s''])
	)
}
run { one s:NetState | one p: Packet | 
		let s' = s.next | s.verify[p, s'] } for exactly 2 NetState,  2 Data,  exactly 2 Packet, exactly 2 Checksum

pred Packet.IsCorrupt[] {
	not this.c = (this.(Global.pToD)).(Global.dToC)
}

pred NetState.rdt_receive[p: Packet, s: NetState] {
	no this.packet
	one d: Data | d = extract[p] and this.deliver_data[d] and this.receiverBuffer = s.receiverBuffer + d
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
	Trace => (
		all d: Data | d in first.senderBuffer and d in last.receiverBuffer and
		all s: NetState | Data = s.senderBuffer + s.receiverBuffer + extract[s.packet] and
		some s:NetState | Data = s.receiverBuffer and not Data in s.senderBuffer
	)
}
check AlwaysPossibleToTransmitAllData for 7 but 15 NetState expect 0
