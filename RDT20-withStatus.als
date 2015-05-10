module RDT10
/*
	CSSE 373 - Sprint 1: Checking RDT 2.0
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
abstract sig Status {}
one sig Idle, Sending, Verifying, Receiving extends Status {}

abstract sig NetState {
	status : one Status,
	senderBuffer: set Data,
	receiverBuffer: set Data,
	packet: lone Packet,
	reply: lone Reply,
	lastSent : lone Data
}

abstract sig Reply{}
one sig Ack, Nak extends Reply{}

/** Start & End States **/
pred NetState.Init_Corrupt[] {
	this.status = Idle
	all d: Data | d in this.senderBuffer and not d in this.receiverBuffer
	no this.packet
	no this.reply
	no this.lastSent
	some p:Packet | p.IsCorrupt
}
run Init_Corrupt for exactly 1 NetState,  exactly 2 Data,  exactly 2 Packet, exactly 2 Checksum

pred NetState.Init[] {
	this.status = Idle
	all d: Data | d in this.senderBuffer and not d in this.receiverBuffer
	no this.packet
	no this.reply
	no this.lastSent
	all p: Packet | not p.IsCorrupt
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

fact NoDataLoss {
	all s: NetState | Data = s.senderBuffer + s.receiverBuffer
	all s: NetState | (s.status = Receiving or s.status = Verifying) implies one s.lastSent
}

/** Functions **/
fun make_good_pkt[d: Data]: Packet {
	{p:Packet | 
		one (Global.pToD).d implies 
		d->(p.c) in Global.dToC and (p->d in Global.pToD )}
}

fun make_bad_pkt[d: Data]: Packet {
	{p:Packet | 
		one (Global.pToD).d implies 
		not d->(p.c) in Global.dToC}
}

fun extract[p: Packet]: Data {
	{d: Data | one p.(Global.pToD) implies p->d in Global.pToD}
}

/** Preds **/
pred NetState.rdt_send[s: NetState] { // this = State A(sending), s = State B (receiving/verifying)
	// some condiitons added to run this instance
	one s
	
	// true in this state
	no this.reply
	this.status = Sending
	
	// true in the next state (verify)
	s.senderBuffer = this.senderBuffer
	s.receiverBuffer = this.receiverBuffer
	one s.reply
	one s.packet
	s.status = Verifying
	
	// make a packet for this state
	one d: this.senderBuffer | 
		this.packet = make_good_pkt[d] and
		s.lastSent = d and
		(s.packet = make_good_pkt[d] or s.packet = make_bad_pkt[d])
}
run { one s:NetState | let s' = s.next |
		s.rdt_send[s'] } for exactly 2 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum

pred NetState.udt_send[p: Packet] {
	this.packet = p
}

pred NetState.verify[recvState:NetState] {
	// some condiitons added to run this instance
	one recvState
	
	// true in this state
	one this.packet // maybe corrupt
	one this.reply
	this.status = Verifying
	
	// true in the next state (receive)
	recvState.reply = this.reply
	no recvState.packet
	recvState.status = Receiving
	recvState.lastSent = this.lastSent
	
	// set the reply
	not this.packet.IsCorrupt implies this.reply = Ack else this.reply = Nak
	// ... and operate based on it
	this.reply = Ack => (
		(one d : this.senderBuffer | 
			d = this.lastSent and
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
run { one s:NetState | let s' = s.next | 
		s.verify[s'] } for exactly 2 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum

pred Packet.IsCorrupt[] {
	not this.c = (this.(Global.pToD)).(Global.dToC)
}

pred NetState.rdt_receive[s: NetState] {
	// true in this state
	this.status = Receiving
	one this.reply

	// true in next state (sending)
	s.status = Sending
	s.senderBuffer = this.senderBuffer
	s.receiverBuffer = this.receiverBuffer
	
	one d: Data | 
		d = extract[p] and 
		this.deliver_data[d] and 
		this.receiverBuffer = s.receiverBuffer + d
}

pred NetState.deliver_data[d: Data] {
	d in this.receiverBuffer
}

pred Skip[s,s': NetState] {
	s.receiverBuffer = s'.receiverBuffer
	s.senderBuffer = s'.senderBuffer
	s.packet = s'.packet
	s.reply = s'.reply
	s.lastSend = s'.lastSend
	s.status = s'.status
}

pred Trace[] {
	first.Init
	last.End
	all s: NetState - last | let s' = s.next |
		not Skip[s,s'] and 
		(s.rdt_send[s'] or s'.rdt_receive[s.packet, s])
}
run Trace for 7 but exactly 3 Data, exactly 3 Packet

assert AlwaysPossibleToTransmitAllData {
	Trace => (
		all d: Data | d in first.senderBuffer and d in last.receiverBuffer and
		some s:NetState | Data = s.receiverBuffer and not Data in s.senderBuffer
	)
}
check AlwaysPossibleToTransmitAllData for 7 but 15 NetState expect 0
