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
pred NetState.Init[] {
	this.status = Receiving
	all d: Data | d in this.senderBuffer and not d in this.receiverBuffer
	no this.packet
	no this.reply
	no this.lastSent
//	all p: Packet | not p.IsCorrupt
}
run Init for exactly 1 NetState,  exactly 2 Data,  exactly 2 Packet, exactly 2 Checksum

pred NetState.End[] {
	all d: Data | not d in this.senderBuffer and d in this.receiverBuffer  
//	all p:Packet | not p.IsCorrupt[]
	no this.packet
//	no this.reply
	this.status in Receiving
}
run End for exactly 1 NetState, exactly 2 Data,  exactly 2 Packet, exactly 2 Checksum

/** Facts **/
fact DataInOnlyOneBuffer{
	all s: NetState | no d: Data | d in s.senderBuffer and d in s.receiverBuffer
}

fact NoDataLoss {
	all s: NetState | Data = s.senderBuffer + s.receiverBuffer
//	all s: NetState | (s.status = Verifying) implies one s.lastSent
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
//	one s and s = this.next
	
	// true in this state
	this.status = Sending
	no this.reply
	one this.packet
	
	// true in the next state (verify)
	s.status = Verifying
	s.senderBuffer = this.senderBuffer
	s.receiverBuffer = this.receiverBuffer
	one s.reply
	one s.packet
	
	// make a packet for this state
	one d: this.senderBuffer | (
		s.lastSent = d and
		this.packet = make_good_pkt[d]
	)
}
pred SimulateSend {  all s:NetState-last | let s' = s.next | s.rdt_send[s'] }
run SimulateSend for exactly 2 NetState, exactly 1 Data, exactly 1 Packet, exactly 1 Checksum

pred NetState.udt_send[p: Packet] {
	this.packet = p
}

pred NetState.verify[recvState:NetState] {
	// some condiitons added to run this instance
//	one recvState and recvState = this.next
	
	// true in this state
	this.status = Verifying
	one this.packet and // maybe corrupt
		one d:Data | (this.packet->d in Global.pToD)	
	
	// true in the next state (receive)
	recvState.status = Receiving
	no recvState.reply
	no recvState.packet
	recvState.lastSent = this.lastSent
	
	// set the reply
	one this.reply and 
		this.lastSent = extract[this.packet] implies this.reply = Ack else this.reply = Nak
	// ... and operate based on it
	this.reply = Ack => (
		(one d : this.lastSent |
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
pred SimulateVerify {  all s:NetState-last | let s' = s.next | s.verify[s'] }
run SimulateVerify for exactly 2 NetState, exactly 1 Data, exactly 1 Packet, exactly 1 Checksum

pred Packet.IsCorrupt[] {
	not this.c = (this.(Global.pToD)).(Global.dToC)
}

pred NetState.rdt_receive[s: NetState] {
//	one s and s = this.next

	// true in this state
	this.status = Receiving
	no this.reply
	no this.packet
	// one this.lastSent

	// true in next state (sending)
	s.status = Sending
	s.senderBuffer = this.senderBuffer
	s.receiverBuffer = this.receiverBuffer
	no s.packet
	no s.reply
	s.lastSent = this.lastSent
	
//	one d: Data | 
	//	d = extract[p] and 
		//this.deliver_data[d] and 
	//	this.receiverBuffer = s.receiverBuffer + d
}
pred SimulateReceive {  all s:NetState-last | let s' = s.next | s.rdt_receive[s'] }
run SimulateReceive for exactly 2 NetState, exactly 1 Data, exactly 1 Packet, exactly 1 Checksum

pred NetState.deliver_data[d: Data] {
	d in this.receiverBuffer
}

pred send_verify[s, s', s'': NetState] { s.next = s' and s'.next = s'' and s.rdt_send[s'] and s'.verify[s''] }
run send_verify for 1 but exactly 3 NetState

pred verify_receive[s, s', s'': NetState] { s.next = s' and s'.next = s'' and s.verify[s'] and s'.rdt_receive[s''] }
run verify_receive for 2 but exactly 3 NetState

pred receive_send[s, s', s'': NetState] { s.next = s' and s'.next = s'' and s.rdt_receive[s'] and s'.rdt_send[s''] }
run receive_send for 2 but exactly 3 NetState

pred Skip[s,s': NetState] {
	s.receiverBuffer = s'.receiverBuffer
	s.senderBuffer = s'.senderBuffer
	s.packet = s'.packet
	s.reply = s'.reply
	s.lastSent = s'.lastSent
	s.status = s'.status
}

pred Transition[s, s', s'' : NetState] {
//	s' = s.next and s'' = s'.next
	not (Skip[s,s'] or Skip[s', s''])
	
	send_verify[s, s', s''] or
	verify_receive[s, s', s''] or
	receive_send[s, s', s'']
}
run Transition for exactly 3 NetState, exactly 1 Data, exactly 1 Packet, exactly 1 Checksum

pred Trace[] {
	first.Init
	last.End
	all s: NetState - (last + last.prev) | let s' = s.next | let s'' = s'.next |
		Transition[s, s', s'']
}
run Trace for 2 but 10 NetState

assert AlwaysPossibleToTransmitAllData {
	Trace => (
		all d: Data | d in first.senderBuffer and d in last.receiverBuffer
	//	some s:NetState | Data = s.receiverBuffer and not Data in s.senderBuffer
	)
}
check AlwaysPossibleToTransmitAllData for 2 but 7 NetState expect 0
