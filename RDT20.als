module RDT20
/*
	CSSE 373 - Sprint 2: Checking RDT 2.0
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
	d in this.senderBuffer
	no this.reply
	s.senderBuffer = this.senderBuffer
	s.receiverBuffer = this.receiverBuffer // at 'this' state we want this true
	one p: Packet | one c: Checksum | p = make_pkt[d, c] and this.udt_send[p]
}
run rdt_send for exactly 2 NetState,  exactly 2 Data,  exactly 2 Packet, exactly 2 Checksum

pred NetState.udt_send[p: Packet] {
	this.packet = p
}

/* Don't think this is the way we want to go about this */
pred NetState.verify[recvP:Packet, recvState:NetState] {
	one p:Packet | this.packet = p and p.c = recvP.c implies this.reply = Ack else this.reply = Nak
	
	this.reply = Ack => (
		(one d: this.senderBuffer | 
			d = extract[recvP] and
			d in recvState.receiverBuffer and 
			recvState.senderBuffer = this.senderBuffer - d
		) 
//		 	and	(some s'': NetState - (this + s + s') | some d: s'.senderBuffer | s'.rdt_send[d, s''])
	) else this.reply = Nak => (
		this.senderBuffer = recvState.senderBuffer and
		this.receiverBuffer = recvState.receiverBuffer
//		and (some s'': NetState - (this + s + s') | s = s'' and s'.rdt_send[extract[s.packet], s''])
	)
}

pred Packet.IsCorrupt[] {
	not this.c = (this.(Global.pToD)).(Global.dToC)
}

pred NetState.rdt_receive[r:Reply, prevSend, nextSend: NetState] {  // s = State A(verifying), this = State B(receiving), s' = State C(sending)
	no this.packet
	no this.reply
	this.senderBuffer = nextSend.senderBuffer
	this.receiverBuffer = nextSend.receiverBuffer

	r = Nak => (
		prevSend.packet = nextSend.packet
	)
	else r = Ack => (
		one d: Data | (
			d = extract[prevSend.packet] and	
			this.deliver_data[d] and
			this.receiverBuffer = prevSend.receiverBuffer + d and
			this.senderBuffer = prevSend.senderBuffer - d
		)
	) // handled in verify
	
}
run rdt_receive for exactly 3 NetState, exactly 1 Data, exactly 1 Packet, exactly 1 Checksum

pred NetState.deliver_data[d: Data] {
	d in this.receiverBuffer
}

/**Checking the Properties**/
pred Skip[s,s': NetState] {
	s.receiverBuffer = s'.receiverBuffer
	s.senderBuffer = s'.senderBuffer
	s.packet = s'.packet
	s.reply = s'.reply
}

pred SuccessTrace[] {
	first.Init
	last.End
	all s: NetState - (first + last) |  //removed last.prev because of the s'.next in the receive function
		let s' = s.next | let s'' = s'.next |
			not (Skip[s,s'] or Skip[s', s'']) and 
			not (s.reply = Nak or s'.reply = Nak or s''.reply = Nak) and
			( 
				(
					(one d: Data | s.rdt_send[d, s']) and  
					s'.verify[s.packet, s''] and
					s''.rdt_receive[s'.reply, s, s''.next]
				) or
				(
					s.verify[s.prev.packet, s'] and
					s'.rdt_receive[s.reply, s.prev, s''] and
					(one d: Data | s''.rdt_send[d, s''.next])  
				) or
				(
					s.rdt_receive[s.prev.reply, s.prev.prev, s'] and
					(one d: Data | s'.rdt_send[d, s'']) and
					s''.verify[s'.packet, s''.next]
				) 
			)
}
run SuccessTrace for 7 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum
/*
assert AlwaysPossibleToTransmitAllData {
	Trace => (
		all d: Data | d in first.senderBuffer and d in last.receiverBuffer and
		all s: NetState | Data = s.senderBuffer + s.receiverBuffer + s.extract[s.packet] and
		some s:NetState | Data = s.receiverBuffer and not Data in s.senderBuffer
		)
}
check AlwaysPossibleToTransmitAllData for 7 but 15 NetState expect 0
*/
