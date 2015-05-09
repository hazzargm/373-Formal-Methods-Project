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
one sig Ack extends Reply{}
one sig Nak extends Reply{}

/** Start & End States **/
pred NetState.Init[] {
	all d: Data | d in this.senderBuffer
	no d:Data | d in this.receiverBuffer
	no this.packet
	no this.reply
}
run Init for exactly 1 NetState,  exactly 2 Data,  exactly 2 Packet, exactly 2 Checksum

pred NetState.End[] {
	no d:Data | d in this.senderBuffer	
	all d: Data | d in this.receiverBuffer
	no this.packet
	no this.reply
}
run End for exactly 1 NetState, exactly 4 Data, exactly 4 Packet

/** Facts **/
fact DataInOnlyOneBuffer{
	all s: NetState | no d: Data | d in s.senderBuffer and d in s.receiverBuffer
}

/** Functions **/
fun NetState.make_pkt[d: Data, c: Checksum]: Packet {
	{p:Packet | one (Global.pToD).d implies ((p->d in Global.pToD) and (d -> c in Global.dToC))}
}

fun NetState.extract[p: Packet]: Data {
	{d: Data | one p.(Global.pToD) implies p->d in Global.pToD}
}

pred Packet.IsCorrupt[] {
	not (this.c = (this.(Global.pToD)).(Global.dToC))
}

/** Preds **/

pred NetState.rdt_send[d: Data, s: NetState] { // this = State A(sending), s = State B (receiving)
	d in this.senderBuffer
	s.senderBuffer = this.senderBuffer
	one p: Packet | one c: Checksum | (p = this.make_pkt[d, c]) and this.udt_send[p]
	no this.reply
}
run rdt_send for exactly 2 NetState,  exactly 2 Data,  exactly 2 Packet, exactly 2 Checksum

pred NetState.udt_send[p: Packet] {
	this.packet = p
}

pred NetState.rdt_receive[p: Packet, s, s': NetState] {  // s = State A(sending), this = State B(receiving/acknowledging), s' = State C(sending)
	no this.packet
	no s.reply
	no s'.reply
	s.packet = p
	this.senderBuffer= s.senderBuffer
	this.receiverBuffer = s'.receiverBuffer
	p.IsCorrupt => ((this.reply = Nak) and
							  (this.receiverBuffer = s.receiverBuffer) and
							  (this.senderBuffer = s'.senderBuffer) and
							  (s.packet = s'.packet))
	else (this.reply = Ack and (one d: Data | ((d = this.extract[p]) and
																		(this.deliver_data[d]) and
																	    (s'.receiverBuffer = s.receiverBuffer + d) and
																	    (s'.senderBuffer = s.senderBuffer - d))))
}
run rdt_receive for exactly 3 NetState, exactly 1 Data, exactly 1 Packet, exactly 1 Checksum

pred NetState.deliver_data[d: Data] {
	d in this.receiverBuffer
}

/* Don't think this is the way we want to go about this
pred NetState.acknowledge[s, s':NetState] {
	no this.packet
	no s.reply
	no s'.reply
	this.senderBuffer = s'.senderBuffer
	this.receiverBuffer = s'.receiverBuffer
	(this.reply = Ack) => ((some d: s.senderBuffer | ((d = s.extract[s.packet]) and
																				 (d in this.receiverBuffer) and 
																			     (this.senderBuffer = s.senderBuffer - d))) and
										 (some s'': NetState - (this + s + s') | some d: s'.senderBuffer | s'.rdt_send[d, s'']))
	(this.reply = Nak) => ((this.senderBuffer = s.senderBuffer) and
										 (this.receiverBuffer = s.receiverBuffer) and
										 (s.senderBuffer = s'.senderBuffer) and
										 (s.receiverBuffer = s'.receiverBuffer) and
										 (some s'': NetState - (this + s + s') | s = s'' and s'.rdt_send[s.extract[s.packet], s'']))
}
run acknowledge for exactly 4 NetState, exactly 1 Data, exactly 1 Packet, exactly 1 Checksum
*/

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
	all s: NetState - (last + first + last.prev)| let s' = s.next | //removed last.prev because of the s'.next in the receive function
		not Skip[s,s'] and
		((one d: Data | s.rdt_send[d, s']) or (s'.rdt_receive[s.packet, s, s'.next]))
}
run SuccessTrace for 6 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum
/*
assert AlwaysPossibleToTransmitAllData {
	Trace => 
		all d: Data | d in first.senderBuffer and d in last.receiverBuffer and
		all s: NetState | Data = s.senderBuffer + s.receiverBuffer + s.extract[s.packet] and
		some s:NetState | Data = s.receiverBuffer and not Data in s.senderBuffer
}
check AlwaysPossibleToTransmitAllData for 7 but 15 NetState expect 0
*/
