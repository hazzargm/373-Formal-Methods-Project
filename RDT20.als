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
pred NetState.rdt_send[d: Data, s: NetState] {
	d in this.senderBuffer
	s.senderBuffer = this.senderBuffer
//	s.receiverBuffer = this.receiverBuffer
	one p: Packet | one c: Checksum | p = this.make_pkt[d, c]
	no this.reply
}

pred NetState.udt_send[p: Packet] {
	this.packet = p
}

pred NetState.rdt_receive[p: Packet, s: NetState] {
	no this.packet
	p.IsCorrupt => (this.reply = Nak and this.receiverBuffer = s.receiverBuffer and this.senderBuffer = s.senderBuffer)
	else (this.reply = Ack and (one d: Data | d = this.extract[p] and
																	  this.deliver_data[d] and
																	  (this.receiverBuffer = s.receiverBuffer + d) and
																	  this.senderBuffer = s.senderBuffer - d))
}

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
	all s: NetState - last| let s' = s.next |
		not Skip[s,s'] and not s.reply = Nak and
		(one d: Data | s.rdt_send[d, s']) or s'.rdt_receive[s.packet, s]
}
run SuccessTrace for 6 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum
/**
assert AlwaysPossibleToTransmitAllData {
	Trace => 
		all d: Data | d in first.senderBuffer and d in last.receiverBuffer and
		all s: NetState | Data = s.senderBuffer + s.receiverBuffer + s.extract[s.packet] and
		some s:NetState | Data = s.receiverBuffer and not Data in s.senderBuffer
}
check AlwaysPossibleToTransmitAllData for 7 but 15 NetState expect 0
**/
