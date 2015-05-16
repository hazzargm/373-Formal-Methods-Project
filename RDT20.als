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
pred Packet.IsCorrupt[] {
	not this.c = (this.(Global.pToD)).(Global.dToC)
}

pred recv_send[s, s': NetState] {
	no s.reply and no s'.reply
	no s.packet
	s.senderBuffer = s'.senderBuffer
	s.receiverBuffer = s'.receiverBuffer
	some d: Data |
							((d in s.senderBuffer) and (d in s'.senderBuffer) and
							  (one p: Packet | one c: Checksum | (s'.packet = p  and s'.packet = make_pkt[d,c])))
}
run recv_send for exactly 2 NetState, exactly 1 Data,  exactly 1 Packet, exactly 1 Checksum

pred send_verify[s, s': NetState] {
	no s.reply
	one p: Packet | p = s.packet and p = s'.packet
	(s.packet).IsCorrupt[] => s'.reply = Nak else s'.reply = Ack
	some d: s'.senderBuffer | d = extract[s.packet]
	s.senderBuffer = s'.senderBuffer
	s.receiverBuffer = s'.receiverBuffer
}
run send_verify for exactly 2 NetState, exactly 2 Data,  exactly 2 Packet, exactly 2 Checksum

pred verify_recv[s, s': NetState] {
	no s'.packet
	no s'.reply
	one p: Packet | (s.packet = p and (one d: s.senderBuffer | d = extract[p]))
	(s.reply = Ack) => (one d: Data | ((s'.senderBuffer = s.senderBuffer - d) and (s'.receiverBuffer = s.receiverBuffer + d))) else 
	((s.reply = Nak) and	(s'.senderBuffer = s.senderBuffer and s'.receiverBuffer = s.receiverBuffer))
}
run verify_recv for exactly 2 NetState, exactly 1 Data,  exactly 1 Packet, exactly 1 Checksum


pred recv_send_verify[s, s', s'': NetState] {
	recv_send[s, s']
	send_verify[s', s'']
}
run recv_send_verify for exactly 3 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum

pred send_verify_recv[s, s', s'': NetState] {
	send_verify[s, s']
	verify_recv[s', s'']
	(s'.reply = Ack) => (one d: s.senderBuffer | (d = extract[s.packet] and (d in s''.receiverBuffer))) else 
	(s'.reply = Nak and s.senderBuffer = s''.senderBuffer and s.receiverBuffer = s''.receiverBuffer)
}
run send_verify_recv for exactly 3 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum

pred verify_recv_send[s, s', s'': NetState] {
	verify_recv[s, s']
	recv_send[s',s'']
	(s.reply = Ack) => (not (s.packet = s''.packet)) else
	((s.reply = Nak) and (s.packet = s''.packet))
}
run verify_recv_send for exactly 3 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum


/**Checking the Properties**/
pred Skip[s,s': NetState] {
	s.receiverBuffer = s'.receiverBuffer
	s.senderBuffer = s'.senderBuffer
	s.packet = s'.packet
	s.reply = s'.reply
}

pred SuccessTrace[] { //look at first instance
	first.Init
	last.End
	all s: NetState - (last + last.prev) |
		let s' = s.next | let s'' = s'.next |
			((not (Skip[s,s'] or Skip[s', s''] or Skip[s, s''])) and
			  ((recv_send_verify[s, s', s'']) or 
				(send_verify_recv[s, s', s'']) or
				(verify_recv_send[s, s', s''])))
}
run SuccessTrace for exactly 7 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum

pred NakTrace[] { //press 'next' to look at the second instance
	first.Init
	not last.End
	all s: NetState - (last + last.prev) |
		let s' = s.next | let s'' = s'.next |
			((not (Skip[s,s'] or Skip[s', s''] or Skip[s, s''])) and
			  ((recv_send_verify[s, s', s'']) or 
				(send_verify_recv[s, s', s'']) or
				(verify_recv_send[s, s', s''])))
}
run NakTrace for exactly 7 NetState, exactly 2 Data, exactly 2 Packet, exactly 2 Checksum


assert AlwaysPossibleToTransmitAllData {
	(SuccessTrace or NakTrace) => (
		all d: Data | d in first.senderBuffer and d in last.receiverBuffer and
		all s: NetState | Data = s.senderBuffer + s.receiverBuffer + extract[s.packet] and
		some s:NetState | Data = s.receiverBuffer and not Data in s.senderBuffer
		)
}
check AlwaysPossibleToTransmitAllData for 2 but 7 NetState

