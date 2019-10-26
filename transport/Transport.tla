---- MODULE Transport ----
\* When establishing a connection the initiator must know the addr, port and
\* peer_id of the responder, where the peer_id is a hash of the peer's public
\* key: peer_id = hash(s).
\*
\* # Handshake phase
\* 
\* ## Message format
\* (drf: bool, seq_num: u16, handshake: [u8], payload: [u8])
\*
\* ## Protocol 
\* XXsig:
\*   -> (true, n, e, []) where n: random(u16)
\*   <- (false, n+1, e ee s sig, addr) where addr is the observed external address
\*   -> (false, n+2, s sig, [])
\*
\* # Transport phase
\* 
\* ## Message format
\* (nonce: u64, mac: u16, seq_num: u16, ack_seq_num: u16, len: u16, payload: [])
\*
\* ## Protocol
\* Messages with a seq_num of 0 do not require an ack or retransmission. Such
\* messages are called control messages.
\*
\* The nonce is used to encrypt and decrypt the rest of the message and is the
\* only part of a message sent unencrypted.
\*
\* # Close
\*
\* # Congestion control

Token == {"e", "ee", "s", "sig"}

Message == Seq(Token)

Handshake == Seq(Message)

XXsig == <<
  <<"e">>,
  <<"e", "ee", "s", "sig">>,
  <<"s", "sig">>,
>>

====
