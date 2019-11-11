---- MODULE Transport ----
\* When establishing a connection the initiator must know the addr, port and
\* peer_id of the responder, where the peer_id is a hash of the peer's public
\* key: peer_id = hash(s).
\*
\* # Handshake phase
\* 
\* ## Message format
\* (drf: bool, seq_num: u64, handshake: [u8], payload: [u8])
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
\* (nonce: u64, mac: u16, seq_num: u64, ack_seq_num: u64, len: u16, payload: [])
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

CONSTANT Data

VARIABLE conns

Conn == [
    sSn: Nat,
    msgs: Seq(Data)
]

HandshakeMessage == [drf: BOOLEAN, sn: Nat]

TransportMessage == [
    nonce: Nat,
    mac: Nat,
    seq_num: Nat,
    ack_seq_num: Nat
]

Init ==
    /\ conns = << >>

TypeInv ==
    /\ conns \in Seq(Conn)

Open ==
    /\ conns' = Append(conns, [msgs |-> << >>])


----

Encrypt[conn \in Conn, data \in Data] == [conn EXCEPT !.msgs = Append(@, data)]

Decrypt[conn \in Conn, nonce \in Nat] == conn.msgs[nonce]

Send(c, d) ==
    /\ c \in 1..Len(conns)
    /\ 'conns = [conns EXCEPT ![c] = Encrypt[@, d]]

Recv(c, n) ==
    /\ c \in 1..Len(conns)
    /\ LET msg == Decrypt[conns[c], n]
       IN



====
