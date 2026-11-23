module
public import Sake.Terms
public import Commonware.Symbolic.Client
public import DY.Actions.Network
public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentLocalState
public import DY.Actions.LongTermKeys
public import DY.Comparse
import DY.Meta

/-! The DyLean protocol around the extracted SAKE steps. Trusted: the events, what a peer keeps
between its steps, the messages on the network, the actions, what the attacker may compromise
and the `#combine` configuration.

Each action looks up identity keys in a public-key infrastructure that stands for the peer set
an application configures, draws its randomness, runs one extracted production step with
`Commonware.Symbolic.run`, logs what the step did, stores what the step keeps and sends the
message that the step returns. The attacker controls the network and the schedule: it chooses
who dials whom, every namespace, clock value and window, the claimed dialer of a `Syn` and the
timestamps of the messages that a peer receives. Timestamps are public, so they are inputs of
the receiving action and not fields of the message on the network.

The attacker can compromise any identity key. It can also compromise what a peer keeps between
its steps, at any time, including after the handshake has finished. What a peer keeps is stored
twice: as the record that its next step reads, and as its secret part, which is what a
compromise reveals. The secret part of a dialer is its ephemeral secret, and that of a listener
is the secret transcript; everything else a peer keeps is public. -/

namespace Sake
open DY DY.Comparse Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-- What the trace records about handshakes. A `secret` is the secret
transcript that the peer derived. -/
inductive Event where
  /-- A dialer starts a handshake. -/
  | dialStart (dialer : Participant) (opening : Opening)
  /-- A listener answers the first message of a handshake. -/
  | listenStart
      (listener : Participant) (exchange : Exchange) (secret : Bytes)
  /-- A dialer finishes a handshake with the listener it looked up. -/
  | dialFinish
      (dialer listener : Participant) (exchange : Exchange) (secret : Bytes)
  /-- A listener finishes a handshake with the dialer it looked up. -/
  | listenFinish
      (listener dialer : Participant) (exchange : Exchange) (secret : Bytes)

/-- What a dialer keeps between its steps. -/
structure Dialing where
  /-- The listener it looked up. -/
  listener : Participant
  /-- What it fixed when it started. -/
  opening : Opening
  /-- Its ephemeral secret. -/
  secret : Bytes
  /-- The transcript that its first step returned. -/
  transcript : Bytes
  /-- The listener timestamps it accepts. -/
  window : sake.Window

/-- What a listener keeps between its steps. -/
structure Listening where
  /-- The dialer it looked up. -/
  dialer : Participant
  /-- What it agreed to when it answered. -/
  exchange : Exchange
  /-- The secret transcript that its first step returned. -/
  transcript : Bytes

/-- The secret part of what a dialer keeps, which the attacker may
compromise. -/
structure DialerSecret where
  /-- The dialer's ephemeral public key. -/
  epk : Bytes
  /-- The dialer's ephemeral secret. -/
  esk : Bytes

/-- The secret part of what a listener keeps, which the attacker may
compromise. -/
structure ListenerSecret where
  /-- The listener's ephemeral public key. -/
  epk : Bytes
  /-- The secret transcript. -/
  transcript : Bytes

/-- The first message on the network. -/
structure SynMessage where
  /-- The dialer's ephemeral public key. -/
  epk : Bytes
  /-- The dialer's signature. -/
  sig : Bytes

/-- The second message on the network. -/
structure SynAckMessage where
  /-- The listener's ephemeral public key. -/
  epk : Bytes
  /-- The listener's signature. -/
  sig : Bytes
  /-- The listener's confirmation. -/
  confirmation : Bytes

instance : ParseableSerializeable SynMessage := .make <|
  .triviallyIsomorphic
    (.prod .unboundedBytes .bytes)
    (fun ⟨epk, sig⟩ => { epk, sig })
    (fun { epk, sig } => ⟨epk, sig⟩)

instance : ParseableSerializeable SynAckMessage := .make <|
  .triviallyIsomorphic
    (.prod .unboundedBytes (.prod .unboundedBytes .bytes))
    (fun ⟨epk, sig, confirmation⟩ => { epk, sig, confirmation })
    (fun { epk, sig, confirmation } => ⟨epk, sig, confirmation⟩)

instance : ParseableSerializeable DialerSecret := .make <|
  .triviallyIsomorphic
    (.prod .unboundedBytes .bytes)
    (fun ⟨epk, esk⟩ => { epk, esk })
    (fun { epk, esk } => ⟨epk, esk⟩)

instance : ParseableSerializeable ListenerSecret := .make <|
  .triviallyIsomorphic
    (.prod .unboundedBytes .bytes)
    (fun ⟨epk, transcript⟩ => { epk, transcript })
    (fun { epk, transcript } => ⟨epk, transcript⟩)

instance : LongTermKeys.ExecConfig "SAKE PKI" Signature.vk where

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  Random,
  ProtocolEvent Event,
  PersistentLocalState.State Dialing,
  PersistentLocalState.State Listening,
  PersistentLocalState.CompromisableState DialerSecret,
  PersistentLocalState.CompromisableState ListenerSecret,
  LongTermKeys "SAKE PKI",

/-- The attacker compromised what `dialer` keeps for the ephemeral key `epk`:
its ephemeral secret. -/
def DialerCompromised
    (dialer : Participant) (epk : Bytes) (tr : ExecTrace) : Prop :=
  ∃ esk, PersistentLocalState.LocalStateCompromised dialer
    ({ epk, esk } : DialerSecret) tr

/-- The attacker compromised what `listener` keeps for the ephemeral key
`epk`: the secret transcript. -/
def ListenerCompromised
    (listener : Participant) (epk : Bytes) (tr : ExecTrace) : Prop :=
  ∃ transcript, PersistentLocalState.LocalStateCompromised listener
    ({ epk, transcript } : ListenerSecret) tr

noncomputable section

/-- Continue only if `event` has not been logged yet. Production finishes a
handshake at most once from what a peer kept, because finishing consumes it;
this check stands for that. -/
def firstTime (event : Event) : Traceful Unit :=
  Traceful.mk fun tr =>
    open Classical in
    if tr.EventLogged event then (none, ⟨tr, Trace.le_refl tr⟩)
    else (some (), ⟨tr, Trace.le_refl tr⟩)

/-- A dialer starts a handshake with `listener` in the namespace `ns`. Its
clock reads `now` and it will accept listener timestamps in `window`. -/
def dial
    (me listener : Participant) (skHandle pkHandle : Nat)
    (ns : ByteArray) (now : Std.U64) (window : sake.Window) :
    Traceful (Nat × Nat × Nat) := do
  let key ← LongTermKeys.getPrivateKey "SAKE PKI" me skHandle
  let listenerKey ← LongTermKeys.getPublicKey "SAKE PKI" listener pkHandle
  let drawn ← Random.genRand 32
  let nonce ← Random.genRand 32
  let (secret, transcript, syn) ←
    run (sake.dial_start sakeTerms signer peer fresh ()
      { early := true, transcript := start ns, now, window,
        signer := ⟨key, nonce⟩, peer := listenerKey } drawn)
  let opening : Opening :=
    { ns, dialer := Signature.vk key, listener := listenerKey,
      dialed := syn.time_ms, dialerKey := syn.epk }
  ProtocolEvent.logEvent (Event.dialStart me opening)
  let stHandle ← PersistentLocalState.storeLocalState me
    ({ listener, opening, secret, transcript, window } : Dialing)
  let secretHandle ← PersistentLocalState.storeLocalState me
    ({ epk := syn.epk, esk := secret } : DialerSecret)
  let msgHandle ← Network.sendMessage
    (serialize ({ epk := syn.epk, sig := syn.sig } : SynMessage))
  return (stHandle, secretHandle, msgHandle)

/-- A listener answers the `Syn` at `msgHandle`, stamped `dialed`, as a
handshake from `dialer` in the namespace `ns`. Its clock reads `now` and it
accepts dialer timestamps in `window`. -/
def listen
    (me dialer : Participant) (skHandle pkHandle msgHandle : Nat)
    (ns : ByteArray) (now : Std.U64) (window : sake.Window)
    (dialed : Std.U64) :
    Traceful (Nat × Nat × Nat) := do
  let received ← Network.receiveMessage msgHandle
  let msg : SynMessage ← parse received
  let key ← LongTermKeys.getPrivateKey "SAKE PKI" me skHandle
  let dialerKey ← LongTermKeys.getPublicKey "SAKE PKI" dialer pkHandle
  let drawn ← Random.genRand 32
  let nonce ← Random.genRand 32
  let .Ok (transcript, synAck) ←
    run (sake.listen_start sakeTerms signer peer fresh ()
      { early := true, transcript := start ns, now, window,
        signer := ⟨key, nonce⟩, peer := dialerKey } drawn
      { time_ms := dialed, epk := msg.epk, sig := msg.sig })
    | failure
  let exchange : Exchange :=
    { ns, dialer := dialerKey, listener := Signature.vk key, dialed,
      dialerKey := msg.epk, answered := synAck.time_ms,
      listenerKey := synAck.epk }
  ProtocolEvent.logEvent (Event.listenStart me exchange transcript)
  let stHandle ← PersistentLocalState.storeLocalState me
    ({ dialer, exchange, transcript } : Listening)
  let secretHandle ← PersistentLocalState.storeLocalState me
    ({ epk := synAck.epk, transcript } : ListenerSecret)
  let answer : SynAckMessage :=
    { epk := synAck.epk, sig := synAck.sig,
      confirmation := synAck.confirmation }
  let msgHandle ← Network.sendMessage (serialize answer)
  return (stHandle, secretHandle, msgHandle)

/-- A dialer finishes the handshake it kept at `stHandle` on the `SynAck` at
`msgHandle`, stamped `answered`, and sends its confirmation. It finishes an
exchange at most once. -/
def finishDial
    (me : Participant) (stHandle msgHandle : Nat) (answered : Std.U64) :
    Traceful Nat := do
  let kept : Dialing ← PersistentLocalState.getLocalState me stHandle
  let received ← Network.receiveMessage msgHandle
  let msg : SynAckMessage ← parse received
  let .Ok (confirmation, secret) ←
    run (sake.dial_end sakeTerms peer () kept.secret kept.transcript
      kept.opening.listener kept.window
      { time_ms := answered, epk := msg.epk, sig := msg.sig,
        confirmation := msg.confirmation })
    | failure
  let exchange : Exchange :=
    { kept.opening with answered := answered, listenerKey := msg.epk }
  firstTime (Event.dialFinish me kept.listener exchange secret)
  ProtocolEvent.logEvent (Event.dialFinish me kept.listener exchange secret)
  Network.sendMessage confirmation

/-- A listener finishes the handshake it kept at `stHandle` on the
confirmation at `msgHandle`. It finishes an exchange at most once. -/
def finishListen
    (me : Participant) (stHandle msgHandle : Nat) :
    Traceful Unit := do
  let kept : Listening ← PersistentLocalState.getLocalState me stHandle
  let confirmation ← Network.receiveMessage msgHandle
  let .Some secret ←
    run (sake.listen_end sakeTerms () kept.transcript confirmation)
    | failure
  firstTime (Event.listenFinish me kept.dialer kept.exchange secret)
  ProtocolEvent.logEvent
    (Event.listenFinish me kept.dialer kept.exchange secret)

/-- The attacker compromises the secret part of what a dialer keeps. -/
def compromiseDialer (handle : Nat) : Traceful Nat :=
  PersistentLocalState.compromise DialerSecret handle

/-- The attacker compromises the secret part of what a listener keeps. -/
def compromiseListener (handle : Nat) : Traceful Nat :=
  PersistentLocalState.compromise ListenerSecret handle

/-- Starting a dial as a step of reachable traces, for any inputs. -/
def dial.reachability : ReachabilityConfig :=
  .make fun (me, listener, skHandle, pkHandle, ns, now, window) =>
    dial me listener skHandle pkHandle ns now window

/-- Answering a `Syn` as a step of reachable traces, for any inputs. -/
def listen.reachability : ReachabilityConfig :=
  .make fun
    (me, dialer, skHandle, pkHandle, msgHandle, ns, now, window, dialed) =>
    listen me dialer skHandle pkHandle msgHandle ns now window dialed

/-- Finishing a dial as a step of reachable traces, for any inputs. -/
def finishDial.reachability : ReachabilityConfig :=
  .make fun (me, stHandle, msgHandle, answered) =>
    finishDial me stHandle msgHandle answered

/-- Finishing a listen as a step of reachable traces, for any inputs. -/
def finishListen.reachability : ReachabilityConfig :=
  .make fun (me, stHandle, msgHandle) => finishListen me stHandle msgHandle

/-- Compromising a dialer as a step of reachable traces, for any handle. -/
def compromiseDialer.reachability : ReachabilityConfig :=
  .make fun handle => compromiseDialer handle

/-- Compromising a listener as a step of reachable traces, for any handle. -/
def compromiseListener.reachability : ReachabilityConfig :=
  .make fun handle => compromiseListener handle

#combine into ReachabilityConfig from
  Network,
  Random,
  LongTermKeys "SAKE PKI",
  dial,
  listen,
  finishDial,
  finishListen,
  compromiseDialer,
  compromiseListener,

end

end
end Sake
