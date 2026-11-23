module
public import Sake.Terms
public import Commonware.Symbolic.RustM

/-! What the extracted handshake steps compute on DyLean terms. Checked. Each lemma equates an
extracted production step, read through `Sake.Terms`, with the terms it returns: the transcripts
that the peers sign, the secret transcript and the confirmations. -/

namespace Sake
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-! ## Transcripts -/

/-- The transcript that the dialer signs: the namespace, its timestamp, both identities and its
ephemeral key. -/
def Opening.signed (o : Opening) : Bytes :=
  Concat.concat (Concat.concat (Concat.concat (Concat.concat (start o.ns) (stamp o.dialed))
    o.listener) o.dialer) o.dialerKey

/-- The transcript that the listener signs: what the dialer signed, then the listener's timestamp
and ephemeral key. -/
def Exchange.signed (e : Exchange) : Bytes :=
  Concat.concat (Concat.concat e.toOpening.signed (stamp e.answered)) e.listenerKey

/-- The confirmation of a transcript for a label. -/
def confirmation (transcript : Bytes) (label : Slice Std.U8) : Bytes :=
  KdfExpand.kdfExpand (Hash.hash transcript) (Literal.literalToBytes (toByteArray label)) 32

/-- The label of the listener's confirmation, `confirmation_l2d`. -/
def listenerLabel : Slice Std.U8 :=
  (Array.make 16#usize [
    99#u8, 111#u8, 110#u8, 102#u8, 105#u8, 114#u8, 109#u8, 97#u8, 116#u8,
    105#u8, 111#u8, 110#u8, 95#u8, 108#u8, 50#u8, 100#u8]).to_slice

/-- The label of the dialer's confirmation, `confirmation_d2l`. -/
def dialerLabel : Slice Std.U8 :=
  (Array.make 16#usize [
    99#u8, 111#u8, 110#u8, 102#u8, 105#u8, 114#u8, 109#u8, 97#u8, 116#u8,
    105#u8, 111#u8, 110#u8, 95#u8, 100#u8, 50#u8, 108#u8]).to_slice

theorem listenerLabel_eq : sake.LABEL_CONFIRMATION_L2D = RustM.ok listenerLabel := by
  simp [sake.LABEL_CONFIRMATION_L2D, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, listenerLabel]

theorem dialerLabel_eq : sake.LABEL_CONFIRMATION_D2L = RustM.ok dialerLabel := by
  simp [sake.LABEL_CONFIRMATION_D2L, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, dialerLabel]

/-! ## The dialer's first step -/

/-- The first step of a dialer returns its secret, the transcript it signed and a `Syn` with its
ephemeral key and its signature of that transcript. -/
theorem dial_start_eq (ns : ByteArray) (now : Std.U64) (window : sake.Window)
    (key nonce listener secret : Bytes) :
    sake.dial_start sakeTerms signer peer fresh ()
      { early := true, transcript := start ns, now, window, signer := ⟨key, nonce⟩,
        peer := listener } secret =
    let o : Opening :=
      { ns, dialer := Signature.vk key, listener, dialed := now,
        dialerKey := DiffieHellman.dhPk secret }
    RustM.ok (secret, o.signed,
      { time_ms := now, epk := o.dialerKey,
        sig := Signature.sign key nonce (Hash.hash o.signed) }) := by
  simp [sake.dial_start, sakeTerms, signer, peer, fresh, Opening.signed]

/-! ## The listener's first step -/

/-- The first step of a listener rejects a `Syn` whose timestamp is outside its window or whose
signature does not sign the opening under the dialer's identity. Otherwise it returns the secret
transcript and a `SynAck` with its ephemeral key, its signature of the exchange and its
confirmation. -/
theorem listen_start_eq (ns : ByteArray) (now : Std.U64) (window : sake.Window)
    (key nonce dialer secret : Bytes) (msg : sake.Syn Bytes Bytes) :
    sake.listen_start sakeTerms signer peer fresh ()
      { early := true, transcript := start ns, now, window, signer := ⟨key, nonce⟩,
        peer := dialer } secret msg =
    let e : Exchange :=
      { ns, dialer, listener := Signature.vk key, dialed := msg.time_ms, dialerKey := msg.epk,
        answered := now, listenerKey := DiffieHellman.dhPk secret }
    let agreed := Concat.concat e.signed (DiffieHellman.dh msg.epk secret)
    RustM.ok (
      if window.start ≤ msg.time_ms ∧ msg.time_ms < window.end then
        if Signature.verify dialer (Hash.hash e.toOpening.signed) msg.sig then
          .Ok (agreed,
            { time_ms := now, epk := e.listenerKey,
              sig := Signature.sign key nonce (Hash.hash e.signed),
              confirmation := confirmation agreed listenerLabel })
        else .Err .Signature
      else .Err .Timestamp) := by
  simp [sake.listen_start, sake.Window.contains, sakeTerms, signer, peer, fresh,
    listenerLabel_eq, Opening.signed, Exchange.signed, confirmation]
  split_ifs <;> simp_all

/-! ## The last steps -/

/-- The last step of a dialer extends the transcript it kept with the listener's timestamp and
ephemeral key. It rejects a `SynAck` whose timestamp is outside its window, whose signature does
not sign that transcript under the listener's identity, or whose confirmation is not that of the
secret transcript. Otherwise it returns its own confirmation and the secret transcript. -/
theorem dial_end_eq (secret transcript listener : Bytes) (window : sake.Window)
    (msg : sake.SynAck Bytes Bytes Bytes) :
    sake.dial_end sakeTerms peer () secret transcript listener window msg =
    let signed := Concat.concat (Concat.concat transcript (stamp msg.time_ms)) msg.epk
    let agreed := Concat.concat signed (DiffieHellman.dh msg.epk secret)
    RustM.ok (
      if window.start ≤ msg.time_ms ∧ msg.time_ms < window.end then
        if Signature.verify listener (Hash.hash signed) msg.sig then
          if msg.confirmation = confirmation agreed listenerLabel then
            .Ok (confirmation agreed dialerLabel, agreed)
          else .Err .Confirmation
        else .Err .Signature
      else .Err .Timestamp) := by
  simp [sake.dial_end, sake.Window.contains, sakeTerms, peer, listenerLabel_eq, dialerLabel_eq,
    confirmation]
  split_ifs <;> simp_all

/-- The last step of a listener returns the secret transcript it kept if the dialer's
confirmation is that of this transcript. -/
theorem listen_end_eq (transcript confirm : Bytes) :
    sake.listen_end sakeTerms () transcript confirm =
    RustM.ok (if confirm = confirmation transcript dialerLabel then .Some transcript else .None)
    := by
  simp [sake.listen_end, sakeTerms, dialerLabel_eq, confirmation]
  split_ifs <;> simp_all

/-- A signature of one message does not verify for another. -/
theorem verify_other {key nonce signed checked : Bytes} (differ : checked ≠ signed) :
    Signature.verify (Signature.vk key) checked (Signature.sign key nonce signed) = false := by
  simp only [Signature.verify, Signature.vk, Signature.sign]
  grind

/-! ## Transcripts are told apart -/

theorem be_inj {a b : Std.U64}
    (h : (Aeneas.Std.core.num.U64.to_be_bytes a).to_slice =
      (Aeneas.Std.core.num.U64.to_be_bytes b).to_slice) : a = b := by
  have vals := congrArg Slice.val h
  simp only [Aeneas.Std.core.num.U64.to_be_bytes, Array.to_slice, Slice.from_val,
    Array.from_val] at vals
  have bytes : a.bv.toBEBytes = b.bv.toBEBytes :=
    List.map_injective_iff.mpr (fun x y same => by cases same; rfl) vals
  have little : a.bv.toLEBytes = b.bv.toLEBytes := List.reverse_injective bytes
  have back (x : Std.U64) : (BitVec.fromLEBytes x.bv.toLEBytes).toNat = x.bv.toNat := by
    rw [BitVec.fromLEBytes_toLEBytes (by rfl)]
    simp
  have nat : a.bv.toNat = b.bv.toNat := by rw [← back a, ← back b, little]
  cases a
  cases b
  simp only [UScalar.mk.injEq]
  exact BitVec.eq_of_toNat_eq nat

theorem stamp_inj {a b : Std.U64} (h : stamp a = stamp b) : a = b :=
  be_inj (part_bytes_inj h)

theorem stamp_length (time : Std.U64) : (stamp time).length = 8 := by
  simp [stamp, Literal.length_literalToBytes, toByteArray, ByteArray.size]

theorem start_inj {a b : ByteArray} (h : start a = start b) : a = b := by
  have := congrArg (Literal.bytesToLiteral (Bytes := Bytes)) (Hash.hash_inj _ _ h)
  simpa only [Literal.bytesToLiteral_literalToBytes, Option.some.injEq] using this

/-- A starting transcript is not a starting transcript with a timestamp and one more part
committed: they differ in length. -/
theorem start_ne_extended (a b : ByteArray) (time : Std.U64) (rest : Bytes) :
    start a ≠ Concat.concat (Concat.concat (start b) (stamp time)) rest := by
  intro h
  have := congrArg Bytes.length h
  simp only [start, Hash.length_hash, Concat.length_concat, stamp_length] at this
  omega

/-- The transcript that a dialer signs fixes its opening. -/
theorem Opening.signed_inj {o o' : Opening} (h : o.signed = o'.signed) : o = o' := by
  obtain ⟨ns, dialer, listener, dialed, dialerKey⟩ := o
  obtain ⟨ns', dialer', listener', dialed', dialerKey'⟩ := o'
  simp only [Opening.signed] at h
  obtain ⟨h₁, key⟩ := concat_inj h
  obtain ⟨h₂, dialers⟩ := concat_inj h₁
  obtain ⟨h₃, listeners⟩ := concat_inj h₂
  obtain ⟨starts, times⟩ := concat_inj h₃
  rw [start_inj starts, stamp_inj times, key, dialers, listeners]

/-- The transcript that a listener signs fixes its exchange. -/
theorem Exchange.signed_inj {e e' : Exchange} (h : e.signed = e'.signed) : e = e' := by
  obtain ⟨o, answered, listenerKey⟩ := e
  obtain ⟨o', answered', listenerKey'⟩ := e'
  simp only [Exchange.signed] at h
  obtain ⟨h₁, key⟩ := concat_inj h
  obtain ⟨openings, times⟩ := concat_inj h₁
  rw [Opening.signed_inj openings, stamp_inj times, key]

/-- No transcript is signed both by a dialer and by a listener. -/
theorem Opening.signed_ne (o : Opening) (e : Exchange) : o.signed ≠ e.signed := by
  intro h
  simp only [Opening.signed, Exchange.signed] at h
  obtain ⟨h₁, -⟩ := concat_inj h
  obtain ⟨h₂, -⟩ := concat_inj h₁
  obtain ⟨h₃, -⟩ := concat_inj h₂
  obtain ⟨h₄, -⟩ := concat_inj h₃
  exact start_ne_extended _ _ _ _ h₄

end
end Sake
