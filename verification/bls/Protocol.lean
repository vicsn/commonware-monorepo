module
public import BlsRouting.Examples
public import DY.Actions.ProtocolEvent
import all DY.Actions.ProtocolEvent
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation

namespace BLS.Protocol
open DY Routing
@[expose] public section

inductive Event where
  | sign (id : Nat) (domain message : Routing.Bytes)
  | compromise (id : Nat)
  | accept (call : Call)

instance : ExecTraceTypes := ⟨ProtocolEvent.ExecEntryT Event⟩
instance : ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Event) where
  inj := id
  proj := some
  inj_proj_eq := by intro x y; exact propext Option.some_inj

abbrev Signed (tr : ExecTrace) (i d m) := tr.EventLogged (Event.sign i d m)
abbrev Leaked (tr : ExecTrace) (i) := tr.EventLogged (Event.compromise i)

def allowed (v : bls_routing.Variant Unit (List Nat) Point) (keys : Nat → Key)
    (tr : ExecTrace) : Event → Prop
  | .sign .. | .compromise .. => True
  | .accept c =>
    (∀ a ∈ claims c.args.1 c.args.2,
      Derives (Signed tr) (Leaked tr) (term (keys a.1) (.possession (keys a.1)))) ∧
    ∃ s, Derives (Signed tr) (Leaked tr) s ∧ c.run v s = .ok (.Ok ())

def protocol (v : bls_routing.Variant Unit (List Nat) Point) (keys : Nat → Key) :
    ReachabilityConfig where
  Input := Event
  PreCond e tr := allowed v keys tr e
  step e := ⟨Unit, ProtocolEvent.logEvent e⟩

private theorem acceptance_guard {tr : ExecTrace} (r : tr.Reachable (protocol v keys))
    (t : Nat) (c : Call) (ev : tr.EventLoggedAt (Event.accept c) t) :
    allowed v keys (tr.prefix t) (.accept c) := by
  induction r with
  | Base => have := Trace.EventLoggedAt_implies_i_le_length _ _ _ ev; simp [Trace.empty, Trace.length] at this
  | @Step tr e pre _ ih =>
    change Event at e
    let entry := ProtocolEvent.ExecEntryT.mk e
    change (tr.append entry).EventLoggedAt _ t at ev
    change allowed v keys ((tr.append entry).prefix t) _
    have lt := Trace.EventLoggedAt_implies_i_le_length _ _ _ ev
    rw [Trace.append_length] at lt
    by_cases eq : t = tr.length
    · subst t
      have atEnd := Trace.at?_append tr entry
      unfold Trace.EventLoggedAt at ev
      rw [atEnd] at ev
      have same : e = Event.accept c := by simpa [entry] using ev
      rw [Trace.append_prefix _ _ _ (by omega), Trace.prefix_length_eq_self]
      exact same ▸ pre
    · rw [Trace.append_prefix _ _ _ (by omega)]
      exact ih (Trace.EventLoggedAt_le' _ _ tr _ (by omega) (Trace.append_le tr entry) ev)

theorem prior_sign {c : Call} {tr : ExecTrace} (b : Backend v keys c.args.2) (reach : tr.Reachable (protocol v keys))
    (accept : tr.EventLoggedAt (Event.accept c) t)
    (canon : keys h = basis h) (uniq : ∀ i, keys i = basis h → i = h)
    (safe : ¬ Leaked (tr.prefix t) h) (member : (h,d,m) ∈ claims c.args.1 c.args.2) :
    ∃ before < t, tr.EventLoggedAt (Event.sign h d m) before := by
  obtain ⟨pop,s,der,ok⟩ := acceptance_guard reach t c accept
  obtain ⟨i, ev⟩ := signer_attribution c b s ok der canon uniq pop safe member
  have lt := Trace.EventLoggedAt_implies_i_le_length _ _ _ ev
  rw [Trace.prefix_length] at lt
  exact ⟨i, by omega, Trace.EventLoggedAt_le _ _ _ _ (Trace.prefix_le_self ..) ev⟩

/-- After any reachable prefix containing the signing events, the adversary
    can submit the honest aggregate and the verifier records acceptance. -/
theorem honest_aggregate {tr : ExecTrace} (ids : List Nat) (d m : Routing.Bytes)
    (r : tr.Reachable (protocol (Examples.variant d m) basis))
    (hist : ∀ i ∈ ids, Signed tr i d m) :
    (tr.append (ProtocolEvent.ExecEntryT.mk (Event.accept (.sameMessage ids d m)))).Reachable
      (protocol (Examples.variant d m) basis) := by
  refine Trace.Reachable.Step (config := protocol (Examples.variant d m) basis)
    (Event.accept (.sameMessage ids d m)) ?_ r
  exact ⟨fun c _ => Derives.pop c.1, _, Examples.aggregate_available ids d m hist,
    Examples.aggregate_accepts ids d m⟩

#print axioms prior_sign
end
end BLS.Protocol
