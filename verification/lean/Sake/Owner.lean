module
public import Sake.Protocol
import all DY.Trace.Basic
import all DY.Actions.ProtocolEvent
import all DY.Actions.PersistentGlobalState
import all DY.Actions.PersistentLocalState
import all DY.Actions.LongTermKeys
import DY.Meta

/-! An identity key has one owner. Checked.

DyLean's key registry gives the signing key of a participant a label that names the participant:
the label is corrupt on exactly the traces that hold a compromise of the key under that name. Two
names for one key therefore give two labels, and the labels differ on the trace that holds a
single compromise under the first name. This uses the bodies of DyLean's definitions of
compromise (`import all`), because DyLean exports them only through their monotonicity. -/

namespace Sake
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-- The names under which the registry labels one signing key are equal. -/
theorem owner_unique {first second : Participant} {key : Bytes}
    (same : LongTermKeys.label "SAKE PKI" first (Signature.vk key) =
      LongTermKeys.label "SAKE PKI" second (Signature.vk key)) :
    first = second := by
  let leak : PersistentGlobalState.Compromise.CompromiseEvent
      (PersistentLocalState.LocalState (LongTermKeys.SecretKeyState "SAKE PKI")) :=
    { state := { participant := first, state := { sk := key } } }
  let tr : ExecTrace := Trace.empty.append (ProtocolEvent.ExecEntryT.mk leak)
  have leaked : (LongTermKeys.label "SAKE PKI" first (Signature.vk key)).isCorrupt tr := by
    simp only [LongTermKeys.label, LongTermKeys.LongTermKeyCompromised,
      PersistentLocalState.LocalStateCompromised, PersistentGlobalState.GlobalStateCompromised,
      Trace.EventLogged, Trace.EventLoggedAt]
    exact ⟨key, rfl, 0, Trace.at?_append _ _⟩
  rw [same] at leaked
  simp only [LongTermKeys.label, LongTermKeys.LongTermKeyCompromised,
    PersistentLocalState.LocalStateCompromised, PersistentGlobalState.GlobalStateCompromised,
    Trace.EventLogged, Trace.EventLoggedAt] at leaked
  obtain ⟨key', -, time, logged⟩ := leaked
  have bound : time < tr.length := by
    have := Trace.at?_eq_some_implies_length_le tr time
      (EntryT := ProtocolEvent.ExecEntryT (PersistentGlobalState.Compromise.CompromiseEvent
        (PersistentLocalState.LocalState (LongTermKeys.SecretKeyState "SAKE PKI"))))
    simp only [logged] at this
    exact this
  have one : tr.length = 1 := Trace.append_length (Trace.empty : ExecTrace) _
  obtain rfl : time = 0 := by omega
  have held : tr.at? 0 = some (ProtocolEvent.ExecEntryT.mk leak) :=
    Trace.at?_append (Trace.empty : ExecTrace) (ProtocolEvent.ExecEntryT.mk leak)
  rw [held] at logged
  have equal : first = second ∧ key = key' := by simpa [leak] using logged
  exact equal.1

end
end Sake
