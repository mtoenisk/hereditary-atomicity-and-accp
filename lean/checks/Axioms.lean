import Factorization
import HereditaryAtomicity
import UnconditionalCounterexample
import Lean

/-! Check the transitive axioms of declarations introduced by the three libraries.
Checking the defining module also covers private and out-of-namespace declarations. -/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let libraries := #[`Factorization, `HereditaryAtomicity, `UnconditionalCounterexample]
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    if libraries.any (fun lib => lib.isPrefixOf env.header.moduleNames[idx]!) then
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
      checked := checked + 1
  if checked == 0 then throwError "No library declarations were checked"
  logInfo m!"Transitive axiom audit passed for {checked} library declarations."
