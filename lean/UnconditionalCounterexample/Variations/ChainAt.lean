import Factorization.PrincipalChainAt
import UnconditionalCounterexample.Target

/-!
# Elementwise ACCP and the manuscript's principal-ideal chains
-/

namespace UnconditionalCounterexample

/-- A nonzero element fails elementwise ACCP exactly when the manuscript's
strict principal-ideal chain starts at that element. -/
theorem not_acc_dvdNotUnit_iff_hasStrictChainAt {R : Type*} [CommRing R] [IsDomain R]
    {x : R} (hx : x ≠ 0) : ¬ Acc DvdNotUnit x ↔ HasStrictChainAt x :=
  Factorization.not_acc_dvdNotUnit_iff_hasStrictPrincipalIdealChainAt hx

end UnconditionalCounterexample
