import UnconditionalCounterexample.Hierarchy.IntegerValued
import UnconditionalCounterexample.Variations.OneCentre
import UnconditionalCounterexample.PaperSpectrum
import UnconditionalCounterexample.PaperSquareChainActual

/-! # The original domain separates weak ACCP from ACCP inside the overring class. -/

namespace UnconditionalCounterexample.Hierarchy

theorem originalWeakACCPWitness :
    intZInK ≤ PaperConstruction.domain ∧ IsAlmostDedekindDomain PaperConstruction.domain ∧
    Factorization.IsWeakACCP PaperConstruction.domain ∧ ¬ WfDvdMonoid PaperConstruction.domain :=
  ⟨intZInK_le_pairedDomain _ _, PaperConstruction.isAlmostDedekindDomain,
    PaperConstruction.weakACCP, PaperConstruction.not_wfDvdMonoid⟩

end UnconditionalCounterexample.Hierarchy
