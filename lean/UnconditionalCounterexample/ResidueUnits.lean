import UnconditionalCounterexample.PairedResidueCRT
import UnconditionalCounterexample.ConstructionReturns

namespace UnconditionalCounterexample.PairedResidues
noncomputable section
open Polynomial PairedDomain GuardSupport

variable (S : Set ℚ[X]) (d : Places)

theorem branchIntegerMap_isUnit (i : ℕ) (b : Bool) (x : domain S d)
    (hx : EvaluationDVR.valuation (d.primes i).val (evaluationBranch d i b) x = 1) :
    IsUnit (branchIntegerMap S d i b x) := by
  apply PadicInt.isUnit_iff.mpr
  change ‖evaluationBranch d i b x‖ = 1
  exact ConstructionReturns.norm_eq_one_of_mulValuation_eq_one _ hx

theorem pairResidue_isUnit (i h : ℕ) (x : domain S d)
    (hp : PairedDomain.vertical d (.inl i) x = 1)
    (hg : PairedDomain.vertical d (.inr (d.primes i)) x = 1) :
    IsUnit (pairResidue S d i h x) := by
  have hfalse : IsUnit (branchIntegerMap S d i false x) :=
    branchIntegerMap_isUnit S d i false x hp
  have htrue : IsUnit (branchIntegerMap S d i true x) :=
    branchIntegerMap_isUnit S d i true x hg
  exact Prod.isUnit_iff.mpr ⟨hfalse.map (PadicInt.toZModPow h), htrue.map (PadicInt.toZModPow h)⟩

theorem primePairResidue_isUnit (p : PrimeIndex) (h : ℕ) (x : domain S d)
    (hp : PairedDomain.vertical d (.inl (d.primes.symm p)) x = 1)
    (hg : PairedDomain.vertical d (.inr p) x = 1) :
    IsUnit (primePairResidue S d p h x) := by
  have hu := pairResidue_isUnit S d (d.primes.symm p) h x hp
    (by simpa only [d.primes.apply_symm_apply] using hg)
  exact hu.map (RingEquiv.prodCongr
    (ZMod.ringEquivCongr (congrArg (fun q : PrimeIndex => q.val ^ h) (d.primes.apply_symm_apply p)))
    (ZMod.ringEquivCongr (congrArg (fun q : PrimeIndex => q.val ^ h) (d.primes.apply_symm_apply p)))).toRingHom

theorem globalResidue_isUnit (n : ℕ) (hn : n ≠ 0) (x : domain S d)
    (h : ∀ p : n.primeFactors, IsUnit (primePairResidue S d
      ⟨p, Nat.prime_of_mem_primeFactors p.property⟩ (n.factorization p) x)) :
    IsUnit (globalResidue S d n hn x) := by
  apply Prod.isUnit_iff.mpr
  constructor
  · have hu : IsUnit (ZMod.equivPi n hn (globalResidue S d n hn x).1) := by
      apply Pi.isUnit_iff.mpr
      intro p
      rw [globalResidue_fst]
      exact (Prod.isUnit_iff.mp (h p)).1
    simpa using hu.map (ZMod.equivPi n hn).symm.toRingHom
  · have hu : IsUnit (ZMod.equivPi n hn (globalResidue S d n hn x).2) := by
      apply Pi.isUnit_iff.mpr
      intro p
      rw [globalResidue_snd]
      exact (Prod.isUnit_iff.mp (h p)).2
    simpa using hu.map (ZMod.equivPi n hn).symm.toRingHom

end
end UnconditionalCounterexample.PairedResidues
