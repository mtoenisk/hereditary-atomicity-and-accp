import UnconditionalCounterexample.SparseIntegerConductor
import UnconditionalCounterexample.SingleTensorConductor

/-!
# Local conductor applications for original sparse-domain subrings

The original intersection supplies all value bounds and denominator survival.
Only the actual extracted fraction sequence, its fixed exponent bound, rational
hull, and the mixed constructor's derivative/transfer estimates remain inputs.
Both cases use the same canonical inclusion and ordinary tensor image.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseLocalConductor

open Polynomial Filter SparsePrimaryDomain SparseDomainValues GuardSupport
open RadicalConductor SparseIntegerConductor LocalAlgebra

variable (S : Set ℚ[X]) (hS : ∀ f ∈ S, f ≠ 0) (d : Places)

theorem pair_of_extracted_words (T : Subring (domain S d))
    (hhull : RationalHull.hull (T.map (inclusion S d)) = ⊤)
    (j : ℕ) (hdiff : IsUnit (d.guard (d.primes j) - d.primary j))
    (y : ℕ → T.map (inclusion S d)) (F H : ℕ → ℚ[X]) (m stage : ℕ → ℕ) (R : ℕ)
    (hH : ∀ i, H i ≠ 0)
    (hword : ∀ i, ((y i : poleAlgebra S) : RatFunc ℚ) =
      algebraMap ℚ[X] (RatFunc ℚ) (F i) ^ m i / algebraMap ℚ[X] (RatFunc ℚ) (H i))
    (hstage : Tendsto stage atTop atTop) (hm : ∀ᶠ i in atTop, m i ≤ R)
    (hda : ∀ᶠ i in atTop,
      (LocalInterpolation.wordDerivative ((F i).map (algebraMap ℚ ℚ_[(d.primes j).val]))
        ((H i).map (algebraMap ℚ ℚ_[(d.primes j).val])) (m i) (d.primary j).val).valuation < -(stage i : ℤ))
    (hdb : ∀ᶠ i in atTop,
      (LocalInterpolation.wordDerivative ((F i).map (algebraMap ℚ ℚ_[(d.primes j).val]))
        ((H i).map (algebraMap ℚ ℚ_[(d.primes j).val])) (m i) (d.guard (d.primes j)).val).valuation < -(stage i : ℤ))
    (htransfer : ∀ s : ℕ, ∀ᶠ i in atTop,
      ∃ u v : padicScaledPolynomialRing (d.primes j).val s,
        (RatFunc.C ((d.primes j).val : ℚ_[(d.primes j).val]) ^ (2 * s) *
          ((RatFunc.X - RatFunc.C (d.primary j).val) *
            (RatFunc.X - RatFunc.C (d.guard (d.primes j)).val))) ^ m i =
        RatFunc.C ((d.primes j).val : ℚ_[(d.primes j).val]) ^ stage i *
          ((u : RatFunc ℚ_[(d.primes j).val]) + (v : RatFunc ℚ_[(d.primes j).val]) *
            (((F i).map (algebraMap ℚ ℚ_[(d.primes j).val]) : RatFunc ℚ_[(d.primes j).val]) ^ m i /
              ((H i).map (algebraMap ℚ ℚ_[(d.primes j).val]) : RatFunc ℚ_[(d.primes j).val])))) :
    conductorIdeal (localImage S hS d (d.primes j) T) = Ideal.span
      {algebraMap ℚ_[(d.primes j).val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[(d.primes j).val] S))
        ((X - C (d.primary j).val) * (X - C (d.guard (d.primes j)).val))} := by
  have hretained {p : ℕ} [Fact p.Prime] (a : ℚ_[p]) (ha : Transcendental ℚ a)
      (f : ℚ[X]) (hf : f ≠ 0) : f.eval₂ (algebraMap ℚ ℚ_[p]) a ≠ 0 :=
    mt ((transcendental_iff.mp ha) f) hf
  have hab : (d.primary j).val ≠ (d.guard (d.primes j)).val := by
    intro he
    have he' : d.primary j = d.guard (d.primes j) := Subtype.ext he
    simp [he'] at hdiff
  exact PoleTensorConductor.conductor_eq_pair_of_extracted_words (d.primes j).val S hS
    (T.map (inclusion S d)) (domainInPole S d) (mapped_subring_le S d T) hhull
    (d.primary j).val (d.guard (d.primes j)).val hab (d.primary j).property (d.guard (d.primes j)).property
    (fun f hf => hretained _ (d.primary_trans j) f (hS f hf))
    (fun f hf => hretained _ (d.guard_trans (d.primes j)) f (hS f hf))
    (primary_norm_eval_le_one_inPole S d j) (guard_norm_eval_le_one_inPole S d (d.primes j))
    y F H m stage R
    (fun i => hretained _ (d.primary_trans j) (H i) (hH i))
    (fun i => hretained _ (d.guard_trans (d.primes j)) (H i) (hH i))
    hword hstage hm hda hdb htransfer

theorem single_of_extracted_words (T : Subring (domain S d))
    (hhull : RationalHull.hull (T.map (inclusion S d)) = ⊤) (p : PrimeIndex)
    (y : ℕ → T.map (inclusion S d)) (F H : ℕ → ℚ[X]) (m stage : ℕ → ℕ) (R : ℕ)
    (hH : ∀ i, H i ≠ 0)
    (hword : ∀ i, ((y i : poleAlgebra S) : RatFunc ℚ) =
      algebraMap ℚ[X] (RatFunc ℚ) (F i) ^ m i / algebraMap ℚ[X] (RatFunc ℚ) (H i))
    (hstage : Tendsto stage atTop atTop) (hm : ∀ᶠ i in atTop, m i ≤ R)
    (hdb : ∀ᶠ i in atTop,
      (LocalInterpolation.wordDerivative ((F i).map (algebraMap ℚ ℚ_[p.val]))
        ((H i).map (algebraMap ℚ ℚ_[p.val])) (m i) (d.guard p).val).valuation < -(stage i : ℤ))
    (htransfer : ∀ s : ℕ, ∀ᶠ i in atTop,
      ∃ u v : padicScaledPolynomialRing p.val s,
        (RatFunc.C (p.val : ℚ_[p.val]) ^ (2 * s) * (RatFunc.X - RatFunc.C (d.guard p).val)) ^ m i =
        RatFunc.C (p.val : ℚ_[p.val]) ^ stage i * ((u : RatFunc ℚ_[p.val]) + (v : RatFunc ℚ_[p.val]) *
          (((F i).map (algebraMap ℚ ℚ_[p.val]) : RatFunc ℚ_[p.val]) ^ m i /
            ((H i).map (algebraMap ℚ ℚ_[p.val]) : RatFunc ℚ_[p.val])))) :
    conductorIdeal (localImage S hS d p T) = Ideal.span
      {algebraMap ℚ_[p.val][X] (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p.val] S))
        (X - C (d.guard p).val)} := by
  have hretained (f : ℚ[X]) (hf : f ≠ 0) :
      f.eval₂ (algebraMap ℚ ℚ_[p.val]) (d.guard p).val ≠ 0 :=
    mt ((transcendental_iff.mp (d.guard_trans p)) f) hf
  exact SingleTensorConductor.conductor_eq_single_of_extracted_words p.val S hS
    (T.map (inclusion S d)) (domainInPole S d) (mapped_subring_le S d T) hhull
    (d.guard p).val (d.guard p).property (fun f hf => hretained f (hS f hf))
    (guard_norm_eval_le_one_inPole S d p) y F H m stage R (fun i => hretained (H i) (hH i))
    hword hstage hm hdb htransfer

end UnconditionalCounterexample.SparseLocalConductor
