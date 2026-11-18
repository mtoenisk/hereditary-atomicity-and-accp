import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Lemmas

import UnconditionalCounterexample.GenericRecovery

/-!
# Geometric recovery from literal raw-stage words

Specialize GenericRecovery to the construction's actual old-factor denominator.
Irreducibility and strictly increasing degree prove no cancellation with the
fresh numerator. Every positive predecessor exponent gives an actual finite
pole. Retained points make the entire old denominator nonzero, and stages
tending to infinity eventually include each selected raw polynomial.

The actual word identity, infinity degree inequalities and scheduled pair and
tangent inequalities remain explicit inputs; no desired rational hull equality
or canonical pole predicate is assumed.
-/

namespace UnconditionalCounterexample.WordGeometry

open Filter

open Polynomial
open scoped BigOperators

variable {k ι : Type*} [Field k]

/-- A fresh irreducible polynomial is coprime to every nonzero old polynomial
of strictly smaller degree. -/
theorem isCoprime_of_irreducible_of_natDegree_lt (F P : k[X])
    (hF : Irreducible F) (hP : P ≠ 0) (hdeg : P.natDegree < F.natDegree) :
    IsCoprime F P := by
  apply hF.coprime_iff_not_dvd.mpr
  intro hdiv
  exact (not_le_of_gt hdeg) (natDegree_le_of_dvd hdiv hP)

theorem fresh_pow_coprime_old_product (old : Finset ι) (P : ι → k[X])
    (F : k[X]) (d : ι → ℕ) (m : ℕ) (hF : Irreducible F)
    (hP : ∀ i ∈ old, P i ≠ 0)
    (hdeg : ∀ i ∈ old, (P i).natDegree < F.natDegree) :
    IsCoprime (F ^ m) (∏ i ∈ old, P i ^ d i) := by
  apply IsCoprime.prod_right
  intro i hi
  exact (isCoprime_of_irreducible_of_natDegree_lt F (P i) hF (hP i hi) (hdeg i hi)).pow

theorem old_factor_dvd_product (old : Finset ι) (P : ι → k[X]) (d : ι → ℕ)
    (j : ι) (hj : j ∈ old) (hd : 0 < d j) :
    P j ∣ ∏ i ∈ old, P i ^ d i := by
  exact (dvd_pow_self (P j) (Nat.ne_of_gt hd)).trans (Finset.dvd_prod_of_mem _ hj)

theorem old_product_ne_zero (old : Finset ι) (P : ι → k[X]) (d : ι → ℕ)
    (hP : ∀ i ∈ old, P i ≠ 0) :
    (∏ i ∈ old, P i ^ d i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero (d i) (hP i hi))

theorem eval_old_product_ne_zero {K : Type*} [Field K]
    [Algebra k K] (α : K) (old : Finset ι) (P : ι → k[X]) (d : ι → ℕ)
    (hP : ∀ i ∈ old, (P i).eval₂ (algebraMap k K) α ≠ 0) :
    (∏ i ∈ old, P i ^ d i).eval₂ (algebraMap k K) α ≠ 0 := by
  change (Polynomial.eval₂RingHom (algebraMap k K) α) _ ≠ 0
  rw [map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [map_pow]
  exact pow_ne_zero (d i) (hP i hi)




/-- Denominator of a literal listed word at raw stage n. -/
noncomputable def oldDenominator (P : ℕ → ℚ[X]) (n : ℕ) (d : ℕ → ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range n, P j ^ d j

/-- Increasing raw stages turn every fixed predecessor into an eventual
finite pole, while the scheduled polynomial tests produce all geometric data.
The only remaining source inputs are actual word membership/identity and the
construction's degree and pair/tangent inequalities. -/
theorem hull_eq_top_of_escaping_raw_words
    (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (P : ℕ → ℚ[X]) (hP : ∀ j, Irreducible (P j))
    (hdegreeP : StrictMono (fun j => (P j).natDegree))
    (α₀ : K) (hα₀ : ∀ j, (P j).eval₂ (algebraMap ℚ K) α₀ ≠ 0)
    (T : Subring (PoleAlgebra.generated (Set.range P))) (y : ℕ → T)
    (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (a : ℕ → ℕ) (ha : ∀ i, 0 < a i) (d : ℕ → ℕ → ℕ)
    (hd : ∀ i j, j < stage i → 0 < d i j)
    (hword : ∀ i, ((y i : PoleAlgebra.generated (Set.range P)) : RatFunc ℚ) =
      (algebraMap ℚ[X] (RatFunc ℚ) (P (stage i))) ^ a i /
        algebraMap ℚ[X] (RatFunc ℚ) (oldDenominator P (stage i) (d i)))
    (hinfinity : ∀ᶠ i in atTop,
      (oldDenominator P (stage i) (d i)).natDegree < a i * (P (stage i)).natDegree)
    (hpair : ∀ α β : K,
      (∀ j, (P j).eval₂ (algebraMap ℚ K) α ≠ 0) →
      (∀ j, (P j).eval₂ (algebraMap ℚ K) β ≠ 0) → α ≠ β → ∀ᶠ i in atTop,
        SeparationExclusions.Test.Holds ((P (stage i)).map (algebraMap ℚ K))
          (.pair α β (a i) ((oldDenominator P (stage i) (d i)).map (algebraMap ℚ K))))
    (htangent : ∀ α : K, (∀ j, (P j).eval₂ (algebraMap ℚ K) α ≠ 0) → ∀ᶠ i in atTop,
      SeparationExclusions.Test.Holds ((P (stage i)).map (algebraMap ℚ K))
        (.tangent α (a i) ((oldDenominator P (stage i) (d i)).map (algebraMap ℚ K)))) :
    RationalHull.hull T = ⊤ := by
  have hS : ∀ p ∈ Set.range P, p ≠ 0 := by
    rintro p ⟨j, rfl⟩
    exact (hP j).ne_zero
  have hzero : ∀ p ∈ Set.range P, p.eval₂ (algebraMap ℚ K) α₀ ≠ 0 := by
    rintro p ⟨j, rfl⟩
    exact hα₀ j
  have hden : ∀ i, oldDenominator P (stage i) (d i) ≠ 0 := by
    intro i
    exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hP j).ne_zero
  have heval : ∀ i α, (∀ j, (P j).eval₂ (algebraMap ℚ K) α ≠ 0) →
      (oldDenominator P (stage i) (d i)).eval₂ (algebraMap ℚ K) α ≠ 0 := by
    intro i α hα
    exact eval_old_product_ne_zero α (Finset.range (stage i)) P (d i) (fun j _ => hα j)
  apply GenericRecovery.hull_eq_top_of_eventually_tested_words K (Set.range P) hS α₀ hzero T y
    (fun i => P (stage i)) (fun i => oldDenominator P (stage i) (d i)) a hword
  · exact Filter.Eventually.of_forall (fun i => (hP (stage i)).ne_zero)
  · exact Filter.Eventually.of_forall hden
  · apply Filter.Eventually.of_forall
    intro i
    exact fresh_pow_coprime_old_product (Finset.range (stage i)) P (P (stage i)) (d i) (a i)
      (hP (stage i)) (fun j _ => (hP j).ne_zero)
      (fun j hj => hdegreeP (Finset.mem_range.mp hj))
  · rintro p ⟨j, rfl⟩
    filter_upwards [hstage.eventually (eventually_gt_atTop j)] with i hi
    exact old_factor_dvd_product (Finset.range (stage i)) P (d i) j
      (Finset.mem_range.mpr hi) (hd i j hi)
  · exact hinfinity
  · intro α β hα hβ hne
    have hα' : ∀ j, (P j).eval₂ (algebraMap ℚ K) α ≠ 0 := fun j => hα _ ⟨j, rfl⟩
    have hβ' : ∀ j, (P j).eval₂ (algebraMap ℚ K) β ≠ 0 := fun j => hβ _ ⟨j, rfl⟩
    filter_upwards [hpair α β hα' hβ' hne] with i hi
    refine ⟨⟨hne, ha i, ?_, ?_⟩, hi⟩
    · simpa only [eval_map] using heval i α hα'
    · simpa only [eval_map] using heval i β hβ'
  · intro α hα
    have hα' : ∀ j, (P j).eval₂ (algebraMap ℚ K) α ≠ 0 := fun j => hα _ ⟨j, rfl⟩
    filter_upwards [htangent α hα'] with i hi
    refine ⟨⟨ha i, ?_⟩, hi⟩
    simpa only [eval_map] using heval i α hα'

end UnconditionalCounterexample.WordGeometry
