import HereditaryAtomicity.DiscreteDetectors
import Factorization.Descent
import Factorization.DescentACCP
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Actual outside valuation detectors for subring factorizations

The valuation witness is obtained by dominating a maximal ideal of the source
subring, directly inside the ambient field. Its existence does not assume that
the source has the whole ambient fraction field.
-/

namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- A source nonunit which is an ambient unit has a detecting outside valuation. -/
theorem exists_outside_valuation_nonunit {S D : Subring K} (hSD : S ≤ D)
    (a : S) (ha : ¬ IsUnit a) (hDa : IsUnit (Subring.inclusion hSD a)) :
    ∃ W : ValuationSubring K, S ≤ W.toSubring ∧ ¬ D ≤ W.toSubring ∧
      (a : K) ∈ W.nonunits := by
  obtain ⟨W, hSW, hW⟩ := Ideal.image_subset_nonunits_valuationSubring
    (Ideal.span ({a} : Set S)) (fun h => ha (Ideal.span_singleton_eq_top.mp h))
  have haW : (a : K) ∈ W.nonunits := hW ⟨a, Ideal.subset_span rfl, rfl⟩
  refine ⟨W, hSW, ?_, haW⟩
  intro hDW
  have hu : IsUnit (⟨(a : K), hSW a.property⟩ : W) :=
    hDa.map (Subring.inclusion hDW)
  have hnu : ¬ IsUnit (⟨(a : K), hSW a.property⟩ : W) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using
      (W.coe_mem_nonunits_iff (a := ⟨(a : K), hSW a.property⟩)).mp haW
  exact hnu hu

/-- The positive support at outside valuation rings. -/
def positiveOutsideSupport (D : Subring K) (z : K) : Set (ValuationSubring K) :=
  {W | ¬ D ≤ W.toSubring ∧ z ∈ W.nonunits}

/-- Finitely many actual outside DVRs give a bound depending only on the fixed
ambient element, uniformly over every embedded subring. -/
theorem exists_uniform_ambientUnitFactorBound_of_finite_discrete_outside
    (D : Subring K)
    (hDVR : ∀ W : ValuationSubring K, ¬ D ≤ W.toSubring → IsDiscreteValuationRing W)
    (z : K) (hz : z ≠ 0) (hfinite : (positiveOutsideSupport D z).Finite) :
    ∃ bound : ℕ, ∀ (S : Subring K) (hSD : S ≤ D) (x : S), (x : K) = z →
      ∀ t : Multiset S, (∀ a ∈ t, ¬ IsUnit a) → Associated t.prod x →
        Factorization.ambientUnitFactorCount (Subring.inclusion hSD).toMonoidHom t ≤ bound := by
  classical
  let ι := positiveOutsideSupport D z
  let : Fintype ι := hfinite.fintype
  let (W : ι) : IsDiscreteValuationRing W.val := hDVR W.val W.property.1
  let bound : ℕ := ∑ W : ι,
    discreteOrder (⟨z, W.val.nonunits_subset W.property.2⟩ : W.val)
  refine ⟨bound, ?_⟩
  intro S hSD x hxz t ht hprod
  have hx : x ≠ 0 := fun h => hz (hxz.symm.trans (congrArg Subtype.val h))
  let weight (W : ι) (a : S) : ℕ :=
    if hSW : S ≤ W.val.toSubring then
      discreteOrder (⟨(a : K), hSW a.property⟩ : W.val)
    else 0
  have hunit : ∀ W ∈ (Finset.univ : Finset ι), ∀ a : S, IsUnit a → weight W a = 0 := by
    intro W _ a ha
    dsimp [weight]
    split_ifs with hSW
    · exact discreteOrder_eq_zero_of_isUnit (ha.map (Subring.inclusion hSW))
    · rfl
  have hmul : ∀ W ∈ (Finset.univ : Finset ι), ∀ a b : S, a ≠ 0 → b ≠ 0 →
      weight W (a * b) = weight W a + weight W b := by
    intro W _ a b ha hb
    dsimp [weight]
    split_ifs with hSW
    · exact discreteOrder_mul (x := (⟨(a : K), hSW a.property⟩ : W.val))
        (y := (⟨(b : K), hSW b.property⟩ : W.val))
        (fun h => ha (Subtype.ext (congrArg (fun r : W.val => (r : K)) h)))
        (fun h => hb (Subtype.ext (congrArg (fun r : W.val => (r : K)) h)))
    · rfl
  have hdetect : ∀ a ∈ t, IsUnit (Subring.inclusion hSD a) →
      ∃ W ∈ (Finset.univ : Finset ι), 0 < weight W a := by
    intro a hat haD
    obtain ⟨W, hSW, hDW, haW⟩ := exists_outside_valuation_nonunit hSD a (ht a hat) haD
    have hdvd : a ∣ x := (Multiset.dvd_prod hat).trans hprod.dvd
    have ha0 : a ≠ 0 := ne_zero_of_dvd_ne_zero hx hdvd
    have hnu : ¬ IsUnit (⟨(a : K), hSW a.property⟩ : W) := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using
        (W.coe_mem_nonunits_iff (a := ⟨(a : K), hSW a.property⟩)).mp haW
    have hxnu : ¬ IsUnit (Subring.inclusion hSW x) := by
      intro hu
      obtain ⟨b, hab⟩ := hdvd
      rw [hab, map_mul] at hu
      exact hnu (isUnit_of_mul_isUnit_left hu)
    have hzW : z ∈ W.nonunits := by
      rw [← hxz]
      exact W.coe_mem_nonunits_iff.mpr (by simpa only
        [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hxnu)
    let Wi : ι := ⟨W, hDW, hzW⟩
    have : IsDiscreteValuationRing W := hDVR W hDW
    refine ⟨Wi, Finset.mem_univ _, ?_⟩
    have hpos : 0 < discreteOrder (⟨(a : K), hSW a.property⟩ : W) :=
      discreteOrder_pos (x := (⟨(a : K), hSW a.property⟩ : W))
        (fun h => ha0 (Subtype.ext (congrArg (fun r : W => (r : K)) h))) hnu
    simpa only [weight, Wi, dite_eq_left hSW] using hpos
  have hcount := Factorization.filter_card_le_sum_nat_of_finite_detectors
    Finset.univ weight hunit hmul hx t hprod
    (fun a => IsUnit (Subring.inclusion hSD a)) hdetect
  apply hcount.trans
  apply Finset.sum_le_sum
  intro W _
  dsimp [weight]
  split_ifs with hSW
  · subst z
    exact le_rfl
  · exact Nat.zero_le _

end HereditaryAtomicity
