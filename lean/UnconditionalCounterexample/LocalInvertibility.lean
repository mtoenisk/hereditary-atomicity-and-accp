import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.FieldSimp

import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Invertibility from discrete valuation stalks

Every nonzero finitely generated fractional ideal is invertible if every
maximal localization is a discrete valuation ring. The permanent endpoint
`LocalInvertibility.fractional_isUnit_of_local_dvr` supplies the general
algebra used in manuscript §4.2; it allows any actual fraction field.

The proof constructs a local generator from the original ideal and clears
one denominator uniformly over its finite generators. Its product with the
actual fractional inverse then escapes every maximal ideal. The fractional
case uses the actual numerator ideal of a common denominator. No global
invertibility or Prüfer hypothesis is assumed. The stronger intermediate
`integral_isUnit_of_local_principal` only requires local principality of the
specified ideal.
-/

noncomputable section
namespace UnconditionalCounterexample.LocalIdealGenerators

variable {R S : Type*} [CommRing R] [CommRing S]
variable (M : Submonoid R) [Algebra R S] [IsLocalization M S]

include M in
theorem exists_generator_mem_of_map_principal (I : Ideal R)
    (hI : (I.map (algebraMap R S)).IsPrincipal) :
    ∃ a ∈ I, I.map (algebraMap R S) = Ideal.span {algebraMap R S a} := by
  let := hI
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (I.map (algebraMap R S))
  have hgm : g ∈ I.map (algebraMap R S) := by
    rw [hg]
    exact Ideal.subset_span (Set.mem_singleton g)
  obtain ⟨⟨a, s⟩, hgs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hgm
  refine ⟨a, a.property, le_antisymm ?_ ?_⟩
  · rw [hg]
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units S s)).mp
    rw [hgs]
    exact Ideal.subset_span (Set.mem_singleton _)
  · exact (Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_map_of_mem _ a.property)

theorem exists_uniform_denominator_of_map_le (I J : Ideal R) (hI : I.FG)
    (hIJ : I.map (algebraMap R S) ≤ J.map (algebraMap R S)) :
    ∃ s : M, ∀ x ∈ I, (s : R) * x ∈ J := by
  induction I, hI using Submodule.fg_induction with
  | singleton a =>
    have ha : algebraMap R S a ∈ J.map (algebraMap R S) :=
      hIJ (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton a)))
    obtain ⟨s, hs, hsa⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M S J a).mp ha
    refine ⟨⟨s, hs⟩, ?_⟩
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
    simpa only [Subtype.coe_mk, mul_assoc] using J.mul_mem_right r hsa
  | sup I₁ I₂ _ _ ih₁ ih₂ =>
    obtain ⟨s, hs⟩ := ih₁ ((Ideal.map_mono le_sup_left).trans hIJ)
    obtain ⟨t, ht⟩ := ih₂ ((Ideal.map_mono le_sup_right).trans hIJ)
    refine ⟨s * t, ?_⟩
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    simpa only [Submonoid.coe_mul, mul_add, mul_assoc, mul_left_comm] using
      J.add_mem (J.mul_mem_left (t : R) (hs y hy))
        (J.mul_mem_left (s : R) (ht z hz))

end UnconditionalCounterexample.LocalIdealGenerators


open scoped nonZeroDivisors
namespace UnconditionalCounterexample.LocalInvertibility

universe u v
variable {R : Type u} [CommRing R] [IsDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero local generator with one common denominator places that
common denominator in the product with the actual fractional inverse. -/
theorem multiplier_mem_product_inverse (I : Ideal R) (hI : I ≠ ⊥)
    {a s : R} (ha : a ∈ I) (ha0 : a ≠ 0)
    (hclear : ∀ x ∈ I, a ∣ s * x) :
    algebraMap R K s ∈ (I : FractionalIdeal R⁰ K) * (I : FractionalIdeal R⁰ K)⁻¹ := by
  have haK : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha0
  have hinv : algebraMap R K s / algebraMap R K a ∈ (I : FractionalIdeal R⁰ K)⁻¹ := by
    apply (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hI)).mpr
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hy
    obtain ⟨b, hb⟩ := hclear x hx
    apply (FractionalIdeal.mem_one_iff R⁰).mpr
    refine ⟨b, ?_⟩
    field_simp
    simpa only [map_mul, mul_comm] using congrArg (algebraMap R K) hb.symm
  have hmem := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_coeIdeal_of_mem R⁰ ha) hinv
  convert hmem using 1
  field_simp

/-- The local witnesses force the product with the fractional inverse to be
all of R, by testing every maximal ideal. -/
theorem isUnit_of_local_multipliers (I : Ideal R) (hI : I ≠ ⊥)
    (hlocal : ∀ M : Ideal R, M.IsMaximal →
      ∃ a ∈ I, a ≠ 0 ∧ ∃ s ∉ M, ∀ x ∈ I, a ∣ s * x) :
    IsUnit (I : FractionalIdeal R⁰ K) := by
  have hle : (I : FractionalIdeal R⁰ K) * (I : FractionalIdeal R⁰ K)⁻¹ ≤ 1 :=
    FractionalIdeal.mul_one_div_le_one
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have htop : J = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨a, ha, ha0, s, hs, hclear⟩ := hlocal M hM
    have hmem := multiplier_mem_product_inverse (K := K) I hI ha ha0 hclear
    rw [← hJ] at hmem
    obtain ⟨t, ht, heq⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hmem
    have hsJ : s ∈ J := (IsFractionRing.injective R K heq) ▸ ht
    exact hs (hJM hsJ)
  apply (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
  rw [← hJ, htop, FractionalIdeal.coeIdeal_top]

/-- Local principality at every maximal ideal suffices for invertibility of
an actual nonzero finitely generated integral ideal. -/
theorem integral_isUnit_of_local_principal (I : Ideal R) (hfg : I.FG) (hI : I ≠ ⊥)
    (hlocal : ∀ (M : Ideal R) [M.IsMaximal],
      (I.map (algebraMap R (Localization.AtPrime M))).IsPrincipal) :
    IsUnit (I : FractionalIdeal R⁰ K) := by
  apply isUnit_of_local_multipliers I hI
  intro M hM
  let := hM
  obtain ⟨a, ha, hgen⟩ := LocalIdealGenerators.exists_generator_mem_of_map_principal
    M.primeCompl I (hlocal M)
  have ha0 : a ≠ 0 := by
    intro h
    apply hI
    apply (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective R (Localization.AtPrime M))).mp
    simpa only [h, map_zero, Ideal.span_singleton_zero] using hgen
  have hle : I.map (algebraMap R (Localization.AtPrime M)) ≤
      (Ideal.span {a}).map (algebraMap R (Localization.AtPrime M)) := by
    simpa only [Ideal.map_span, Set.image_singleton] using hgen.le
  obtain ⟨s, hs⟩ := LocalIdealGenerators.exists_uniform_denominator_of_map_le M.primeCompl
    I (Ideal.span {a}) hfg hle
  exact ⟨a, ha, ha0, s, s.property, fun x hx => Ideal.mem_span_singleton.mp (hs x hx)⟩

/-- The DVR stalk hypothesis used for the constructed domain gives the
integral invertibility statement directly. -/
theorem integral_isUnit_of_local_dvr
    (hDVR : ∀ (M : Ideal R) [M.IsMaximal],
      IsDiscreteValuationRing (Localization.AtPrime M))
    (I : Ideal R) (hfg : I.FG) (hI : I ≠ ⊥) :
    IsUnit (I : FractionalIdeal R⁰ K) := by
  apply integral_isUnit_of_local_principal I hfg hI
  intro M hM
  let := hDVR M
  infer_instance

/-- The integral finitely generated case implies the fractional case by
using the actual numerator ideal of a common denominator. -/
theorem fractional_isUnit_of_integral (hintegral : ∀ I : Ideal R,
    I.FG → I ≠ ⊥ → IsUnit (I : FractionalIdeal R⁰ K))
    (I : FractionalIdeal R⁰ K) (hfg : (I : Submodule R K).FG) (hI : I ≠ 0) :
    IsUnit I := by
  have hnum0 : I.num ≠ ⊥ := fun h => hI
    (FractionalIdeal.zero_of_num_eq_bot (by simp) h)
  have hnumfg : I.num.FG := by
    apply (FractionalIdeal.coeIdeal_fg R⁰ (IsFractionRing.injective R K) I.num).mp
    rw [← FractionalIdeal.den_mul_self_eq_num' R⁰ K I, FractionalIdeal.coe_mul,
      FractionalIdeal.coe_spanSingleton]
    exact Submodule.FG.mul (Submodule.fg_span_singleton _) hfg
  have hunit := hintegral I.num hnumfg hnum0
  rw [← FractionalIdeal.den_mul_self_eq_num' R⁰ K I] at hunit
  exact isUnit_of_mul_isUnit_right hunit

/-- Every nonzero finitely generated fractional ideal is invertible when
all maximal localizations are discrete valuation rings. -/
theorem fractional_isUnit_of_local_dvr
    (hDVR : ∀ (M : Ideal R) [M.IsMaximal],
      IsDiscreteValuationRing (Localization.AtPrime M))
    (I : FractionalIdeal R⁰ K) (hfg : (I : Submodule R K).FG) (hI : I ≠ 0) :
    IsUnit I :=
  fractional_isUnit_of_integral (integral_isUnit_of_local_dvr hDVR) I hfg hI

end UnconditionalCounterexample.LocalInvertibility
