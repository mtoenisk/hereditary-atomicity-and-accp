import HereditaryAtomicity.ValuationPolynomial
import HereditaryAtomicity.ConductorBranches
import HereditaryAtomicity.BranchProfiles
import HereditaryAtomicity.ArithmeticDVR
import Mathlib.Topology.LocallyConstant.Basic

/-! Finite ranges of actual normalized arithmetic valuation profiles. -/

noncomputable section
namespace HereditaryAtomicity
open scoped NNReal

variable {K : Type*} [Field K]

/-- Algebraicity over a literal DVR makes the normalized order of each nonzero
fraction range over a finite set, for an arbitrary family of containing branches. -/
theorem finite_range_normalized_dvr_orders
    (A : Subring K) [IsDiscreteValuationRing A] [Algebra.IsAlgebraic A K]
    {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (hv : ∀ (i : ι) (a : A), v i (a : K) ≤ 1)
    (π : A) (hπ : Irreducible π)
    (hnorm : ∀ i, realValuationOrder (v i) (π : K) = 1)
    (x : K) (hx : x ≠ 0) :
    Set.Finite (Set.range (fun i => realValuationOrder (v i) x)) := by
  classical
  obtain ⟨p, hp, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := A) x
  have hexp : ∀ j : p.support, ∃ n : ℕ, ∀ i,
      realValuationOrder (v i) (p.coeff j : K) = n := by
    intro j
    exact normalized_dvr_coefficient_orders A.subtype v hv hπ hnorm
      (Polynomial.mem_support_iff.mp j.property)
  choose n hn using hexp
  let slopes : (p.support × p.support) → ℝ := fun q =>
    ((n q.2 : ℝ) - n q.1) / ((q.1.val : ℝ) - q.2.val)
  apply (Set.finite_range slopes).subset
  rintro y ⟨i, rfl⟩
  obtain ⟨a, ha, b, hb, hab, heq, _⟩ :=
    polynomial_exists_maximal_valuation_tie A.subtype Subtype.val_injective (v i)
      p hp x hx hpx
  refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
  have ha0 : (p.coeff a : K) ≠ 0 := Subtype.coe_ne_coe.mpr
    (Polynomial.mem_support_iff.mp ha)
  have hb0 : (p.coeff b : K) ≠ 0 := Subtype.coe_ne_coe.mpr
    (Polynomial.mem_support_iff.mp hb)
  have ho : realValuationOrder (v i) ((p.coeff a : K)*x^a) =
      realValuationOrder (v i) ((p.coeff b : K)*x^b) := by
    exact congrArg (fun z : ℝ≥0 => -Real.log (z : ℝ)) heq
  rw [realValuationOrder_mul _ ha0 (pow_ne_zero _ hx),
    realValuationOrder_mul _ hb0 (pow_ne_zero _ hx),
    realValuationOrder_pow, realValuationOrder_pow, hn ⟨a, ha⟩ i, hn ⟨b, hb⟩ i] at ho
  have hab' : (a : ℝ) - b ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_lt hab)
  dsimp [slopes]
  apply (div_eq_iff hab').mpr
  nlinarith

/-- A bounded conductor profile yields a uniformizer power in the conductor,
without a finite branch-count assumption. -/
theorem exists_uniformizer_power_conductor_of_bddAbove
    {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (B C : Subring K) (hB : ∀ x : K, x ∈ B ↔ ∀ i, v i x ≤ 1)
    {π d : K} (hπ0 : π ≠ 0) (hd0 : d ≠ 0)
    (hπ : ∀ i, realValuationOrder (v i) π = 1)
    (hbdd : BddAbove (Set.range (fun i => realValuationOrder (v i) d)))
    (hd : ∀ b : B, d * (b : K) ∈ C) :
    ∃ n : ℕ, 0 < n ∧ ∀ b : B, π^n * (b : K) ∈ C := by
  obtain ⟨b, hb⟩ := hbdd
  obtain ⟨n, hn⟩ := exists_nat_gt (max b 0)
  have hn0 : 0 < n := by
    have hnpos : (0 : ℝ) < n := (le_max_right _ _).trans_lt hn
    exact_mod_cast hnpos
  have hquot : π^n / d ∈ B := by
    apply (hB _).mpr
    intro i
    apply (realValuationOrder_nonneg_iff (v i) (div_ne_zero (pow_ne_zero _ hπ0) hd0)).mp
    rw [realValuationOrder_div _ (pow_ne_zero _ hπ0) hd0,
      realValuationOrder_pow, hπ i, mul_one]
    have hi := hb (Set.mem_range_self i)
    linarith [le_max_left b 0]
  refine ⟨n, hn0, fun z => ?_⟩
  have h := hd (⟨π^n/d, hquot⟩ * z)
  convert h using 1
  change π^n * (z : K) = d * ((π^n/d) * (z : K))
  field_simp

/-- Finite order ranges on the actual maximal branches of a Prüfer domain,
normalized at a uniformizer of a contained arithmetic DVR. -/
theorem finite_range_branchProfile_of_dvr
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (t : B) (ht0 : t ≠ 0) (htJ : t ∈ Ideal.jacobson (⊥ : Ideal B))
    (A : Subring K) [IsDiscreteValuationRing A] [Algebra.IsAlgebraic A K]
    (hAB : A ≤ B) (π : A) (hπ : Irreducible π) (hπt : (π : K) = t)
    {x : K} (hx : x ≠ 0) :
    Set.Finite (Set.range (branchProfile B hB hfield t ht0 htJ x)) := by
  apply finite_range_normalized_dvr_orders A
    (normalizedPrueferValuation B hB hfield t ht0 htJ) _ π hπ _ x hx
  · intro P a
    apply (normalizeRealValuation_le_one_iff _ _ _ _).mpr
    exact (mem_pruefer_iff_realValuations_le_one B hB hfield _).mp (hAB a.property) P
  · intro P
    rw [hπt]
    exact realValuationOrder_normalize_self _ _ _

/-- A continuous map into a T1 space with finite range is locally constant. -/
theorem locallyConstant_of_continuous_finite_range
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (f : X → Y) (hf : Continuous f) (hfin : Set.Finite (Set.range f)) :
    IsLocallyConstant f := by
  let : Finite (Set.range f) := hfin.to_subtype
  let g : X → Set.range f := fun x => ⟨f x, Set.mem_range_self x⟩
  have hg : Continuous g := hf.subtype_mk (fun x => Set.mem_range_self x)
  exact ((IsLocallyConstant.iff_continuous g).mpr hg).comp Subtype.val

/-- Arithmetic profiles are locally constant on the actual Zariski maximal
spectrum, not merely functions on an assumed finite quotient of the branches. -/
theorem isLocallyConstant_branchProfile_of_dvr
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (t : B) (ht0 : t ≠ 0) (htJ : t ∈ Ideal.jacobson (⊥ : Ideal B))
    (A : Subring K) [IsDiscreteValuationRing A] [Algebra.IsAlgebraic A K]
    (hAB : A ≤ B) (π : A) (hπ : Irreducible π) (hπt : (π : K) = t)
    {x : K} (hx : x ≠ 0) :
    IsLocallyConstant (branchProfile B hB hfield t ht0 htJ x) :=
  locallyConstant_of_continuous_finite_range _
    (continuous_branchProfile B hB hfield t ht0 htJ hx)
    (finite_range_branchProfile_of_dvr B hB hfield t ht0 htJ A hAB π hπ hπt hx)

end HereditaryAtomicity
