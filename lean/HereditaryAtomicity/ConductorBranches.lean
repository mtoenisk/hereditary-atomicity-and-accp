import HereditaryAtomicity.ArithmeticCoefficients
import HereditaryAtomicity.SparseProductCut
import HereditaryAtomicity.FiniteBranchCut
import Factorization.Transport
import HereditaryAtomicity.PrueferBranches
import HereditaryAtomicity.SemilocalDimension
import Factorization.BFInstances
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Factorization.Bounds

/-!
# Coefficients and conductor cutoffs for finitely many valuation branches

All ideals and inclusions below belong to literal subrings of the common field.
Rescaling a real valuation changes no containing ring or center.
-/

open scoped NNReal
noncomputable section
namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- Positive real rescaling of a multiplicative nonnegative-real valuation. -/
def scaleRealValuation (v : Valuation K ℝ≥0) (r : ℝ) (hr : 0 < r) :
    Valuation K ℝ≥0 :=
  v.map { NNReal.rpowMonoidHom r with map_zero' := NNReal.zero_rpow hr.ne' }
    (NNReal.monotone_rpow_of_nonneg hr.le)

@[simp] theorem scaleRealValuation_apply
    (v : Valuation K ℝ≥0) (r : ℝ) (hr : 0 < r) (x : K) :
    scaleRealValuation v r hr x = (v x) ^ r := rfl

theorem realValuationOrder_scale
    (v : Valuation K ℝ≥0) (r : ℝ) (hr : 0 < r) (x : K) :
    realValuationOrder (scaleRealValuation v r hr) x = r * realValuationOrder v x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : 0 < (v x : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx))
    simp only [realValuationOrder, scaleRealValuation_apply, NNReal.coe_rpow,
      Real.log_rpow hx', mul_neg]

theorem scaleRealValuation_le_one_iff
    (v : Valuation K ℝ≥0) (r : ℝ) (hr : 0 < r) (x : K) :
    scaleRealValuation v r hr x ≤ 1 ↔ v x ≤ 1 := by
  simpa only [scaleRealValuation_apply, NNReal.one_rpow] using
    (NNReal.rpow_le_rpow_iff (x := v x) (y := 1) hr)

/-- Normalize the additive order of one common positive element to one. -/
def normalizeRealValuation (v : Valuation K ℝ≥0) (π : K)
    (hπ : 0 < realValuationOrder v π) : Valuation K ℝ≥0 :=
  scaleRealValuation v (realValuationOrder v π)⁻¹ (inv_pos.mpr hπ)

@[simp] theorem realValuationOrder_normalize_self
    (v : Valuation K ℝ≥0) (π : K) (hπ : 0 < realValuationOrder v π) :
    realValuationOrder (normalizeRealValuation v π hπ) π = 1 := by
  rw [normalizeRealValuation, realValuationOrder_scale, inv_mul_cancel₀ hπ.ne']

theorem normalizeRealValuation_le_one_iff
    (v : Valuation K ℝ≥0) (π : K) (hπ : 0 < realValuationOrder v π) (x : K) :
    normalizeRealValuation v π hπ x ≤ 1 ↔ v x ≤ 1 :=
  scaleRealValuation_le_one_iff _ _ _ _

theorem realValuationOrder_normalize_pos_iff
    (v : Valuation K ℝ≥0) (π : K) (hπ : 0 < realValuationOrder v π) (x : K) :
    0 < realValuationOrder (normalizeRealValuation v π hπ) x ↔
      0 < realValuationOrder v x := by
  rw [normalizeRealValuation, realValuationOrder_scale]
  exact mul_pos_iff_of_pos_left (inv_pos.mpr hπ)

/-- Normalized DVR coefficients have one natural order at every branch. -/
theorem normalized_dvr_coefficient_orders
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {ι : Type*} (f : A →+* K) (v : ι → Valuation K ℝ≥0)
    (hv : ∀ i a, v i (f a) ≤ 1) {π a : A}
    (hπ : Irreducible π) (hnorm : ∀ i, realValuationOrder (v i) (f π) = 1)
    (ha : a ≠ 0) : ∃ n : ℕ, ∀ i, realValuationOrder (v i) (f a) = n := by
  obtain ⟨n, hn⟩ := dvr_coefficient_values f v hv hπ ha
  refine ⟨n, fun i => ?_⟩
  calc
    realValuationOrder (v i) (f a) = realValuationOrder (v i) ((f π)^n) := by
      simp only [realValuationOrder, map_pow, hn i]
    _ = n * realValuationOrder (v i) (f π) := realValuationOrder_pow _ _ _
    _ = n := by rw [hnorm i, mul_one]

/-- Every nonzero coefficient from a contained field has additive order zero. -/
theorem field_coefficient_order
    {k : Type*} [Field k] (f : k →+* K) (v : Valuation K ℝ≥0)
    (hv : ∀ a, v (f a) ≤ 1) {a : k} (ha : a ≠ 0) :
    realValuationOrder v (f a) = 0 := by
  simp only [realValuationOrder, field_coefficient_value f v hv ha, NNReal.coe_one,
    Real.log_one, neg_zero]

/-- In a normalized DVR coefficient ring, a nonzero coefficient has zero order
exactly when it is a coefficient unit. -/
theorem normalized_dvr_coefficient_order_zero_iff
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A →+* K) (hf : Function.Injective f) (v : Valuation K ℝ≥0)
    (hv : ∀ a, v (f a) ≤ 1) {π a : A}
    (hπ : Irreducible π) (hnorm : realValuationOrder v (f π) = 1) (ha : a ≠ 0) :
    realValuationOrder v (f a) = 0 ↔ IsUnit a := by
  constructor
  · intro hz
    obtain ⟨n, u, heq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hu : v (f (u : A)) = 1 := coefficient_unit_value f v hv u.isUnit
    have hn : (n : ℝ) = 0 := by
      rw [heq, map_mul, map_pow,
        realValuationOrder_mul v ((map_ne_zero_iff f hf).mpr u.ne_zero)
          (pow_ne_zero _ ((map_ne_zero_iff f hf).mpr hπ.ne_zero)),
        realValuationOrder_pow, hnorm, mul_one] at hz
      simpa only [realValuationOrder, hu, NNReal.coe_one, Real.log_one, neg_zero, zero_add] using hz
    have hn0 : n = 0 := by exact_mod_cast hn
    simp [heq, hn0]
  · intro hu
    simp only [realValuationOrder, coefficient_unit_value f v hv hu, NNReal.coe_one,
      Real.log_one, neg_zero]

/-- A normalized uniformizer power eventually lies inside any nonzero conductor ideal. -/
theorem exists_uniformizer_power_conductor
    {ι : Type*} [Fintype ι] (v : ι → Valuation K ℝ≥0)
    (B C : Subring K) (hB : ∀ x : K, x ∈ B ↔ ∀ i, v i x ≤ 1)
    {π d : K} (hπ0 : π ≠ 0) (hd0 : d ≠ 0)
    (hπ : ∀ i, realValuationOrder (v i) π = 1)
    (hd : ∀ b : B, d * (b : K) ∈ C) :
    ∃ n : ℕ, 0 < n ∧ ∀ b : B, π ^ n * (b : K) ∈ C := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (1 + ∑ i, |realValuationOrder (v i) d|)
  have hsum : ∀ i, realValuationOrder (v i) d ≤ ∑ j, |realValuationOrder (v j) d| := by
    intro i
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |realValuationOrder (v j) d|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hquot : π ^ n / d ∈ B := by
    apply (hB _).mpr
    intro i
    apply (realValuationOrder_nonneg_iff (v i) (div_ne_zero (pow_ne_zero _ hπ0) hd0)).mp
    rw [realValuationOrder_div _ (pow_ne_zero _ hπ0) hd0,
      realValuationOrder_pow, hπ i, mul_one]
    linarith [hsum i]
  refine ⟨n, hn0, fun b => ?_⟩
  have h := hd (⟨π ^ n / d, hquot⟩ * b)
  convert h using 1
  change π ^ n * (b : K) = d * ((π ^ n / d) * (b : K))
  field_simp

/-- A positive joint lower bound for finitely many containing valuations bounds
all nonunit factorizations in the source ring. -/
theorem isBFDomain_of_finite_valuation_floor
    {ι : Type*} [Fintype ι] (v : ι → Valuation K ℝ≥0) (C : Subring K)
    (hC : ∀ a : C, ∀ i, v i (a : K) ≤ 1)
    (ε : ℝ) (hε : 0 < ε)
    (hfloor : ∀ a : C, a ≠ 0 → ¬ IsUnit a →
      ε ≤ ∑ i, realValuationOrder (v i) (a : K)) : Factorization.IsBFDomain C := by
  classical
  let degree : C → ℝ := fun a => ∑ i, realValuationOrder (v i) (a : K)
  intro x hx
  apply Factorization.hasBoundedFactorizations_of_realDegree degree
    (floor := ε) (hx := hx)
  · intro a ha
    apply Finset.sum_eq_zero
    intro i _
    have hv : v i (a : K) = 1 := coefficient_unit_value C.subtype (v i) (fun a => hC a i) ha
    simp only [realValuationOrder, hv, NNReal.coe_one, Real.log_one, neg_zero]
  · intro a b ha hb
    dsimp [degree]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact realValuationOrder_mul _ (Subtype.coe_ne_coe.mpr ha) (Subtype.coe_ne_coe.mpr hb)
  · exact hε
  · intro a ha _
    apply Finset.sum_nonneg
    intro i _
    exact (realValuationOrder_nonneg_iff _ (Subtype.coe_ne_coe.mpr ha)).mpr (hC a i)
  · intro a ha _ hnu
    exact hfloor a ha hnu

/-- Failure of BF gives actual source nonunits simultaneously small at finitely
many containing valuations. This is a conclusion about source elements, not values alone. -/
theorem exists_small_nonunit_of_not_isBFDomain
    {ι : Type*} [Fintype ι] (v : ι → Valuation K ℝ≥0) (C : Subring K)
    (hC : ∀ a : C, ∀ i, v i (a : K) ≤ 1)
    (hnot : ¬ Factorization.IsBFDomain C) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : C, a ≠ 0 ∧ ¬ IsUnit a ∧ ∀ i, realValuationOrder (v i) (a : K) < ε := by
  classical
  have hex : ∃ a : C, a ≠ 0 ∧ ¬ IsUnit a ∧
      (∑ i, realValuationOrder (v i) (a : K)) < ε := by
    by_contra! h
    apply hnot
    exact isBFDomain_of_finite_valuation_floor v C hC ε hε h
  obtain ⟨a, ha0, hanu, ha⟩ := hex
  refine ⟨a, ha0, hanu, fun i => ?_⟩
  apply lt_of_le_of_lt _ ha
  exact Finset.single_le_sum
    (fun j _ => (realValuationOrder_nonneg_iff _ (Subtype.coe_ne_coe.mpr ha0)).mpr (hC a j))
    (Finset.mem_univ i)

/-- A nonzero conductor can be made strictly positive at every dominating branch. -/
theorem exists_positive_conductor
    {ι : Type*} (v : ι → Valuation K ℝ≥0) (B C : Subring K) (hCB : C ≤ B)
    (hC : ∀ a : C, ∀ i, v i (a : K) ≤ 1)
    (hcenter : ∀ a : C, a ≠ 0 → ¬ IsUnit a → ∀ i, 0 < realValuationOrder (v i) a)
    {d : K} (hd0 : d ≠ 0) (hd : ∀ b : B, d * (b : K) ∈ C)
    (a : C) (ha0 : a ≠ 0) (hanu : ¬ IsUnit a) :
    ∃ e : K, e ≠ 0 ∧ (∀ i, 0 < realValuationOrder (v i) e) ∧
      ∀ b : B, e * (b : K) ∈ C := by
  have hdC : d ∈ C := by simpa using hd 1
  refine ⟨d * (a : K), mul_ne_zero hd0 (Subtype.coe_ne_coe.mpr ha0), ?_, ?_⟩
  · intro i
    rw [realValuationOrder_mul _ hd0 (Subtype.coe_ne_coe.mpr ha0)]
    exact add_pos_of_nonneg_of_pos
      ((realValuationOrder_nonneg_iff _ hd0).mpr (hC ⟨d, hdC⟩ i))
      (hcenter a ha0 hanu i)
  · intro b
    simpa only [Subring.coe_mul, mul_assoc] using hd (⟨a, hCB a.property⟩ * b)

/-- Concrete coefficient and conductor data for the sparse cut. The rescaled
valuations define the same valuation rings as the given branches. -/
structure ConductorCoefficientData {ι : Type*}
    (v : ι → Valuation K ℝ≥0) (B C : Subring K) where
  coefficient : Subring C
  coefficient_local : IsLocalRing coefficient
  valuation : ι → Valuation K ℝ≥0
  integer_ring_iff : ∀ i x, valuation i x ≤ 1 ↔ v i x ≤ 1
  positive_order_iff : ∀ i x, 0 < realValuationOrder (valuation i) x ↔
    0 < realValuationOrder (v i) x
  coefficient_orders : ∀ a : coefficient, a ≠ 0 →
    ∃ n : ℕ, ∀ i, realValuationOrder (valuation i) ((a : C) : K) = n
  coefficient_unit : ∀ a : coefficient, a ≠ 0 → ∀ i,
    realValuationOrder (valuation i) ((a : C) : K) = 0 → IsUnit a
  element : K
  element_ne_zero : element ≠ 0
  element_order : ∀ i, realValuationOrder (valuation i) element = 1
  cutoff : ℕ
  cutoff_pos : 0 < cutoff
  conductor : ∀ b : B, element ^ cutoff * (b : K) ∈ C

/-- Every local common-conductor situation supplies actual coefficient data,
in every characteristic and without a module-finiteness assumption. -/
theorem nonempty_conductorCoefficientData
    {ι : Type*} [Fintype ι] (v : ι → Valuation K ℝ≥0)
    (B C : Subring K) [IsLocalRing C] (hCB : C ≤ B)
    (hB : ∀ x : K, x ∈ B ↔ ∀ i, v i x ≤ 1)
    (hcenter : ∀ a : C, a ≠ 0 → ¬ IsUnit a → ∀ i, 0 < realValuationOrder (v i) a)
    {d : K} (hd0 : d ≠ 0) (hd : ∀ b : B, d * (b : K) ∈ C)
    (a : C) (ha0 : a ≠ 0) (hanu : ¬ IsUnit a) :
    Nonempty (ConductorCoefficientData v B C) := by
  classical
  have hC : ∀ a : C, ∀ i, v i (a : K) ≤ 1 := fun a => (hB _).mp (hCB a.property)
  obtain ⟨A, hA | ⟨hA, hlocal⟩⟩ := exists_field_or_dvr_coefficients C
  · let : Field A := hA.toField
    obtain ⟨e, he0, hepos, heC⟩ := exists_positive_conductor v B C hCB hC hcenter hd0 hd a ha0 hanu
    let w : ι → Valuation K ℝ≥0 := fun i => normalizeRealValuation (v i) e (hepos i)
    have hw : ∀ i x, w i x ≤ 1 ↔ v i x ≤ 1 :=
      fun i x => normalizeRealValuation_le_one_iff _ _ _ _
    let f : A →+* K := C.subtype.comp A.subtype
    have hfbound : ∀ i x, w i (f x) ≤ 1 := fun i x => (hw i _).mpr (hC x i)
    refine ⟨{ coefficient := A
              coefficient_local := inferInstance
              valuation := w
              integer_ring_iff := hw
              positive_order_iff := fun i x => realValuationOrder_normalize_pos_iff _ _ _ _
              coefficient_orders := ?_
              coefficient_unit := ?_
              element := e
              element_ne_zero := he0
              element_order := fun i => realValuationOrder_normalize_self _ _ _
              cutoff := 1
              cutoff_pos := zero_lt_one
              conductor := ?_ }⟩
    · intro x hx
      refine ⟨0, fun i => ?_⟩
      simpa only [Nat.cast_zero, f, RingHom.comp_apply, Subring.subtype_apply] using field_coefficient_order f (w i) (hfbound i) hx
    · intro x hx _ _
      exact isUnit_iff_ne_zero.mpr hx
    · intro b
      simpa only [pow_one] using heC b
  · let : IsDiscreteValuationRing A := hA
    let : IsLocalHom A.subtype := hlocal
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
    let f : A →+* K := C.subtype.comp A.subtype
    have hf : Function.Injective f := C.subtype_injective.comp A.subtype_injective
    have hπ0 : f π ≠ 0 := (map_ne_zero_iff f hf).mpr hπ.ne_zero
    have hπC0 : (π : C) ≠ 0 := Subtype.coe_ne_coe.mpr hπ.ne_zero
    have hπnu : ¬ IsUnit (π : C) := fun h => hπ.not_isUnit ((isUnit_map_iff A.subtype π).mp h)
    have hπpos : ∀ i, 0 < realValuationOrder (v i) (f π) := hcenter π hπC0 hπnu
    let w : ι → Valuation K ℝ≥0 := fun i => normalizeRealValuation (v i) (f π) (hπpos i)
    have hw : ∀ i x, w i x ≤ 1 ↔ v i x ≤ 1 :=
      fun i x => normalizeRealValuation_le_one_iff _ _ _ _
    have hwB : ∀ x : K, x ∈ B ↔ ∀ i, w i x ≤ 1 := by
      intro x
      simp only [hw, hB]
    have hfbound : ∀ i x, w i (f x) ≤ 1 := fun i x => (hw i _).mpr (hC x i)
    have hnorm : ∀ i, realValuationOrder (w i) (f π) = 1 :=
      fun i => realValuationOrder_normalize_self _ _ _
    obtain ⟨n, hn0, hn⟩ := exists_uniformizer_power_conductor w B C hwB hπ0 hd0 hnorm hd
    refine ⟨{ coefficient := A
              coefficient_local := inferInstance
              valuation := w
              integer_ring_iff := hw
              positive_order_iff := fun i x => realValuationOrder_normalize_pos_iff _ _ _ _
              coefficient_orders := ?_
              coefficient_unit := ?_
              element := f π
              element_ne_zero := hπ0
              element_order := hnorm
              cutoff := n
              cutoff_pos := hn0
              conductor := hn }⟩
    · intro x hx
      exact normalized_dvr_coefficient_orders f w hfbound hπ hnorm hx
    · intro x hx i hz
      exact (normalized_dvr_coefficient_order_zero_iff f hf (w i) (hfbound i) hπ (hnorm i) hx).mp hz

/-- The entire open tail lies in the literal source if a normalized uniformizer
power multiplies the intersection ring into that source. -/
theorem open_tail_mem_of_conductor
    {ι : Type*} (v : ι → Valuation K ℝ≥0) (B C : Subring K)
    (hB : ∀ x : K, x ∈ B ↔ ∀ i, v i x ≤ 1)
    {π : K} (hπ0 : π ≠ 0) (hπ : ∀ i, realValuationOrder (v i) π = 1)
    (c : ℕ) (hc : ∀ b : B, π ^ c * (b : K) ∈ C)
    {x : K} (hx : x ≠ 0) (hval : ∀ i, (c : ℝ) < realValuationOrder (v i) x) :
    x ∈ C := by
  have hq0 : x / π ^ c ≠ 0 := div_ne_zero hx (pow_ne_zero _ hπ0)
  have hqB : x / π ^ c ∈ B := by
    apply (hB _).mpr
    intro i
    apply (realValuationOrder_nonneg_iff _ hq0).mp
    rw [realValuationOrder_div _ hx (pow_ne_zero _ hπ0), realValuationOrder_pow, hπ i, mul_one]
    exact (sub_pos.mpr (hval i)).le
  have h := hc ⟨x / π ^ c, hqB⟩
  simpa only [mul_div_cancel₀ _ (pow_ne_zero _ hπ0)] using h

/-- The finite-branch conductor theorem with its exact atomicity input.
Every subring containing a nonzero source ideal must be atomic; hereditary
atomicity of the localization is not assumed. -/
theorem isBFDomain_of_finite_valuation_conductor
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → Valuation K ℝ≥0) (B C : Subring K)
    [IsLocalRing C] (hCB : C ≤ B)
    (hB : ∀ x : K, x ∈ B ↔ ∀ i, v i x ≤ 1)
    (hcenter : ∀ a : C, a ≠ 0 → ¬ IsUnit a → ∀ i, 0 < realValuationOrder (v i) a)
    (hatomic : ∀ S : Subring C, (∃ I : Ideal C, I ≠ ⊥ ∧ (I : Set C) ⊆ S) →
      Factorization.IsAtomicDomain S)
    {d : K} (hd0 : d ≠ 0) (hd : ∀ b : B, d * (b : K) ∈ C) :
    Factorization.IsBFDomain C := by
  classical
  by_contra hnot
  have hC : ∀ a : C, ∀ i, v i (a : K) ≤ 1 := fun a => (hB _).mp (hCB a.property)
  obtain ⟨a, ha0, hanu, _⟩ := exists_small_nonunit_of_not_isBFDomain v C hC hnot 1 zero_lt_one
  let q := Classical.choice (nonempty_conductorCoefficientData v B C hCB hB hcenter hd0 hd a ha0 hanu)
  let w := q.valuation
  have hwB : ∀ x : K, x ∈ B ↔ ∀ i, w i x ≤ 1 := by
    intro x
    simp only [w, q.integer_ring_iff, hB]
  have hwC : ∀ a : C, ∀ i, w i (a : K) ≤ 1 := fun a i => (q.integer_ring_iff i _).mpr (hC a i)
  have hBnonneg : ∀ x : B, x ≠ 0 → ∀ i, 0 ≤ realValuationOrder (w i) x := by
    intro x hx i
    exact (realValuationOrder_nonneg_iff _ (Subtype.coe_ne_coe.mpr hx)).mpr ((hwB _).mp x.property i)
  let f : C →+* B := Subring.inclusion hCB
  let C' : Subring B := f.range
  let A' : Subring B := q.coefficient.map f
  have hA'C' : A' ≤ C' := by
    rintro x ⟨a, _, rfl⟩
    exact ⟨a, rfl⟩
  have hcoeff : ∀ x : A', x ≠ 0 → ∃ n : ℕ, ∀ i,
      realValuationOrder (w i) ((x : B) : K) = n := by
    rintro ⟨x, hx⟩ hx0
    obtain ⟨a, ha, hax⟩ := hx
    have ha0 : (⟨a, ha⟩ : q.coefficient) ≠ 0 := by
      intro h
      apply hx0
      apply Subtype.ext
      have haC : a = 0 := congrArg Subtype.val h
      change x = (0 : B)
      exact hax.symm.trans (by rw [haC, map_zero])
    obtain ⟨n, hn⟩ := q.coefficient_orders ⟨a, ha⟩ ha0
    refine ⟨n, fun i => ?_⟩
    change realValuationOrder (w i) (x : K) = n
    rw [← hax]
    exact hn i
  have hπB : q.element ∈ B := (hwB _).mpr fun i =>
    (realValuationOrder_nonneg_iff _ q.element_ne_zero).mp ((q.element_order i).symm ▸ zero_le_one)
  let π : B := ⟨q.element, hπB⟩
  let I := realValuationTail w B hBnonneg q.cutoff
  have hIC' : (I : Set B) ⊆ C' := by
    intro x hx
    have hxC : (x : K) ∈ C := by
      rcases hx with hx | hx
      · simp [hx]
      · apply open_tail_mem_of_conductor w B C hwB q.element_ne_zero q.element_order
          q.cutoff q.conductor
        · intro hx0
          have : x = 0 := Subtype.ext hx0
          have hh := hx (Classical.choice ‹Nonempty ι›)
          simp only [this, Subring.coe_zero, realValuationOrder_zero] at hh
          exact (not_lt_of_ge (Nat.cast_nonneg q.cutoff)) hh
        · exact hx
    exact ⟨⟨x, hxC⟩, rfl⟩
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ x : B, x ∈ C' ∧ x ≠ 0 ∧
      ∀ i, 0 < realValuationOrder (w i) x ∧ realValuationOrder (w i) x < ε := by
    intro ε hε
    obtain ⟨x, hx0, hxnu, hx⟩ := exists_small_nonunit_of_not_isBFDomain w C hwC hnot ε hε
    refine ⟨f x, ⟨x, rfl⟩, ?_, fun i => ⟨?_, hx i⟩⟩
    · exact fun h => hx0 ((Subring.inclusion_injective hCB) (h.trans (map_zero f).symm))
    · exact (q.positive_order_iff i _).mpr (hcenter x hx0 hxnu i)
  obtain ⟨S, hSC', hSnot, hIS, hI0⟩ := exists_nonatomic_polynomial_tail w B hBnonneg
    (fun x hx => (hwB x).mpr hx) C' A' hA'C' hcoeff π
    (fun h => q.element_ne_zero (congrArg Subtype.val h)) q.element_order q.cutoff q.cutoff_pos hIC' hsmall
  let T : Subring C := S.comap f
  have hIcomap : I.comap f ≠ ⊥ := by
    obtain ⟨b, hbI, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨a, ha⟩ := hIC' hbI
    intro hz
    have haI : a ∈ I.comap f := by
      change f a ∈ I
      rw [ha]
      exact hbI
    have ha0 : a = 0 := Ideal.mem_bot.mp (hz ▸ haI)
    exact hb0 (by simpa [ha0] using ha.symm)
  have hT : Factorization.IsAtomicDomain T := hatomic T
    ⟨I.comap f, hIcomap, fun _ hx => hIS hx⟩
  apply hSnot
  have hmap := (Factorization.subring_map_isAtomicDomain_iff T f
    (Subring.inclusion_injective hCB)).mpr hT
  rwa [Subring.map_comap_eq_self hSC'] at hmap

/-- A local source with a finite-branch dimension-one Prüfer overring and
nonzero conductor is BF under the exact common-ideal atomicity hypothesis. -/
theorem isBFDomain_of_semilocal_pruefer_conductor
    (B C : Subring K) [IsLocalRing C] [IsFractionRing B K]
    [Finite (MaximalSpectrum B)] [Ring.KrullDimLE 1 B]
    (hpruefer : IsPrueferDomain B) (hfield : ¬ IsField B) (hCB : C ≤ B)
    (hcenter : ∀ P : MaximalSpectrum B,
      P.asIdeal.comap (Subring.inclusion hCB) = IsLocalRing.maximalIdeal C)
    (hatomic : ∀ S : Subring C, (∃ I : Ideal C, I ≠ ⊥ ∧ (I : Set C) ⊆ S) →
      Factorization.IsAtomicDomain S)
    {d : K} (hd0 : d ≠ 0) (hd : ∀ b : B, d * (b : K) ∈ C) :
    Factorization.IsBFDomain C := by
  classical
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let v := prueferMaximalRealValuation B hpruefer hfield
  apply isBFDomain_of_finite_valuation_conductor v B C hCB
    (mem_pruefer_iff_realValuations_le_one B hpruefer hfield) _ hatomic hd0 hd
  intro a ha hnu P
  apply (realValuationOrder_pos_iff _ (Subtype.coe_ne_coe.mpr ha)).mpr
  apply (prueferMaximalRealValuation_lt_one_iff B hpruefer hfield P
    (Subring.inclusion hCB a)).mpr
  change a ∈ P.asIdeal.comap (Subring.inclusion hCB)
  rw [hcenter P]
  exact hnu

/-- The local normalization version retains only the actual Prüfer, finite
branch and common-conductor hypotheses, together with common-ideal atomicity. -/
theorem local_isBFDomain_of_semilocal_normalization_conductor
    (C : Subring K) [IsLocalRing C] [IsFractionRing C K]
    [Finite (MaximalSpectrum (integralClosure C K))]
    [Ring.KrullDimLE 1 (integralClosure C K)]
    (hpruefer : IsPrueferDomain (integralClosure C K))
    (hatomic : ∀ S : Subring C, (∃ I : Ideal C, I ≠ ⊥ ∧ (I : Set C) ⊆ S) →
      Factorization.IsAtomicDomain S)
    {d : K} (hd0 : d ≠ 0)
    (hd : ∀ b : integralClosure C K, d * (b : K) ∈ C) : Factorization.IsBFDomain C := by
  classical
  by_cases hfieldC : IsField C
  · let : Field C := hfieldC.toField
    exact Factorization.isBFDomain_of_field C
  let B := (integralClosure C K).toSubring
  let : Algebra C B := inferInstanceAs (Algebra C (integralClosure C K))
  let : IsScalarTower C B K := inferInstanceAs (IsScalarTower C (integralClosure C K) K)
  let : Algebra.IsIntegral C B := inferInstanceAs (Algebra.IsIntegral C (integralClosure C K))
  let : IsFractionRing B K := normalization_isFractionRing C K
  have hCB : C ≤ B := by
    intro x hx
    exact (integralClosure C K).algebraMap_mem ⟨x, hx⟩
  have hinj : Function.Injective (algebraMap C B) := by
    intro x y h
    apply IsFractionRing.injective C K
    rw [IsScalarTower.algebraMap_apply C B K x, IsScalarTower.algebraMap_apply C B K y, h]
  have hfieldB : ¬ IsField B := fun hb => hfieldC
    (isField_of_isIntegral_of_isField hinj hb)
  have hcenter : ∀ P : MaximalSpectrum B,
      P.asIdeal.comap (Subring.inclusion hCB) = IsLocalRing.maximalIdeal C := by
    intro P
    have hmax : (P.asIdeal.comap (algebraMap C B)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
    exact IsLocalRing.eq_maximalIdeal hmax
  exact isBFDomain_of_semilocal_pruefer_conductor B C hpruefer hfieldB hCB
    hcenter hatomic hd0 hd

end HereditaryAtomicity
