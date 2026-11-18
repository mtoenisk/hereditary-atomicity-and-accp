import HereditaryAtomicity.DVRBase.Reduction
import HereditaryAtomicity.DVRBase.Radical
import HereditaryAtomicity.SparseProductCut
import Factorization.PrincipalIdeals

/-!
# Source chains with a uniformizer-power top

Multiplication by a common scalar makes the first endpoint a uniformizer power. All
endpoint equations and ratio-power divisibilities hold in the source ring. Valuation
bounds can then be imposed on the normalized chain.
-/

noncomputable section
open scoped NNReal
namespace HereditaryAtomicity.DVRBase

/-- Exact endpoint equations and source divisibility for a chain normalized at a
uniformizer power. -/
structure UniformizerChainData {R : Type*} [CommRing R]
    (π : R) (ratio : ℕ → R) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  endpoint : ℕ → R
  endpoint_ne_zero : ∀ n, endpoint n ≠ 0
  top : endpoint 0 = π ^ exponent
  step : ∀ n, endpoint n = endpoint (n + 1) * ratio n
  ratio_power : ∀ n, ∃ e : ℕ, 0 < e ∧ π ^ exponent ∣ ratio n ^ e

variable {R : Type*} [CommRing R]

theorem UniformizerChainData.ratio_ne_zero {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (n : ℕ) : t n ≠ 0 := by
  intro h
  exact C.endpoint_ne_zero n (by rw [C.step n, h, mul_zero])

section AlgebraicDVR

variable (A R K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing R] [IsDomain R] [IsLocalRing R] [Field K]
  [Algebra A R] [Algebra R K] [IsFractionRing R K]
  [Algebra A K] [IsScalarTower A R K] [FaithfulSMul A K]
  [Algebra.IsAlgebraic A K]

include A K

/-- Scale an actual nonzero chain to a uniformizer-power top and retain
positive-power witnesses for all its ratios in the actual source ring. -/
theorem exists_uniformizerChainData_scaled {π : A} (hπ : Irreducible π)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (ht : ∀ n, t n ∈ IsLocalRing.maximalIdeal R)
    (hxt : ∀ n, x n = x (n + 1) * t n) :
    ∃ (C : UniformizerChainData (algebraMap A R π) t) (w : R),
      ∀ n, C.endpoint n = algebraMap A R π * w * x n := by
  let : Algebra.IsAlgebraic A R := Algebra.IsAlgebraic.tower_bot_of_injective
    (A := K) (IsFractionRing.injective R K)
  have hπR : algebraMap A R π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply FaithfulSMul.algebraMap_injective A K
    rw [IsScalarTower.algebraMap_apply A R K, h, map_zero, map_zero]
  obtain ⟨m, w, hw⟩ := exists_dvd_uniformizer_pow hπ (hx 0)
  have hw0 : w ≠ 0 := by
    intro h
    exact pow_ne_zero m hπR (by simpa [h] using hw)
  let c : ℕ → R := fun n => algebraMap A R π * w * x n
  have hc0 : ∀ n, c n ≠ 0 :=
    fun n => mul_ne_zero (mul_ne_zero hπR hw0) (hx n)
  have htop : c 0 = algebraMap A R π ^ (m + 1) := by
    dsimp [c]
    rw [pow_succ, hw]
    ring
  have hI : Ideal.span {algebraMap A R π ^ (m + 1)} ≠ (⊥ : Ideal R) := by
    intro h
    exact pow_ne_zero (m + 1) hπR (Ideal.span_singleton_eq_bot.mp h)
  refine ⟨{
    exponent := m + 1
    exponent_pos := Nat.succ_pos _
    endpoint := c
    endpoint_ne_zero := hc0
    top := htop
    step := ?_
    ratio_power := ?_
  }, w, ?_⟩
  · intro n
    dsimp [c]
    rw [hxt n]
    ring
  · intro n
    obtain ⟨e, he, hmem⟩ := exists_pos_pow_mem_of_algebraic_dvr A R K
      (Ideal.span {algebraMap A R π ^ (m + 1)}) hI (ht n)
    exact ⟨e, he, Ideal.mem_span_singleton.mp hmem⟩
  · intro n
    rfl

/-- The local scaling factory retains endpoint divisibility separately. -/
theorem exists_uniformizerChainData_with_dvd {π : A} (hπ : Irreducible π)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (ht : ∀ n, t n ∈ IsLocalRing.maximalIdeal R)
    (hxt : ∀ n, x n = x (n + 1) * t n) :
    ∃ C : UniformizerChainData (algebraMap A R π) t,
      ∀ n, algebraMap A R π ∣ C.endpoint n := by
  obtain ⟨C, w, he⟩ := exists_uniformizerChainData_scaled A R K hπ x t hx ht hxt
  exact ⟨C, fun n => ⟨w * x n, by rw [he n]; ring⟩⟩

/-- The local scaling factory, forgetting its additional endpoint divisibility. -/
theorem exists_uniformizerChainData {π : A} (hπ : Irreducible π)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (ht : ∀ n, t n ∈ IsLocalRing.maximalIdeal R)
    (hxt : ∀ n, x n = x (n + 1) * t n) :
    Nonempty (UniformizerChainData (algebraMap A R π) t) := by
  obtain ⟨C, _⟩ := exists_uniformizerChainData_with_dvd A R K hπ x t hx ht hxt
  exact ⟨C⟩

/-- Failure of ACCP supplies the exact source-chain data needed for the
DVR-base construction, with no hereditary-atomicity assumption. -/
theorem exists_uniformizerChainData_of_not_wfDvdMonoid
    {π : A} (hπ : Irreducible π) (hfail : ¬ WfDvdMonoid R) :
    ∃ t : ℕ → R, (∀ n, t n ∈ IsLocalRing.maximalIdeal R) ∧
      Nonempty (UniformizerChainData (algebraMap A R π) t) := by
  obtain ⟨x, t, hx, ht, hxt⟩ :=
    Factorization.not_wfDvdMonoid_iff_exists_nonunit_chain.mp hfail
  have htM : ∀ n, t n ∈ IsLocalRing.maximalIdeal R :=
    fun n => (IsLocalRing.mem_maximalIdeal _).mpr (ht n)
  exact ⟨t, htM, exists_uniformizerChainData A R K hπ x t hx htM hxt⟩

end AlgebraicDVR

/-- The scaled-chain construction for literal coefficient and source subrings
of one field. The coefficient DVR need only lie in this local source ring. -/
theorem embedded_exists_uniformizerChainData
    {K : Type*} [Field K] (A R : Subring K)
    [IsDiscreteValuationRing A] [IsLocalRing R] [IsFractionRing R K]
    [Algebra.IsAlgebraic A K] (hAR : A ≤ R)
    {π : A} (hπ : Irreducible π)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (ht : ∀ n, t n ∈ IsLocalRing.maximalIdeal R)
    (hxt : ∀ n, x n = x (n + 1) * t n) :
    Nonempty (UniformizerChainData (Subring.inclusion hAR π) t) := by
  let : Algebra A R := (Subring.inclusion hAR).toAlgebra
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact exists_uniformizerChainData A R K hπ x t hx ht hxt

/-- Literal scaled endpoints for the embedded local-chain factory. -/
theorem embedded_exists_uniformizerChainData_scaled
    {K : Type*} [Field K] (A R : Subring K)
    [IsDiscreteValuationRing A] [IsLocalRing R] [IsFractionRing R K]
    [Algebra.IsAlgebraic A K] (hAR : A ≤ R)
    {π : A} (hπ : Irreducible π)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (ht : ∀ n, t n ∈ IsLocalRing.maximalIdeal R)
    (hxt : ∀ n, x n = x (n + 1) * t n) :
    ∃ (C : UniformizerChainData (Subring.inclusion hAR π) t) (w : R),
      ∀ n, C.endpoint n = Subring.inclusion hAR π * w * x n := by
  let : Algebra A R := (Subring.inclusion hAR).toAlgebra
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact exists_uniformizerChainData_scaled A R K hπ x t hx ht hxt

/-- The embedded local scaling factory retains endpoint divisibility as a
separate conclusion; it is not part of the arbitrary-chain interface. -/
theorem embedded_exists_uniformizerChainData_with_dvd
    {K : Type*} [Field K] (A R : Subring K)
    [IsDiscreteValuationRing A] [IsLocalRing R] [IsFractionRing R K]
    [Algebra.IsAlgebraic A K] (hAR : A ≤ R)
    {π : A} (hπ : Irreducible π)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (ht : ∀ n, t n ∈ IsLocalRing.maximalIdeal R)
    (hxt : ∀ n, x n = x (n + 1) * t n) :
    ∃ C : UniformizerChainData (Subring.inclusion hAR π) t,
      ∀ n, Subring.inclusion hAR π ∣ C.endpoint n := by
  let : Algebra A R := (Subring.inclusion hAR).toAlgebra
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact exists_uniformizerChainData_with_dvd A R K hπ x t hx ht hxt

/-- Source divisibility by the normalized uniformizer gives the lower value
bound one for every chain endpoint at any valuation containing the source. -/
theorem UniformizerChainData.one_le_endpoint_order
    {R K : Type*} [CommRing R] [Field K]
    {π : R} {t : ℕ → R} (C : UniformizerChainData π t)
    (hdiv : ∀ n, π ∣ C.endpoint n)
    (f : R →+* K) (hf : Function.Injective f) (v : Valuation K ℝ≥0)
    (hv : ∀ r : R, v (f r) ≤ 1)
    (hπ : realValuationOrder v (f π) = 1) (n : ℕ) :
    1 ≤ realValuationOrder v (f (C.endpoint n)) := by
  obtain ⟨r, hr⟩ := hdiv n
  have hp : f π * f r ≠ 0 := by
    rw [← map_mul, ← hr]
    exact (map_ne_zero_iff f hf).mpr (C.endpoint_ne_zero n)
  have hπ0 : f π ≠ 0 := (mul_ne_zero_iff.mp hp).1
  have hr0 : f r ≠ 0 := (mul_ne_zero_iff.mp hp).2
  have hrord := (realValuationOrder_nonneg_iff v hr0).mpr (hv r)
  rw [hr, map_mul, realValuationOrder_mul v hπ0 hr0, hπ]
  linarith

end HereditaryAtomicity.DVRBase
