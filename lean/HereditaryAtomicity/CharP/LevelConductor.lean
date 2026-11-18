import HereditaryAtomicity.FiniteNormalization
import HereditaryAtomicity.CharP.FunctionField
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.NumberTheory.FunctionField

/-!
# Conductors at finite function-field levels

Finite generation over the polynomial base produces a common denominator in
that base, although the source need not be finite over it. After localizing at
the zero of the coordinate, this gives a power conductor for each finite level.
The exponent is allowed to depend on the level.
-/

noncomputable section

namespace HereditaryAtomicity.CharP

open scoped nonZeroDivisors Polynomial

/-- The polynomial denominators which are invertible at the coordinate zero. -/
def polynomialZeroDenominators (k : Type*) [Field k] : Submonoid k[X] :=
  (nonZeroDivisors k).comap Polynomial.constantCoeff

@[simp]
theorem mem_polynomialZeroDenominators (k : Type*) [Field k] (q : k[X]) :
    q ∈ polynomialZeroDenominators k ↔ q.coeff 0 ≠ 0 := by
  simp [polynomialZeroDenominators, mem_nonZeroDivisors_iff_ne_zero]

theorem mem_polynomialZeroDenominators_iff_not_mem (k : Type*) [Field k] (q : k[X]) :
    q ∈ polynomialZeroDenominators k ↔
      q ∉ Ideal.span ({Polynomial.X} : Set k[X]) := by
  rw [mem_polynomialZeroDenominators, Ideal.mem_span_singleton, Polynomial.X_dvd_iff]

/-- The mapped denominators remain regular in the actual level normalization. -/
theorem polynomialZeroDenominators_map_le (k L : Type*) [Field k] [Field L]
    [Algebra k[X] L] [Algebra (RatFunc k) L] [IsScalarTower k[X] (RatFunc k) L] :
    (polynomialZeroDenominators k).map
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k L)) ≤
      nonZeroDivisors (_root_.FunctionField.ringOfIntegers k L) := by
  rintro _ ⟨q, hq, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro hq0
  have hz : q = 0 := _root_.FunctionField.ringOfIntegers.algebraMap_injective k L
    (by simpa only [map_zero] using hq0)
  exact (mem_polynomialZeroDenominators k q).mp hq (by simp [hz])

/-- The literal finite-level normalization localized at the base prime `(X)`.
Its embedding in `L`, and hence in any compatible ambient field, is fixed. -/
def finiteLevelLocalRing (k L : Type*) [Field k] [Field L]
    [Algebra k[X] L] [Algebra (RatFunc k) L] [IsScalarTower k[X] (RatFunc k) L]
    [_root_.FunctionField k L] :
    Subalgebra (_root_.FunctionField.ringOfIntegers k L) L :=
  Localization.subalgebra.ofField L
    ((polynomialZeroDenominators k).map
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k L)))
    (polynomialZeroDenominators_map_le k L)

/-- A finite base module in the actual source fraction field admits a common
nonzero denominator from the base, if the source is algebraic over the base. -/
theorem exists_nonzero_base_conductor
    (A D F : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    [Field F] [Algebra A D] [Algebra D F] [Algebra A F]
    [IsScalarTower A D F] [FaithfulSMul A D] [IsFractionRing D F]
    [Algebra.IsAlgebraic A D] (E : Type*) [CommRing E] [Algebra A E]
    [Module.Finite A E] (ι : E →ₐ[A] F) :
    ∃ c : A, c ≠ 0 ∧ ∀ x : E, ∃ d : D,
      algebraMap D F d = algebraMap A F c * ι x := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite A E)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples
    (Algebra.algebraMapSubmonoid D A⁰) s ι
  obtain ⟨a, ha, hca⟩ := c.property
  refine ⟨a, nonZeroDivisors.coe_ne_zero ⟨a, ha⟩, ?_⟩
  intro x
  have hx : x ∈ Submodule.span A (s : Set E) := by rw [hs]; trivial
  have hint : IsLocalization.IsInteger D ((c : D) • ι x) := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact hc x hx
    | zero => simpa using (IsLocalization.isInteger_zero (R := D) (S := F))
    | add x y _ _ hx hy => simpa [smul_add] using IsLocalization.isInteger_add hx hy
    | smul a x _ hx =>
      simpa only [Algebra.smul_def, map_mul, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply A D F, mul_left_comm] using
        IsLocalization.isInteger_smul (a := algebraMap A D a) hx
  obtain ⟨d, hd⟩ := hint
  refine ⟨d, ?_⟩
  simpa only [Algebra.smul_def, ← hca, ← IsScalarTower.algebraMap_apply] using hd

/-- Localizing the polynomial base away from its coordinate zero turns a
finite-level base conductor into a coordinate-power conductor. The returned
fractions are exactly those in the corresponding localization of the level. -/
theorem exists_polynomial_power_return
    (k D F E : Type*) [Field k] [CommRing D] [IsDomain D] [Field F]
    [CommRing E] [Algebra k[X] D] [Algebra D F] [Algebra k[X] F]
    [IsScalarTower k[X] D F] [FaithfulSMul k[X] D] [IsFractionRing D F]
    [Algebra.IsAlgebraic k[X] D] [Algebra k[X] E] [Module.Finite k[X] E]
    (ι : E →ₐ[k[X]] F) (R : Subring F)
    (hD : ∀ d : D, algebraMap D F d ∈ R)
    (haway : ∀ q : k[X], q.coeff 0 ≠ 0 → (algebraMap k[X] F q)⁻¹ ∈ R) :
    ∃ a : ℕ, ∀ (ω : E) (q : k[X]), q.coeff 0 ≠ 0 →
      (algebraMap k[X] F Polynomial.X)^a * (ι ω / algebraMap k[X] F q) ∈ R := by
  obtain ⟨c, hc, hcond⟩ := exists_nonzero_base_conductor k[X] D F E ι
  obtain ⟨u, hcu, hu⟩ := c.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hc 0
  simp only [Polynomial.C_0, sub_zero, Polynomial.X_dvd_iff] at hcu hu
  have hAF : Function.Injective (algebraMap k[X] F) := by
    rw [IsScalarTower.algebraMap_eq k[X] D F]
    exact (IsFractionRing.injective D F).comp (FaithfulSMul.algebraMap_injective k[X] D)
  have huF : algebraMap k[X] F u ≠ 0 := by
    intro hz
    have hz' : u = 0 := hAF (by simpa only [map_zero] using hz)
    exact hu (by simp only [hz', Polynomial.coeff_zero])
  refine ⟨c.rootMultiplicity 0, ?_⟩
  intro ω q hq
  obtain ⟨d, hd⟩ := hcond ω
  have hret : (algebraMap k[X] F Polynomial.X)^(c.rootMultiplicity 0) * ι ω ∈ R := by
    convert R.mul_mem (hD d) (haway u hu) using 1
    rw [hd]
    conv_rhs => rw [hcu, map_mul, map_pow]
    field_simp
  simpa only [div_eq_mul_inv, mul_assoc] using R.mul_mem hret (haway q hq)

/-- The common denominator for the actual normalization of a finite separable
function-field level lies in the original polynomial base. -/
theorem exists_finite_level_base_conductor
    (k D F L : Type*) [Field k] [CommRing D] [IsDomain D] [Field F] [Field L]
    [Algebra k[X] D] [Algebra D F] [Algebra k[X] F]
    [IsScalarTower k[X] D F] [FaithfulSMul k[X] D] [IsFractionRing D F]
    [Algebra.IsAlgebraic k[X] D]
    [Algebra k[X] L] [Algebra (RatFunc k) L] [IsScalarTower k[X] (RatFunc k) L]
    [_root_.FunctionField k L] [Algebra.IsSeparable (RatFunc k) L]
    (ι : L →ₐ[k[X]] F) :
    ∃ c : k[X], c ≠ 0 ∧ ∀ ω : _root_.FunctionField.ringOfIntegers k L,
      ∃ d : D, algebraMap D F d = algebraMap k[X] F c * ι (ω : L) := by
  let := FunctionField.finite_ringOfIntegers k L
  exact exists_nonzero_base_conductor k[X] D F (_root_.FunctionField.ringOfIntegers k L)
    (ι.comp (_root_.FunctionField.ringOfIntegers k L).val)

/-- A power of the actual coordinate returns the literal localized finite
normalization to any source overring containing the base local ring. -/
theorem exists_finite_level_power_return
    (k D F L : Type*) [Field k] [CommRing D] [IsDomain D] [Field F] [Field L]
    [Algebra k[X] D] [Algebra D F] [Algebra k[X] F]
    [IsScalarTower k[X] D F] [FaithfulSMul k[X] D] [IsFractionRing D F]
    [Algebra.IsAlgebraic k[X] D]
    [Algebra k[X] L] [Algebra (RatFunc k) L] [IsScalarTower k[X] (RatFunc k) L]
    [_root_.FunctionField k L] [Algebra.IsSeparable (RatFunc k) L]
    (ι : L →ₐ[k[X]] F) (R : Subring F)
    (hD : ∀ d : D, algebraMap D F d ∈ R)
    (haway : ∀ q : k[X], q.coeff 0 ≠ 0 → (algebraMap k[X] F q)⁻¹ ∈ R) :
    ∃ a : ℕ, ∀ x : finiteLevelLocalRing k L,
      (algebraMap k[X] F Polynomial.X)^a * ι (x : L) ∈ R := by
  let := FunctionField.finite_ringOfIntegers k L
  obtain ⟨a, ha⟩ := exists_polynomial_power_return k D F
    (_root_.FunctionField.ringOfIntegers k L)
    (ι.comp (_root_.FunctionField.ringOfIntegers k L).val) R hD haway
  refine ⟨a, ?_⟩
  intro x
  obtain ⟨ω, s, hs, hx⟩ := x.property
  obtain ⟨q, hq, rfl⟩ := hs
  rw [hx, map_mul, map_inv₀, ← IsScalarTower.algebraMap_apply k[X]
    (_root_.FunctionField.ringOfIntegers k L) L, ι.commutes]
  simpa only [div_eq_mul_inv, AlgHom.coe_comp, Function.comp_apply,
    Subalgebra.coe_val, Subalgebra.algebraMap_apply] using
    ha ω q ((mem_polynomialZeroDenominators k q).mp hq)

/-- Increasing a source-return exponent by one places every returned element
in the source maximal ideal; its one-plus translate is consequently a unit. -/
theorem positive_power_return_in_maximalIdeal
    {F : Type*} [Field F] (R : Subring F) [IsLocalRing R]
    (π : R) (hπ : π ∈ IsLocalRing.maximalIdeal R) (a : ℕ)
    (x : F) (hx : (π : F)^a * x ∈ R) :
    ∃ r : R, (r : F) = (π : F)^(a + 1) * x ∧
      r ∈ IsLocalRing.maximalIdeal R ∧ IsUnit (1 + r) := by
  let r : R := π * ⟨(π : F)^a * x, hx⟩
  have hr : r ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).mul_mem_right _ hπ
  refine ⟨r, ?_, hr, ?_⟩
  · change (π : F) * ((π : F)^a * x) = (π : F)^(a + 1) * x
    rw [pow_succ]
    ring
  · have hn : -r ∈ nonunits R := (IsLocalRing.maximalIdeal R).neg_mem hr
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-r) hn

/-- If the coordinate lies in a source prime, every polynomial with nonzero
constant coefficient avoids that prime. Thus the base local ring really maps
to the actual source stalk. -/
theorem polynomial_image_not_mem_of_constantCoeff_ne_zero
    (k D : Type*) [Field k] [CommRing D] [Algebra k D] [Algebra k[X] D]
    [IsScalarTower k k[X] D] (M : Ideal D) [M.IsPrime]
    (hX : algebraMap k[X] D Polynomial.X ∈ M)
    (q : k[X]) (hq : q.coeff 0 ≠ 0) : algebraMap k[X] D q ∉ M := by
  have hdiff : algebraMap k[X] D q - algebraMap k[X] D (Polynomial.C (q.coeff 0)) ∈ M := by
    obtain ⟨g, hg⟩ := Polynomial.X_dvd_sub_C (p := q)
    rw [← map_sub, hg, map_mul]
    exact M.mul_mem_right _ hX
  intro hm
  have hc : algebraMap k[X] D (Polynomial.C (q.coeff 0)) ∈ M := by
    simpa only [sub_sub_cancel] using M.sub_mem hm hdiff
  have hunit : IsUnit (algebraMap k[X] D (Polynomial.C (q.coeff 0))) := by
    change IsUnit (algebraMap k[X] D (algebraMap k k[X] (q.coeff 0)))
    rw [← IsScalarTower.algebraMap_apply]
    exact (isUnit_iff_ne_zero.mpr hq).map (algebraMap k D)
  exact (inferInstance : M.IsPrime).ne_top (M.eq_top_of_isUnit_mem hc hunit)

/-- At an actual source prime containing the coordinate, each compatible
finite separable level has a positive power conductor into the source stalk.
Every returned element lies in its maximal ideal, and its one-plus translate
is a source-stalk unit. No conductor is assumed, and no exponent uniform over
all finite levels is asserted. -/
theorem exists_finite_level_stalk_return
    (k D F L : Type*) [Field k] [CommRing D] [IsDomain D] [Field F] [Field L]
    [Algebra k D] [Algebra k[X] D] [IsScalarTower k k[X] D]
    [Algebra D F] [Algebra k[X] F] [IsScalarTower k[X] D F]
    [FaithfulSMul k[X] D] [IsFractionRing D F] [Algebra.IsAlgebraic k[X] D]
    [Algebra k[X] L] [Algebra (RatFunc k) L] [IsScalarTower k[X] (RatFunc k) L]
    [_root_.FunctionField k L] [Algebra.IsSeparable (RatFunc k) L]
    (ι : L →ₐ[k[X]] F) (M : Ideal D) [M.IsPrime]
    (hX : algebraMap k[X] D Polynomial.X ∈ M) :
    ∃ h : ℕ, 0 < h ∧ ∀ x : finiteLevelLocalRing k L,
      ∃ r : Localization.subalgebra.ofField F M.primeCompl M.primeCompl_le_nonZeroDivisors,
        (r : F) = (algebraMap k[X] F Polynomial.X)^h * ι (x : L) ∧
          ¬ IsUnit r ∧ IsUnit (1 + r) := by
  let S := Localization.subalgebra.ofField F M.primeCompl M.primeCompl_le_nonZeroDivisors
  let : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S M
  have hD : ∀ d : D, algebraMap D F d ∈ S.toSubring := S.algebraMap_mem
  have haway : ∀ q : k[X], q.coeff 0 ≠ 0 → (algebraMap k[X] F q)⁻¹ ∈ S.toSubring := by
    intro q hq
    refine ⟨1, algebraMap k[X] D q,
      polynomial_image_not_mem_of_constantCoeff_ne_zero k D M hX q hq, ?_⟩
    simp only [map_one, one_mul, ← IsScalarTower.algebraMap_apply]
  obtain ⟨a, ha⟩ := exists_finite_level_power_return k D F L ι S.toSubring hD haway
  let π : S := algebraMap D S (algebraMap k[X] D Polynomial.X)
  have hπ : π ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff S M _).mpr hX
  have hπF : (π : F) = algebraMap k[X] F Polynomial.X := by
    change algebraMap D F (algebraMap k[X] D Polynomial.X) = _
    rw [← IsScalarTower.algebraMap_apply]
  refine ⟨a + 1, Nat.succ_pos _, ?_⟩
  intro x
  obtain ⟨r, hr, hrm, hunit⟩ := positive_power_return_in_maximalIdeal S.toSubring π hπ
    a (ι (x : L)) (by simpa only [hπF] using ha x)
  exact ⟨r, by simpa only [hπF] using hr, hrm, hunit⟩

end HereditaryAtomicity.CharP
