import UnconditionalCounterexample.Variations.MultiDomainPlaces

/-!
# The generic fibres of the two multivariate domains

Ordinary integration is governed by finitely many failures at the primary
and guard places of a horizontal fraction. A second integer clears the
denominator of its value at the reserved rational point. Consequently both
domains recover the very same horizontal localization after inverting the
nonzero integers.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open GuardSupport IntersectionDomain Filter WithZero

variable {r : ℕ} {A : Data r}

/-- The eventual integrality and prime normalizations needed to clear
denominators, without requiring the positive vertical support to be finite. -/
structure Clearing (A : Data r) where
  primes : ℕ → PrimeIndex
  primary_prime : ∀ j, A.primary j ((primes j).val : FunctionField r) = exp (-1)
  guard_prime : ∀ p, A.guard p (p.val : FunctionField r) = exp (-1)
  primary_late : ∀ z ∈ poleAlgebra A, ∀ᶠ j in atTop, A.primary j z ≤ 1
  guard_late : ∀ z ∈ poleAlgebra A, ∀ᶠ p in cofinite, A.guard p z ≤ 1

namespace Clearing

variable (H : Clearing A)
include H

theorem clear_ordinary (z : poleAlgebra A) : ∃ n : ℕ, 0 < n ∧ (n : FunctionField r) * z ∈ ordinary A := by
  apply exists_nat_mul_mem_intersection _ (vertical A) (Sum.elim (fun j ↦ (H.primes j).val) Subtype.val)
    (fun i ↦ by cases i with | inl j => exact (H.primes j).property.pos | inr p => exact p.property.pos)
    (fun i ↦ by cases i with | inl j => exact H.primary_prime j | inr p => exact H.guard_prime p)
    _ z.property
  apply Set.finite_preimage_inl_and_inr.mp
  obtain ⟨N, hN⟩ := eventually_atTop.mp (H.primary_late z z.property)
  refine ⟨(Set.finite_Iio N).subset fun j hj ↦ ?_, ?_⟩
  · exact lt_of_not_ge fun h ↦ (not_lt_of_ge (hN j h)) hj
  · simpa [Filter.eventually_cofinite, ← not_le, vertical] using H.guard_late z z.property

theorem clear_pullback (c : Fin r → ℚ) (hc : MultivariateFibres.Retained (denominators A) c)
    (q : ℕ) [Fact q.Prime] (z : poleAlgebra A) :
    ∃ n : ℕ, 0 < n ∧ (n : FunctionField r) * z ∈ pullback A c hc q := by
  obtain ⟨n, hn, hy⟩ := H.clear_ordinary z
  let y : ordinary A := ⟨(n : FunctionField r) * z, hy⟩
  let ev := point A c hc
  let a := ev y
  refine ⟨a.den*n, Nat.mul_pos a.den_pos hn, (a.den : ordinary A)*y, ?_, ?_⟩
  · change ev ((a.den : ordinary A)*y) ∈ PointPullback.localRationals q
    rw [map_mul, map_natCast]
    change (a.den : ℚ) * a ∈ _
    rw [Rat.den_mul_eq_num]
    exact intCast_mem _ _
  · change (a.den : FunctionField r) * (n * z) = (↑(a.den * n) : FunctionField r) * z
    rw [Nat.cast_mul, mul_assoc]

end Clearing

private theorem integerLocalization_of_clear {K : Type*} [Field K] [CharZero K]
    (D B : Subring K) (h : D ≤ B) [Algebra ℚ B]
    (H : ∀ x : B, ∃ n : ℕ, 0 < n ∧ (n : K) * x ∈ D) :
    letI := (Subring.inclusion h).toAlgebra
    IsLocalization (integerDenominators D) B := by
  let := (Subring.inclusion h).toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    have hmq : IsUnit (m : ℚ) := isUnit_iff_ne_zero.mpr (by
      exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.mp hm)
    simpa using hmq.map (algebraMap ℚ B)
  · intro x
    obtain ⟨n, hn, hnx⟩ := H x
    have hden : (n : D) ∈ integerDenominators D := by
      exact ⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast hn.ne'), by simp⟩
    refine ⟨⟨⟨n * (x : K), hnx⟩, ⟨n, hden⟩⟩, Subtype.ext ?_⟩
    exact mul_comm _ _
  · intro x y hxy
    exact ⟨1, by simpa using (Subtype.ext (congrArg B.subtype hxy) : x = y)⟩

theorem ordinary_le_pole : ordinary A ≤ (poleAlgebra A).toSubring := intersection_le _ _

theorem pullback_le_pole (c : Fin r → ℚ) (hc : MultivariateFibres.Retained (denominators A) c)
    (q : ℕ) [Fact q.Prime] : pullback A c hc q ≤ (poleAlgebra A).toSubring := by
  rintro _ ⟨x, _, rfl⟩
  exact ordinary_le_pole x.property

instance ordinaryPoleAlgebra : Algebra (ordinary A) (poleAlgebra A) :=
  (Subring.inclusion ordinary_le_pole).toAlgebra

instance pullbackPoleAlgebra (c : Fin r → ℚ) (hc : MultivariateFibres.Retained (denominators A) c)
    (q : ℕ) [Fact q.Prime] : Algebra (pullback A c hc q) (poleAlgebra A) :=
  (Subring.inclusion (pullback_le_pole c hc q)).toAlgebra

theorem ordinary_integerLocalization (H : Clearing A) :
    IsLocalization (integerDenominators (ordinary A)) (poleAlgebra A) := by
  let : Algebra ℚ (poleAlgebra A).toSubring := inferInstanceAs (Algebra ℚ (poleAlgebra A))
  exact integerLocalization_of_clear _ _ ordinary_le_pole H.clear_ordinary

theorem pullback_integerLocalization (H : Clearing A) (c : Fin r → ℚ)
    (hc : MultivariateFibres.Retained (denominators A) c) (q : ℕ) [Fact q.Prime] :
    IsLocalization (integerDenominators (pullback A c hc q)) (poleAlgebra A) := by
  let : Algebra ℚ (poleAlgebra A).toSubring := inferInstanceAs (Algebra ℚ (poleAlgebra A))
  exact integerLocalization_of_clear _ _ (pullback_le_pole c hc q) (H.clear_pullback c hc q)

end UnconditionalCounterexample.Variations.MultiDomain
