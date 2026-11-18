import UnconditionalCounterexample.DirectConductor

/-!
# The one-point local conductor by direct Taylor cancellation

The polynomial preimage of the actual conductor is a power of the sole
surviving linear factor. Integral values force its exponent positive, and
first-order Taylor cancellation excludes every repeated factor. All maps
are the actual localized first jets. There is no auxiliary second point.
-/

namespace UnconditionalCounterexample.DirectConductor

open Polynomial LocalizedPolynomialJets RadicalConductor

theorem ideal_above_linear_pow_eq {K : Type*} [Field K] (I : Ideal K[X])
    (a : K) (k : ℕ) (h : (X - C a) ^ k ∈ I) :
    ∃ e ≤ k, I = Ideal.span {(X - C a) ^ e} := by
  have hdiv := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp h
  obtain ⟨e, he, ha⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C a) k).mp hdiv
  refine ⟨e, he, ?_⟩
  rw [← Ideal.span_singleton_generator I]
  exact Ideal.span_singleton_eq_span_singleton.mpr ha

variable {K A : Type*} [NontriviallyNormedField K] [CommRing A]
  [Algebra K A] [Algebra K[X] A] [IsScalarTower K K[X] A]
  (M : Submonoid K[X]) [IsLocalization M A]

/-- Direct cancellation excludes a repeated sole linear factor. -/
theorem single_exponent_le_one_direct
    (a : K) (ha : ∀ m : M, (m : K[X]).eval a ≠ 0)
    (O : Subring K) (hO : ∀ u : K, u ∈ O ↔ ‖u‖ ≤ 1)
    (T : Subring A) (hscalar : ∀ u ∈ O, algebraMap K A u ∈ T)
    (hclear : ∀ y : A, ∃ c : K, c ≠ 0 ∧ algebraMap K A c * y ∈ T)
    (hvalue : ∀ z ∈ T, ‖(localizedFirstJet M A a ha z).fst‖ ≤ 1)
    (hderivative : ∀ N : ℝ, ∃ z ∈ T, N < ‖(localizedFirstJet M A a ha z).snd‖)
    (e : ℕ)
    (hI : (conductorIdeal T).comap (algebraMap K[X] A) =
      Ideal.span {(X - C a) ^ e}) : e ≤ 1 := by
  by_contra he
  have he2 : 2 ≤ e := by omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le he2
  have heN : e = n + 2 := by omega
  clear hn
  subst e
  let q : K[X] := (X - C a) ^ n
  have hq : q ≠ 0 := pow_ne_zero n (Polynomial.prime_X_sub_C a).ne_zero
  have hpol : q * (X - C a) ^ 2 = (X - C a) ^ (n + 2) := by
    dsimp [q]
    rw [pow_add]
  have hspan : conductorIdeal T =
      Ideal.span {algebraMap K[X] A q * algebraMap K[X] A (X - C a) ^ 2} := by
    rw [← IsLocalization.map_under M A (conductorIdeal T), Ideal.under, hI,
      Ideal.map_span, Set.image_singleton, ← hpol, map_mul]
    simp only [map_pow]
  have hcancel := cancel_localized_square_into_conductor M a ha O hO T hscalar
    (algebraMap K[X] A q) hclear (by
      intro y hy
      exact conductorIdeal_subset T y (hspan.symm ▸ hy)) hvalue hderivative
  have hcancelPoly : q * (X - C a) ∈
      (conductorIdeal T).comap (algebraMap K[X] A) := by
    change algebraMap K[X] A (q * (X - C a)) ∈ conductorIdeal T
    simpa only [map_mul] using hcancel
  have hneq := not_square_generator_of_cancelled_mem
    ((conductorIdeal T).comap (algebraMap K[X] A)) q (X - C a) hq
    (Polynomial.prime_X_sub_C a).ne_zero
    (Polynomial.prime_X_sub_C a).irreducible.not_isUnit hcancelPoly
  apply hneq
  rw [hpol]
  exact hI

/-- Exact one-point localized conductor, with the source's scalar clearing,
actual integral values, unbounded derivatives and initial ideal power. -/
theorem localized_conductor_eq_single_direct
    (O : Subring K) (hO : ∀ u : K, u ∈ O ↔ ‖u‖ ≤ 1)
    (T : Subring A) (a : K)
    (ha : ∀ m : M, (m : K[X]).eval a ≠ 0)
    (hscalar : ∀ u ∈ O, algebraMap K A u ∈ T)
    (hclear : ∀ y : A, ∃ c : K, c ≠ 0 ∧ algebraMap K A c * y ∈ T)
    (hvalue : ∀ z ∈ T, ‖(localizedFirstJet M A a ha z).fst‖ ≤ 1)
    (hderivative : ∀ N : ℝ, ∃ z ∈ T, N < ‖(localizedFirstJet M A a ha z).snd‖)
    (k : ℕ)
    (hpower : ∀ z ∈ Ideal.span {algebraMap K[X] A ((X - C a) ^ k)}, z ∈ T) :
    conductorIdeal T = Ideal.span {algebraMap K[X] A (X - C a)} := by
  let I : Ideal K[X] := (conductorIdeal T).comap (algebraMap K[X] A)
  have hpowermem : (X - C a) ^ k ∈ I := by
    change algebraMap K[X] A ((X - C a) ^ k) ∈ conductorIdeal T
    exact (le_conductorIdeal_iff T _).mpr hpower (Ideal.subset_span (by simp))
  obtain ⟨e, _, hI⟩ := ideal_above_linear_pow_eq I a k hpowermem
  have he_le := single_exponent_le_one_direct M a ha O hO T hscalar hclear
    hvalue hderivative e hI
  have hgen : algebraMap K[X] A ((X - C a) ^ e) ∈ conductorIdeal T := by
    change (X - C a) ^ e ∈ I
    rw [hI]
    exact Ideal.subset_span (by simp)
  let v : A →ₐ[K] K :=
    { toRingHom := (TrivSqZeroExt.fstHom K K K).toRingHom.comp (localizedFirstJet M A a ha)
      commutes' c := by
        change (localizedFirstJet M A a ha (algebraMap K A c)).fst = c
        rw [localizedFirstJet_scalar]
        rfl }
  have hz : ((X - C a) ^ e).eval a = 0 := by
    have hv := conductor_le_ker_of_integral_values T v hvalue hgen
    change (localizedFirstJet M A a ha (algebraMap K[X] A ((X - C a) ^ e))).fst = 0 at hv
    simpa only [localizedFirstJet_algebraMap_fst] using hv
  have he_ne : e ≠ 0 := by
    intro he
    simp only [he, pow_zero, eval_one] at hz
    exact one_ne_zero hz
  have he1 : e = 1 := by omega
  simp only [he1, pow_one] at hI
  rw [← IsLocalization.map_under M A (conductorIdeal T), Ideal.under]
  change I.map (algebraMap K[X] A) = _
  rw [hI, Ideal.map_span, Set.image_singleton]

end UnconditionalCounterexample.DirectConductor
