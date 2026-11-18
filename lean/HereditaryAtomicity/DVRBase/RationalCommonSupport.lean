import HereditaryAtomicity.DVRBase.RationalCoefficientBase
import HereditaryAtomicity.DVRBase.CommonSupportClients
import HereditaryAtomicity.DVRBase.MultiplaceDescentTermination

/-! The one-rational-prime obstruction from actual common-support chains. -/
noncomputable section
namespace HereditaryAtomicity.DVRBase
variable {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]

/-- The actual rational-prime DVR is an algebraic coefficient base for K. -/
theorem rationalCoefficientRing_isAlgebraic (p : ℕ) [Fact p.Prime] :
    Algebra.IsAlgebraic (rationalCoefficientRing p K) K := by
  let : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  let : Algebra.IsAlgebraic ℤ K := Algebra.IsAlgebraic.trans ℤ ℚ K
  exact Algebra.IsAlgebraic.extendScalars (R := ℤ) (S := rationalCoefficientRing p K) (A := K) (Int.cast_injective)

omit [Algebra.IsAlgebraic ℚ K] in
/-- A rational prime in a source maximal ideal puts the literal Z_(p) inside
its actual field-valued maximal stalk. -/
theorem rationalCoefficientRing_le_sourceMaximalStalk
    (p : ℕ) [Fact p.Prime] (D : Subring K) [IsFractionRing D K]
    (M : MaximalSpectrum D) (hpM : (p : D) ∈ M.asIdeal) :
    rationalCoefficientRing p K ≤ sourceMaximalStalk D M := by
  let R := sourceMaximalStalk D M
  let S := Localization.subalgebra.ofField K M.asIdeal.primeCompl
    M.asIdeal.primeCompl_le_nonZeroDivisors
  let : Algebra D R := inferInstanceAs (Algebra D S)
  let : IsLocalization.AtPrime R M.asIdeal := inferInstanceAs (IsLocalization.AtPrime S M.asIdeal)
  let : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R M.asIdeal
  apply rationalCoefficientRing_le_local p K R
  apply (IsLocalRing.mem_maximalIdeal _).mpr
  intro hu
  exact ((isUnit_sourceMaximalMap_iff D M (p : D)).mp (by simpa using hu)) hpM

/-- A strict chain supported on any nonempty set of centers over one rational
prime contradicts hereditary atomicity. All valuation, completion and return
data are constructed from the actual rational-prime coefficient DVR. -/
theorem rational_common_support_not_hereditarilyAtomic
    (p : ℕ) [Fact p.Prime] (D : Subring K) [IsFractionRing D K]
    (U : Set (MaximalSpectrum D)) (hU : U.Nonempty)
    (hpU : ∀ P ∈ U, (p : D) ∈ P.asIdeal)
    (x t : ℕ → D) (hx : ∀ n, x n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (hsupport : ∀ n (P : MaximalSpectrum D), t n ∈ P.asIdeal ↔ P ∈ U) :
    ¬ Factorization.IsHereditarilyAtomic D := by
  let O := rationalCoefficientRing p K
  let : Algebra.IsAlgebraic O K := rationalCoefficientRing_isAlgebraic p
  apply common_support_not_hereditarilyAtomic D O U hU
    (fun P hP => rationalCoefficientRing_le_sourceMaximalStalk p D P (hpU P hP))
    (rationalCoefficientUniformizer p K) (rationalCoefficientUniformizer_irreducible p K)
    (by rw [rationalCoefficientUniformizer_coe]; exact (p : D).property) ?_
    x t hx hxt hsupport
  intro P hP
  have he : (⟨rationalCoefficientUniformizer p K,
      by rw [rationalCoefficientUniformizer_coe]; exact (p : D).property⟩ : D) = (p : D) :=
    Subtype.ext (rationalCoefficientUniformizer_coe p K)
  simpa only [he] using hpU P hP

/-- A strict source chain with finite top support and all recurrent centers over one prime
yields consecutive blocks on a common support, contradicting hereditary atomicity. -/
theorem rational_recurrent_one_prime_not_hereditarilyAtomic
    (p : ℕ) [Fact p.Prime] (D : Subring K) [IsFractionRing D K]
    (x t : ℕ → D) (hx : ∀ n, x n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (ht : ∀ n, ¬ IsUnit (t n))
    (hfinite : Set.Finite {P : MaximalSpectrum D | x 0 ∈ P.asIdeal})
    (hp : ∀ P : MaximalSpectrum D, Set.Infinite {n | t n ∈ P.asIdeal} →
      (p : D) ∈ P.asIdeal) : ¬ Factorization.IsHereditarilyAtomic D := by
  obtain ⟨S, hS, hrec⟩ := exists_finite_nonempty_recurrent_set x t hxt ht hfinite
  obtain ⟨C, _, _, _⟩ := SupportedSourceChain.exists_of_recurrent_set S hS x t hx hxt hfinite hrec
  exact rational_common_support_not_hereditarilyAtomic p D (S : Set (MaximalSpectrum D))
    (by simpa using hS) (fun P hP => hp P ((hrec P).mpr hP))
    C.endpoint C.ratio C.endpoint_ne_zero C.step C.support

/-- A genuine common-support chain in an HA source cannot have all its
centers above one rational prime. This forces two distinct residue characteristics. -/
theorem rational_common_support_two_primes_of_hereditarilyAtomic
    (D : Subring K) [IsFractionRing D K] (hD : Factorization.IsHereditarilyAtomic D)
    (U : Set (MaximalSpectrum D)) (hU : U.Nonempty)
    (p : U → ℕ) (hp : ∀ P, (p P).Prime)
    (hpM : ∀ P : U, (p P : D) ∈ P.val.asIdeal)
    (x t : ℕ → D) (hx : ∀ n, x n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (hsupport : ∀ n (P : MaximalSpectrum D), t n ∈ P.asIdeal ↔ P ∈ U) :
    ∃ P Q : U, p P ≠ p Q := by
  classical
  obtain ⟨M, hM⟩ := hU
  let M' : U := ⟨M, hM⟩
  by_contra h
  push Not at h
  let : Fact (p M').Prime := ⟨hp M'⟩
  apply rational_common_support_not_hereditarilyAtomic (p M') D U ⟨M, hM⟩
    (fun P hP => ?_) x t hx hxt hsupport hD
  have he : p M' = p ⟨P, hP⟩ := h M' ⟨P, hP⟩
  rw [he]
  exact hpM ⟨P, hP⟩

end HereditaryAtomicity.DVRBase
