import HereditaryAtomicity.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.CharP.Basic

/-!
# Elementary semilocal arithmetic

Finiteness of the maximal spectrum supplies an inverted rational prime.
For a nonfield domain it also supplies a nonzero Jacobson element. A nonzero
Jacobson element is transcendental over any coefficient field contained in the
ring. These statements do not use hereditary atomicity.
-/

namespace HereditaryAtomicity

universe u v w

/-- A semilocal nontrivial commutative ring inverts some rational prime. -/
theorem exists_prime_isUnit_of_finite_maximalSpectrum
    (R : Type u) [CommRing R] [Nontrivial R] [Finite (MaximalSpectrum R)] :
    ∃ q : ℕ, Nat.Prime q ∧ IsUnit (q : R) := by
  classical
  let chars : MaximalSpectrum R → ℕ := fun M => ringChar (R ⧸ M.asIdeal)
  obtain ⟨n, hn⟩ := (Set.finite_range chars).bddAbove
  obtain ⟨q, hnq, hq⟩ := Nat.exists_infinite_primes (n + 1)
  refine ⟨q, hq, ?_⟩
  by_contra hu
  obtain ⟨M, hM, hqM⟩ := exists_max_ideal_of_mem_nonunits hu
  let : M.IsMaximal := hM
  have hqzero : (q : R ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M) q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hqM
  have hchar : ringChar (R ⧸ M) = q := CharP.ringChar_of_prime_eq_zero hq hqzero
  have hle : ringChar (R ⧸ M) ≤ n := hn ⟨(⟨M, hM⟩ : MaximalSpectrum R), rfl⟩
  omega

/-- A nonfield semilocal domain has a nonzero Jacobson element. -/
theorem exists_nonzero_mem_jacobson_of_semilocal_nonfield
    (R : Type u) [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hfield : ¬ IsField R) : ∃ c : R, c ≠ 0 ∧ c ∈ Ideal.jacobson (⊥ : Ideal R) := by
  classical
  let := Fintype.ofFinite (MaximalSpectrum R)
  have hM : ∀ M : MaximalSpectrum R, ∃ c : R, c ∈ M.asIdeal ∧ c ≠ 0 := by
    intro M
    exact Submodule.exists_mem_ne_zero_of_ne_bot
      (Ring.ne_bot_of_isMaximal_of_not_isField M.isMaximal hfield)
  choose c hc hczero using hM
  refine ⟨∏ M : MaximalSpectrum R, c M, Finset.prod_ne_zero_iff.mpr (fun M _ => hczero M), ?_⟩
  apply Ideal.mem_sInf.mpr
  rintro M ⟨_, hMmax⟩
  let P : MaximalSpectrum R := ⟨M, hMmax⟩
  exact M.mem_of_dvd (Finset.dvd_prod_of_mem c (Finset.mem_univ P)) (hc P)

/-- A Jacobson element of a nontrivial ring is not a unit. -/
theorem not_isUnit_of_mem_jacobson
    {R : Type u} [CommRing R] [Nontrivial R] {c : R}
    (hc : c ∈ Ideal.jacobson (⊥ : Ideal R)) : ¬ IsUnit c := by
  intro hu
  have htop := (Ideal.jacobson (⊥ : Ideal R)).eq_top_of_isUnit_mem hc hu
  exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp htop)

/-- A nonzero Jacobson element is transcendental over any embedded field. -/
theorem transcendental_of_nonzero_mem_jacobson
    (k : Type v) [Field k] {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    {c : R} (hc0 : c ≠ 0) (hc : c ∈ Ideal.jacobson (⊥ : Ideal R)) :
    Transcendental k c := by
  intro halg
  exact not_isUnit_of_mem_jacobson hc (halg.isIntegral.isUnit hc0)

/-- Adding one to a Jacobson element gives a unit. -/
theorem isUnit_one_add_of_mem_jacobson
    {R : Type u} [CommRing R] {c : R} (hc : c ∈ Ideal.jacobson (⊥ : Ideal R)) :
    IsUnit (1 + c) := by
  apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
  simpa using hc

/-- The Jacobson unit `1 + c` remains transcendental over a coefficient field. -/
theorem transcendental_one_add_of_nonzero_mem_jacobson
    (k : Type v) [Field k] {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    {c : R} (hc0 : c ≠ 0) (hc : c ∈ Ideal.jacobson (⊥ : Ideal R)) :
    Transcendental k (1 + c) := by
  intro halg
  apply transcendental_of_nonzero_mem_jacobson k hc0 hc
  simpa using halg.sub (isAlgebraic_one : IsAlgebraic k (1 : R))

/-- The nonzero Jacobson element supplies a unit which is not integral over
its prime subring, expressed through the canonical integer algebra. -/
theorem not_isIntegral_int_one_add_of_nonzero_mem_jacobson
    (k : Type v) [Field k] {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    {c : R} (hc0 : c ≠ 0) (hc : c ∈ Ideal.jacobson (⊥ : Ideal R)) :
    ¬ IsIntegral ℤ (1 + c) := by
  intro hint
  have htop : IsIntegral k (1 + c) := hint.tower_top
  exact transcendental_one_add_of_nonzero_mem_jacobson k hc0 hc htop.isAlgebraic

/-- Algebraicity of all images of the source ring extends to its actual fraction
field, even when the coefficient field is not contained in the source ring. -/
theorem isAlgebraic_fractionField_of_images
    (k : Type w) [Field k] {R : Type u} [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] [Algebra k K]
    (h : ∀ r : R, IsAlgebraic k (algebraMap R K r)) : Algebra.IsAlgebraic k K := by
  constructor
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R x
  simpa only [div_eq_mul_inv] using ((h a).isIntegral.mul (h b).isIntegral.inv).isAlgebraic

end HereditaryAtomicity
