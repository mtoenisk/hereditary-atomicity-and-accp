import UnconditionalCounterexample.IntersectionStalks
import UnconditionalCounterexample.PoleAlgebra
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# The full prime spectrum from paired isolators

A prime meeting the nonzero integers contains a rational prime. A power of that
rational prime factors as the product of the paired isolators, so the prime ideal
equals one of their maximal centers. The other primes contract from the pole algebra.
For a nonzero horizontal prime, a quotient of the form g^k/f^m excludes containment in
a vertical center.

The horizontal stalk is obtained by the canonical localization tower. The
concrete pole algebra is proved to be a PID without a finite-generation
hypothesis on its denominator set. Together with the preceding vertical
stalk theorem this gives every maximal stalk as a DVR.

The pair product identities and singleton isolator profiles are explicit
construction inputs. The complete prime list, its maximality, and stalk
identifications are conclusions, not constructor assumptions.
-/

noncomputable section
namespace UnconditionalCounterexample.IntersectionSpectrum
open WithZero IntersectionDomain IntersectionStalks
variable {K ι : Type*} [Field K]

/-- A prime meeting the integer denominators contains a rational prime. -/
theorem exists_prime_natCast_mem (D : Subring K) (P : Ideal D) [P.IsPrime]
    (h : ¬Disjoint (integerDenominators D : Set D) (P : Set D)) :
    ∃ p : ℕ, p.Prime ∧ (p : D) ∈ P := by
  obtain ⟨s, hs, hsP⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨z, hz, hzs⟩ := hs
  let I : Ideal ℤ := P.comap (Int.castRingHom D)
  have hzI : z ∈ I := by
    change (Int.castRingHom D) z ∈ P
    rwa [hzs]
  have hI0 : I ≠ ⊥ := by
    intro hI
    have hz0 : z = 0 := by simpa [hI] using hzI
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hz) hz0
  have hI : I.IsPrime := inferInstance
  obtain ⟨q, hq, hp⟩ := hI.exists_mem_prime_of_ne_bot hI0
  refine ⟨q.natAbs, Int.prime_iff_natAbs_prime.mp hp, ?_⟩
  have hqabs : (q.natAbs : ℤ) ∈ I := by
    rw [Int.natCast_natAbs]
    rcases le_total 0 q with hq0 | hq0
    · simpa [abs_of_nonneg hq0] using hq
    · simpa [abs_of_nonpos hq0] using I.neg_mem hq
  change ((q.natAbs : ℤ) : D) ∈ P at hqabs
  simpa only [Int.cast_natCast] using hqabs

/-- A product decomposition of each rational prime power into paired isolators
proves the vertical-versus-horizontal dichotomy for all prime ideals. -/
theorem prime_vertical_or_disjoint (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    (left right : {p : ℕ // p.Prime} → ι)
    (hmax : ∀ i, (center B v i).IsMaximal)
    (hpair : ∀ p : {p : ℕ // p.Prime}, ∃ f g : intersection B v, ∃ k : ℕ, 0 < k ∧
      f * g = (p.val : intersection B v) ^ k ∧
      (Ideal.span ({f} : Set (intersection B v))).radical = center B v (left p) ∧
      (Ideal.span ({g} : Set (intersection B v))).radical = center B v (right p))
    (P : Ideal (intersection B v)) [P.IsPrime] :
    (∃ i, P = center B v i) ∨
      Disjoint (integerDenominators (intersection B v) : Set (intersection B v)) (P : Set _) := by
  by_cases hdis : Disjoint (integerDenominators (intersection B v) : Set (intersection B v)) (P : Set _)
  · exact Or.inr hdis
  · obtain ⟨p, hp, hpP⟩ := exists_prime_natCast_mem (intersection B v) P hdis
    obtain ⟨f, g, k, hk, hfg, hf, hg⟩ := hpair ⟨p, hp⟩
    have := hmax (left ⟨p, hp⟩)
    have := hmax (right ⟨p, hp⟩)
    have hprod : f * g ∈ P := by
      rw [hfg]
      exact P.pow_mem_of_mem hpP k hk
    rcases prime_eq_one_of_isolator_radicals P _ _ f g hf hg hprod with h | h
    · exact Or.inl ⟨left ⟨p, hp⟩, h⟩
    · exact Or.inl ⟨right ⟨p, hp⟩, h⟩

/-- An isolator outside a nonzero prime produces an element of that prime
outside the selected vertical center. No defining horizontal polynomial is needed. -/
theorem not_le_center_of_isolator_not_mem (B : Subring K)
    (v : ι → Valuation K ℤᵐ⁰) (i : ι)
    (P : Ideal (intersection B v)) [P.IsPrime] (hP0 : P ≠ ⊥)
    (f : intersection B v) (k : ℕ) (hk : 0 < k) (hfinv : (f : K)⁻¹ ∈ B)
    (hfi : v i f = exp (-(k : ℤ))) (hfother : ∀ j, j ≠ i → v j f = 1)
    (hfP : f ∉ P) : ¬P ≤ center B v i := by
  obtain ⟨g, hgP, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hgK0 : (g : K) ≠ 0 := fun h => hg0 (Subtype.ext h)
  obtain ⟨m, hm⟩ := exists_nat_value (v i) g hgK0
    (((mem_intersection B v g).mp g.property).2 i)
  let s : K := (g : K) ^ k / (f : K) ^ m
  have hsval : v i s = 1 := by
    dsimp [s]
    rw [map_div₀, map_pow, map_pow, hm, hfi, ← exp_nsmul, ← exp_nsmul, ← exp_sub]
    have hzero : k • (-(m : ℤ)) - m • (-(k : ℤ)) = 0 := by
      simp only [nsmul_eq_mul]
      ring
    rw [hzero, exp_zero]
  have hs : s ∈ intersection B v :=
    div_pow_mem_of_bound B v i ((g : K) ^ k) f ((intersection B v).pow_mem g.property k)
      hfinv hfother m (by rw [← hsval])
  let z : intersection B v := ⟨s, hs⟩
  have hfK0 : (f : K) ≠ 0 := by
    intro hz
    exact exp_ne_zero (hfi.symm.trans (by simp [hz]))
  have heq : f ^ m * z = g ^ k := by
    apply Subtype.ext
    change (f : K) ^ m * ((g : K) ^ k / (f : K) ^ m) = (g : K) ^ k
    exact mul_div_cancel₀ _ (pow_ne_zero m hfK0)
  have hP : P.IsPrime := inferInstance
  have hzP : z ∈ P := by
    have hprod : f ^ m * z ∈ P := by
      rw [heq]
      exact P.pow_mem_of_mem hgP k hk
    exact (hP.mem_or_mem hprod).resolve_left (fun h => hfP (hP.mem_of_pow_mem m h))
  intro hle
  have hzval := (mem_center B v i z).mp (hle hzP)
  change v i s < 1 at hzval
  rw [hsval] at hzval
  exact lt_irrefl _ hzval

/-- A horizontal prime extends to an actual prime of the pole algebra and is
recovered by contraction along the canonical inclusion. -/
theorem horizontal_extension (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    [IsLocalization (integerDenominators (intersection B v)) B]
    (P : Ideal (intersection B v)) [P.IsPrime]
    (hdis : Disjoint (integerDenominators (intersection B v) : Set (intersection B v))
      (P : Set (intersection B v))) :
    (P.map (algebraMap (intersection B v) B)).IsPrime ∧
      (P.map (algebraMap (intersection B v) B)).under (intersection B v) = P :=
  ⟨IsLocalization.isPrime_of_isPrime_disjoint _ B P inferInstance hdis,
    IsLocalization.under_map_of_isPrime_disjoint _ B inferInstance hdis⟩

/-- A B-unit isolator cannot belong to a horizontal prime. -/
theorem isolator_not_mem_horizontal (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    [IsLocalization (integerDenominators (intersection B v)) B]
    (P : Ideal (intersection B v)) [P.IsPrime]
    (hdis : Disjoint (integerDenominators (intersection B v) : Set (intersection B v))
      (P : Set (intersection B v)))
    (f : intersection B v) (hf0 : (f : K) ≠ 0) (hfinv : (f : K)⁻¹ ∈ B) : f ∉ P := by
  have hQ := (horizontal_extension B v P hdis).1
  have hunit : IsUnit (algebraMap (intersection B v) B f) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨(f : K)⁻¹, hfinv⟩, ?_⟩
    apply Subtype.ext
    exact mul_inv_cancel₀ hf0
  intro hfP
  exact hQ.ne_top ((P.map (algebraMap (intersection B v) B)).eq_top_of_isUnit_mem
    (Ideal.mem_map_of_mem _ hfP) hunit)

/-- The image of a nonzero horizontal prime is nonzero. -/
theorem horizontal_extension_ne_bot (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    (P : Ideal (intersection B v)) (hP : P ≠ ⊥) :
    P.map (algebraMap (intersection B v) B) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  intro hbot
  have h := Ideal.mem_map_of_mem (algebraMap (intersection B v) B) hx
  rw [hbot, Ideal.mem_bot] at h
  apply hx0
  apply Subtype.ext
  exact congrArg (fun z : B => (z : K)) h

/-- In the paired construction every nonzero horizontal prime is maximal.
The required separation from vertical centers is proved with the isolators. -/
theorem horizontal_isMaximal (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    [IsLocalization (integerDenominators (intersection B v)) B] [Ring.DimensionLEOne B]
    (left right : {p : ℕ // p.Prime} → ι)
    (hmax : ∀ i, (center B v i).IsMaximal)
    (hpair : ∀ p : {p : ℕ // p.Prime}, ∃ f g : intersection B v, ∃ k : ℕ, 0 < k ∧
      f * g = (p.val : intersection B v) ^ k ∧
      (Ideal.span ({f} : Set (intersection B v))).radical = center B v (left p) ∧
      (Ideal.span ({g} : Set (intersection B v))).radical = center B v (right p))
    (hiso : ∀ i, ∃ f : intersection B v, ∃ k : ℕ, 0 < k ∧ (f : K)⁻¹ ∈ B ∧
      v i f = exp (-(k : ℤ)) ∧ ∀ j, j ≠ i → v j f = 1)
    (P : Ideal (intersection B v)) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hdis : Disjoint (integerDenominators (intersection B v) : Set (intersection B v))
      (P : Set (intersection B v))) :
    P.IsMaximal := by
  have hP : P.IsPrime := inferInstance
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
  have := hM
  rcases prime_vertical_or_disjoint B v left right hmax hpair M with ⟨i, hMi⟩ | hMdis
  · obtain ⟨f, k, hk, hfinv, hfi, hfother⟩ := hiso i
    have hf0 : (f : K) ≠ 0 := by
      intro hz
      exact exp_ne_zero (hfi.symm.trans (by simp [hz]))
    have hfP := isolator_not_mem_horizontal B v P hdis f hf0 hfinv
    exact False.elim (not_le_center_of_isolator_not_mem B v i P hP0 f k hk hfinv hfi
      hfother hfP (hMi ▸ hPM))
  · have hQP := horizontal_extension B v P hdis
    have hQM := horizontal_extension B v M hMdis
    have hQmax := hQP.1.isMaximal (horizontal_extension_ne_bot B v P hP0)
    have heq := hQmax.eq_of_le hQM.1.ne_top (Ideal.map_mono hPM)
    have hPeqM : P = M := by
      rw [← hQP.2, ← hQM.2, heq]
    exact hPeqM ▸ hM

/-- Localization first at the integers and then at a horizontal prime gives the
same canonical stalk as localizing D at its contraction. -/
def horizontalStalkEquiv (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    [IsLocalization (integerDenominators (intersection B v)) B]
    (Q : Ideal B) [Q.IsPrime] :
    Localization.AtPrime (Q.under (intersection B v)) ≃ₐ[intersection B v]
      Localization.AtPrime Q := by
  letI : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.under (intersection B v)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (integerDenominators (intersection B v)) (Localization.AtPrime Q) Q
  exact IsLocalization.algEquiv (Q.under (intersection B v)).primeCompl _ _

/-- The actual horizontal stalk is a DVR once the pole algebra is Dedekind. -/
theorem horizontalStalk_isDVR (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    [IsLocalization (integerDenominators (intersection B v)) B] [IsDedekindDomain B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime (Q.under (intersection B v))) := by
  have : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hQ _
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (horizontalStalkEquiv B v Q).symm

/-- The concrete pole algebra is a principal ideal domain, with no finite
hypothesis on the set of inverted polynomials. -/
theorem poleAlgebra_isPrincipalIdealRing (S : Set (Polynomial K))
    (hS : ∀ q ∈ S, q ≠ 0) : IsPrincipalIdealRing (PoleAlgebra.generated S) := by
  have := PoleAlgebra.isLocalization_generated S hS
  refine ⟨fun I => ?_⟩
  rw [← IsLocalization.map_under (Submonoid.closure S) (PoleAlgebra.generated S) I]
  exact (inferInstance : (I.under (Polynomial K)).IsPrincipal).map_ringHom _

/-- Consequently the concrete pole algebra supplies the Dedekind hypothesis
used for its nonzero horizontal stalks. -/
theorem poleAlgebra_isDedekindDomain (S : Set (Polynomial K))
    (hS : ∀ q ∈ S, q ≠ 0) : IsDedekindDomain (PoleAlgebra.generated S) := by
  have := poleAlgebra_isPrincipalIdealRing S hS
  infer_instance

/-- A nonzero singleton isolator proves that every maximal ideal is nonzero. -/
theorem maximal_ne_bot_of_isolator (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    (i : ι) (f : intersection B v) (k : ℕ) (hk : 0 < k)
    (hfi : v i f = exp (-(k : ℤ)))
    (M : Ideal (intersection B v)) [M.IsMaximal] : M ≠ ⊥ := by
  have hf0 : f ≠ 0 := by
    intro hz
    exact exp_ne_zero (hfi.symm.trans (by simp [hz]))
  have hfc : f ∈ center B v i := by
    rw [mem_center, hfi, exp_lt_one_iff]
    exact neg_neg_of_pos (by exact_mod_cast hk)
  have hc0 : center B v i ≠ ⊥ := by
    intro hc
    exact hf0 (by simpa [hc] using hfc)
  intro hM0
  have hM : M.IsMaximal := inferInstance
  have hc : M = center B v i := hM.eq_of_le (center_isPrime B v i).ne_top (by simp [hM0])
  exact hc0 (hc.symm.trans hM0)

/-- Complete prime classification from the paired product identities and the
actual integer localization. Horizontal primes are actual contractions from B. -/
theorem prime_classification (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    [IsLocalization (integerDenominators (intersection B v)) B]
    (left right : {p : ℕ // p.Prime} → ι)
    (hmax : ∀ i, (center B v i).IsMaximal)
    (hpair : ∀ p : {p : ℕ // p.Prime}, ∃ f g : intersection B v, ∃ k : ℕ, 0 < k ∧
      f * g = (p.val : intersection B v) ^ k ∧
      (Ideal.span ({f} : Set (intersection B v))).radical = center B v (left p) ∧
      (Ideal.span ({g} : Set (intersection B v))).radical = center B v (right p))
    (P : Ideal (intersection B v)) [P.IsPrime] :
    (∃ i, P = center B v i) ∨ ∃ Q : Ideal B, Q.IsPrime ∧ P = Q.under (intersection B v) := by
  rcases prime_vertical_or_disjoint B v left right hmax hpair P with hv | hd
  · exact Or.inl hv
  · exact Or.inr ⟨P.map (algebraMap (intersection B v) B),
      (horizontal_extension B v P hd).1, (horizontal_extension B v P hd).2.symm⟩

/-- Equality of prime ideals transports the DVR property of their actual localizations. -/
theorem stalk_isDVR_of_eq {R : Type*} [CommRing R] [IsDomain R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P = Q)
    (hP : IsDiscreteValuationRing (Localization.AtPrime P)) :
    IsDiscreteValuationRing (Localization.AtPrime Q) := by
  subst Q
  exact hP

/-- All maximal stalks are DVRs, proved from actual local rings and explicit
isolators/product identities rather than a supplied maximal-list assumption. -/
theorem every_maximal_stalk_isDVR [Nonempty ι]
    (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    [IsLocalization (integerDenominators (intersection B v)) B]
    [IsFractionRing (intersection B v) K] [IsDedekindDomain B]
    (left right : {p : ℕ // p.Prime} → ι)
    (hmax : ∀ i, (center B v i).IsMaximal)
    (hdvr : ∀ i, IsDiscreteValuationRing (v i).valuationSubring)
    (hpair : ∀ p : {p : ℕ // p.Prime}, ∃ f g : intersection B v, ∃ k : ℕ, 0 < k ∧
      f * g = (p.val : intersection B v) ^ k ∧
      (Ideal.span ({f} : Set (intersection B v))).radical = center B v (left p) ∧
      (Ideal.span ({g} : Set (intersection B v))).radical = center B v (right p))
    (hiso : ∀ i, ∃ f : intersection B v, ∃ k : ℕ, 0 < k ∧ (f : K)⁻¹ ∈ B ∧
      v i f = exp (-(k : ℤ)) ∧ ∀ j, j ≠ i → v j f = 1)
    (M : Ideal (intersection B v)) [M.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime M) := by
  have hM0 : M ≠ ⊥ := by
    let i : ι := Classical.choice inferInstance
    obtain ⟨f, k, hk, _, hfi, _⟩ := hiso i
    exact maximal_ne_bot_of_isolator B v i f k hk hfi M
  rcases prime_vertical_or_disjoint B v left right hmax hpair M with ⟨i, rfl⟩ | hd
  · obtain ⟨f, k, hk, hfinv, hfi, hfother⟩ := hiso i
    have := hdvr i
    exact stalk_isDVR B v i f k hk hfinv hfi hfother
  · have hext := horizontal_extension B v M hd
    have := hext.1
    have h := horizontalStalk_isDVR B v (M.map (algebraMap (intersection B v) B))
      (horizontal_extension_ne_bot B v M hM0)
    exact stalk_isDVR_of_eq _ M hext.2 h

end UnconditionalCounterexample.IntersectionSpectrum
