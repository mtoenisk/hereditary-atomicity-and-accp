import UnconditionalCounterexample.PrimaryIsolators
import UnconditionalCounterexample.PairedDomain
import UnconditionalCounterexample.IntersectionSpectrum

/-!
# All maximal localizations of the actual paired domain

For the same primary and guard evaluations defining `PairedDomain.domain`,
residue maps prove maximality, and rational prime values identify the paired
places. The literal normalized generators produce all singleton isolators and
paired product identities. The actual integer localization and the pole
algebra PID then give every maximal localization as a DVR.

Construction inputs are the raw nonzero constants, prescribed b/q primary
columns, guard-unit values, and the persistent guard avoidance schedule.
No prime classification, full-stalk equality, or isolator is assumed.
-/

noncomputable section
namespace UnconditionalCounterexample.PairedSpectrum
open WithZero Polynomial GuardSupport PairedDomain IntersectionDomain IntersectionStalks
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

theorem vertical_eq_sum (d : Places) :
    Sum.elim (fun j => vertical d (.inl j)) (fun p => vertical d (.inr p)) = vertical d := by
  funext i
  cases i <;> rfl

/-- Distinct rational primes are units at the other prime's actual evaluation. -/
theorem valuation_other_prime {K : Type*} [Field K] (p q : PrimeIndex)
    (e : K →+* ℚ_[p.val]) (hpq : p ≠ q) :
    EvaluationDVR.valuation p.val e (q.val : K) = 1 := by
  have hne : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  simp [EvaluationDVR.valuation, Padic.mulValuation, q.property.ne_zero,
    Padic.valuation_natCast, padicValNat_primes hne]

/-- Every primary and guard center is actually maximal by its residue map. -/
theorem center_isMaximal (S : Set ℚ[X]) (d : Places) (i : ℕ ⊕ PrimeIndex) :
    (center (PoleAlgebra.generated S).toSubring (vertical d) i).IsMaximal := by
  cases i with
  | inl i =>
    exact center_isMaximal_of_residueMap _ _ _ (d.primes i).val
      (EvaluationDVR.residueMap _ (EvaluationDVR.evaluationHom _ _ (d.primary_trans i)))
      (EvaluationDVR.residueMap_ker _ _)
  | inr p =>
    exact center_isMaximal_of_residueMap _ _ _ p.val
      (EvaluationDVR.residueMap _ (guardEvaluation d.guard d.guard_trans p))
      (EvaluationDVR.residueMap_ker _ _)

/-- Each defining vertical ring is the actual discrete valuation ring. -/
theorem vertical_isDVR (d : Places) (i : ℕ ⊕ PrimeIndex) :
    IsDiscreteValuationRing (vertical d i).valuationSubring := by
  cases i with
  | inl i => exact EvaluationDVR.valuationSubring_isDVR _ _
  | inr p => exact EvaluationDVR.valuationSubring_isDVR _ _

/-- The prime at one primary has value one there and at its paired guard. -/
theorem prime_values (d : Places) (p : PrimeIndex) :
    vertical d (.inl (d.primes.symm p)) (p.val : RatFunc ℚ) = exp (-1) ∧
    vertical d (.inr p) (p.val : RatFunc ℚ) = exp (-1) ∧
    (∀ l, l ≠ .inl (d.primes.symm p) → l ≠ .inr p →
      vertical d l (p.val : RatFunc ℚ) = 1) := by
  constructor
  · have h := EvaluationDVR.valuation_prime (d.primes (d.primes.symm p)).val
      (EvaluationDVR.evaluationHom _ _ (d.primary_trans (d.primes.symm p)))
    change EvaluationDVR.valuation _
      (EvaluationDVR.evaluationHom _ _ (d.primary_trans (d.primes.symm p))) _ = _
    convert h using 1
    simp
  constructor
  · exact EvaluationDVR.valuation_prime _ _
  · intro l hl hr
    cases l with
    | inl j =>
      apply valuation_other_prime (d.primes j) p _
      intro h
      apply hl
      exact congrArg Sum.inl (d.primes.eq_symm_apply.mpr h)
    | inr q =>
      exact valuation_other_prime q p _ (fun h => hr (congrArg Sum.inr h))

section Generators
variable (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (d : Places)
local notation "W" => RawWords.normalizedFactor (fun i => algebraMap ℚ[X] (RatFunc ℚ) (F i)) E

/-- Raw guard-unit values imply the normalized guard values used below. -/
theorem normalized_guard_values
    (hraw : ∀ p i, vertical d (.inr p) (algebraMap ℚ[X] (RatFunc ℚ) (F i)) = 1) :
    ∀ p i, vertical d (.inr p) (W i) = 1 := by
  intro p i
  exact PrimaryIsolators.normalizedFactor_guard (vertical d (.inr p)) _ E (hraw p) i

/-- The actual normalized raw generators construct both members of every
primary/guard pair; pole membership and prime values have been discharged. -/
theorem paired_isolators
    (hb : ∀ n j, vertical d (.inl j) (W (NormalizedWords.Generator.b n).stage) =
      exp (-(PrimaryWordProfiles.bWeight n j)))
    (hq : ∀ n j, vertical d (.inl j) (W (NormalizedWords.Generator.q n).stage) =
      exp (-(PrimaryWordProfiles.qWeight n j)))
    (hw : ∀ p i, vertical d (.inr p) (W i) = 1) (p : PrimeIndex) :
    ∃ f g : domain (Set.range F) d,
      (f : RatFunc ℚ)⁻¹ ∈ PoleAlgebra.generated (Set.range F) ∧
      (g : RatFunc ℚ)⁻¹ ∈ PoleAlgebra.generated (Set.range F) ∧
      vertical d (.inl (d.primes.symm p)) f = exp (-3) ∧
      (∀ l, l ≠ .inl (d.primes.symm p) → vertical d l f = 1) ∧
      vertical d (.inr p) g = exp (-3) ∧
      (∀ l, l ≠ .inr p → vertical d l g = 1) ∧
      f * g = (p.val : domain (Set.range F) d) ^ 3 := by
  obtain ⟨hpi, hpj, hpother⟩ := prime_values d p
  have hpinv : (p.val : RatFunc ℚ)⁻¹ ∈ PoleAlgebra.generated (Set.range F) := by
    simpa only [map_inv₀, map_natCast] using
      (PoleAlgebra.generated (Set.range F)).algebraMap_mem ((p.val : ℚ)⁻¹)
  have h := PrimaryIsolators.exists_paired_isolators (PoleAlgebra.generated (Set.range F)).toSubring
    (fun j => vertical d (.inl j)) (fun p => vertical d (.inr p)) W hb hq
    (fun i => (PrimaryIsolators.normalizedFactor_pole_mem F E i).1)
    (fun i => (PrimaryIsolators.normalizedFactor_pole_mem F E i).2)
    hw (d.primes.symm p) p p.val hpinv hpi hpj
      (by simpa only [vertical_eq_sum] using hpother)
  rw [vertical_eq_sum] at h
  exact h

/-- Thus every actual defining vertical place has a singleton; none is assumed. -/
theorem vertical_isolators
    (hb : ∀ n j, vertical d (.inl j) (W (NormalizedWords.Generator.b n).stage) =
      exp (-(PrimaryWordProfiles.bWeight n j)))
    (hq : ∀ n j, vertical d (.inl j) (W (NormalizedWords.Generator.q n).stage) =
      exp (-(PrimaryWordProfiles.qWeight n j)))
    (hw : ∀ p i, vertical d (.inr p) (W i) = 1) (i : ℕ ⊕ PrimeIndex) :
    ∃ f : domain (Set.range F) d, (f : RatFunc ℚ)⁻¹ ∈ PoleAlgebra.generated (Set.range F) ∧
      vertical d i f = exp (-3) ∧ (∀ j, j ≠ i → vertical d j f = 1) := by
  cases i with
  | inl j =>
    have h := PrimaryIsolators.exists_primary_isolator (PoleAlgebra.generated (Set.range F)).toSubring
      (fun j => vertical d (.inl j)) (fun p => vertical d (.inr p)) W hb hq
      (fun i => (PrimaryIsolators.normalizedFactor_pole_mem F E i).1)
      (fun i => (PrimaryIsolators.normalizedFactor_pole_mem F E i).2) hw j
    rw [vertical_eq_sum] at h
    exact h
  | inr p =>
    obtain ⟨_, g, _, hginv, _, _, hgj, hgother, _⟩ := paired_isolators F E d hb hq hw p
    exact ⟨g, hginv, hgj, hgother⟩

/-- The literal paired principal ideals have exactly the two actual vertical
radicals needed to classify every prime over a rational prime. -/
theorem paired_radicals
    (hb : ∀ n j, vertical d (.inl j) (W (NormalizedWords.Generator.b n).stage) =
      exp (-(PrimaryWordProfiles.bWeight n j)))
    (hq : ∀ n j, vertical d (.inl j) (W (NormalizedWords.Generator.q n).stage) =
      exp (-(PrimaryWordProfiles.qWeight n j)))
    (hw : ∀ p i, vertical d (.inr p) (W i) = 1) (p : PrimeIndex) :
    ∃ f g : domain (Set.range F) d, ∃ k : ℕ, 0 < k ∧
      f * g = (p.val : domain (Set.range F) d) ^ k ∧
      (Ideal.span ({f} : Set (domain (Set.range F) d))).radical =
        center (PoleAlgebra.generated (Set.range F)).toSubring (vertical d) (.inl (d.primes.symm p)) ∧
      (Ideal.span ({g} : Set (domain (Set.range F) d))).radical =
        center (PoleAlgebra.generated (Set.range F)).toSubring (vertical d) (.inr p) := by
  obtain ⟨f, g, hfinv, hginv, hfi, hfother, hgj, hgother, hprod⟩ :=
    paired_isolators F E d hb hq hw p
  exact ⟨f, g, 3, by decide, hprod,
    radical_span_isolator _ _ _ f 3 (by decide) hfinv hfi hfother,
    radical_span_isolator _ _ _ g 3 (by decide) hginv hgj hgother⟩

/-- Actual primary/guard evaluations and normalized raw generators give every
maximal localization of the concrete paired domain as a DVR. No spectrum,
stalk-completeness, singleton, or paired-product hypothesis is supplied. -/
theorem every_maximal_stalk_isDVR
    (hF : ∀ i, constantCoeff (F i) ≠ 0)
    (hb : ∀ n j, vertical d (.inl j) (W (NormalizedWords.Generator.b n).stage) =
      exp (-(PrimaryWordProfiles.bWeight n j)))
    (hq : ∀ n j, vertical d (.inl j) (W (NormalizedWords.Generator.q n).stage) =
      exp (-(PrimaryWordProfiles.qWeight n j)))
    (hw : ∀ p i, vertical d (.inr p) (W i) = 1)
    (stage : PrimeIndex → ℕ) (hstage : ∀ n, {p | stage p ≤ n}.Finite)
    (havoid : ∀ p j, j < stage p →
      (integerPolynomialEnumeration j).val.eval₂ (Int.castRingHom (ZMod p.val))
        (PadicInt.toZMod (d.guard p)) ≠ 0)
    (M : Ideal (domain (Set.range F) d)) [M.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime M) := by
  have hconst : ∀ q ∈ Set.range F, constantCoeff q ≠ 0 := by
    rintro q ⟨i, rfl⟩
    exact hF i
  have hnonzero : ∀ q ∈ Set.range F, q ≠ 0 := by
    intro q hq hzero
    exact hconst q hq (by simp [hzero])
  let := PairedDomain.fractionRing (Set.range F) d
  let := PairedDomain.integerLocalization d stage hstage havoid hconst
  let := IntersectionSpectrum.poleAlgebra_isDedekindDomain (Set.range F) hnonzero
  apply IntersectionSpectrum.every_maximal_stalk_isDVR
    (PoleAlgebra.generated (Set.range F)).toSubring (vertical d)
    (fun p => .inl (d.primes.symm p)) (fun p => .inr p)
    (center_isMaximal (Set.range F) d) (vertical_isDVR d)
    (paired_radicals F E d hb hq hw) _ M
  intro i
  obtain ⟨f, hfinv, hfi, hfother⟩ := vertical_isolators F E d hb hq hw i
  exact ⟨f, 3, by decide, hfinv, hfi, hfother⟩

end Generators
end UnconditionalCounterexample.PairedSpectrum
