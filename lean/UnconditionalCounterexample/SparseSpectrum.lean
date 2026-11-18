import UnconditionalCounterexample.SparsePrimaryDomain

/-!
# The maximal localizations for a selected set of primary primes

A selected prime has the two cubic isolators of the paired construction.
At every other prime, the rational prime itself isolates the guard with order
one. Using it twice in the radical product gives the same prime dichotomy for
all maximal ideals, including the horizontal centers after integer localization.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseSpectrum
open WithZero Polynomial GuardSupport SparsePrimaryDomain IntersectionDomain IntersectionStalks
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

theorem vertical_eq_sum (d : Places) :
    Sum.elim (fun j => vertical d (.inl j)) (fun p => vertical d (.inr p)) = vertical d := by
  funext i
  cases i <;> rfl

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


/-- First center above a rational prime. At an omitted prime both centers are its guard. -/
def firstCenter (d : Places) (p : PrimeIndex) : ℕ ⊕ PrimeIndex := by
  classical
  exact if h : p ∈ Set.range d.primes then .inl h.choose else .inr p

@[simp] theorem firstCenter_selected (d : Places) (j : ℕ) :
    firstCenter d (d.primes j) = .inl j := by
  classical
  have h : d.primes j ∈ Set.range d.primes := ⟨j, rfl⟩
  simp [firstCenter, h]

theorem firstCenter_unpaired (d : Places) (p : PrimeIndex) (hp : p ∉ Set.range d.primes) :
    firstCenter d p = .inr p := by
  classical
  simp [firstCenter, hp]

theorem selected_prime_values (d : Places) (j : ℕ) :
    vertical d (.inl j) ((d.primes j).val : RatFunc ℚ) = exp (-1) ∧
    vertical d (.inr (d.primes j)) ((d.primes j).val : RatFunc ℚ) = exp (-1) ∧
    (∀ l, l ≠ .inl j → l ≠ .inr (d.primes j) →
      vertical d l ((d.primes j).val : RatFunc ℚ) = 1) := by
  refine ⟨EvaluationDVR.valuation_prime _ _, EvaluationDVR.valuation_prime _ _, ?_⟩
  rintro (k | q) hl hr
  · exact PairedSpectrum.valuation_other_prime (d.primes k) (d.primes j) _
      (fun h => hl (congrArg Sum.inl (d.primes.injective h)))
  · exact PairedSpectrum.valuation_other_prime q (d.primes j) _ (fun h => hr (congrArg Sum.inr h))

section Generators
variable (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (d : Places)
local notation "W(" f "," e ")" => RawWords.normalizedFactor (fun i => algebraMap ℚ[X] (RatFunc ℚ) (f i)) e
variable
    (hb : ∀ n j, vertical d (.inl j) (W(F,E) (NormalizedWords.Generator.b n).stage) =
      exp (-(PrimaryWordProfiles.bWeight n j)))
    (hq : ∀ n j, vertical d (.inl j) (W(F,E) (NormalizedWords.Generator.q n).stage) =
      exp (-(PrimaryWordProfiles.qWeight n j)))
    (hw : ∀ p i, vertical d (.inr p) (W(F,E) i) = 1)

def Isolates (i : ℕ ⊕ PrimeIndex) (f : domain (Set.range F) d) (k : ℕ) : Prop :=
  (f : RatFunc ℚ)⁻¹ ∈ PoleAlgebra.generated (Set.range F) ∧
  vertical d i f = exp (-(k : ℤ)) ∧ ∀ l, l ≠ i → vertical d l f = 1

include hb hq hw in
theorem isolating_pair (p : PrimeIndex) :
    ∃ f g : domain (Set.range F) d, ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      Isolates F d (firstCenter d p) f k ∧ Isolates F d (.inr p) g k ∧
      f * g = (p.val : domain (Set.range F) d) ^ l := by
  have hpinv : (p.val : RatFunc ℚ)⁻¹ ∈ PoleAlgebra.generated (Set.range F) := by
    simpa only [map_inv₀, map_natCast] using
      (PoleAlgebra.generated (Set.range F)).algebraMap_mem ((p.val : ℚ)⁻¹)
  by_cases hp : p ∈ Set.range d.primes
  · obtain ⟨j, rfl⟩ := hp
    obtain ⟨hpi, hpj, hpother⟩ := selected_prime_values d j
    have h := PrimaryIsolators.exists_paired_isolators (PoleAlgebra.generated (Set.range F)).toSubring
      (fun j => vertical d (.inl j)) (fun p => vertical d (.inr p)) W(F,E) hb hq
      (fun i => (PrimaryIsolators.normalizedFactor_pole_mem F E i).1)
      (fun i => (PrimaryIsolators.normalizedFactor_pole_mem F E i).2)
      hw j (d.primes j) (d.primes j).val hpinv hpi hpj
        (by simpa only [vertical_eq_sum] using hpother)
    rw [vertical_eq_sum] at h
    obtain ⟨f, g, hfinv, hginv, hfi, hfo, hgi, hgo, hprod⟩ := h
    rw [firstCenter_selected]
    exact ⟨f, g, 3, 3, by decide, by decide, ⟨hfinv, hfi, hfo⟩, ⟨hginv, hgi, hgo⟩, hprod⟩
  · obtain ⟨hpi, hpo⟩ := unpaired_prime_profile d p hp
    rw [firstCenter_unpaired d p hp]
    have h : Isolates F d (.inr p) (p.val : domain (Set.range F) d) 1 := ⟨hpinv, hpi, hpo⟩
    exact ⟨_, _, 1, 2, by decide, by decide, h, h, (sq _).symm⟩

include hb hq hw in
theorem vertical_isolators (i : ℕ ⊕ PrimeIndex) :
    ∃ f : domain (Set.range F) d, ∃ k : ℕ, 0 < k ∧ Isolates F d i f k := by
  cases i with
  | inl j =>
    obtain ⟨f, _, k, _, hk, _, hf, _, _⟩ := isolating_pair F E d hb hq hw (d.primes j)
    exact ⟨f, k, hk, firstCenter_selected d j ▸ hf⟩
  | inr p =>
    obtain ⟨_, g, k, _, hk, _, _, hg, _⟩ := isolating_pair F E d hb hq hw p
    exact ⟨g, k, hk, hg⟩

include hb hq hw in
theorem paired_radicals (p : PrimeIndex) :
    ∃ f g : domain (Set.range F) d, ∃ k : ℕ, 0 < k ∧
      f * g = (p.val : domain (Set.range F) d) ^ k ∧
      (Ideal.span ({f} : Set (domain (Set.range F) d))).radical =
        center (PoleAlgebra.generated (Set.range F)).toSubring (vertical d) (firstCenter d p) ∧
      (Ideal.span ({g} : Set (domain (Set.range F) d))).radical =
        center (PoleAlgebra.generated (Set.range F)).toSubring (vertical d) (.inr p) := by
  obtain ⟨f, g, k, l, hk, hl, hf, hg, hprod⟩ := isolating_pair F E d hb hq hw p
  exact ⟨f, g, l, hl, hprod, radical_span_isolator _ _ _ f k hk hf.1 hf.2.1 hf.2.2,
    radical_span_isolator _ _ _ g k hk hg.1 hg.2.1 hg.2.2⟩

include hb hq hw in
theorem every_maximal_stalk_isDVR (hF : ∀ i, constantCoeff (F i) ≠ 0)
    (hguard : ∀ x : RatFunc ℚ, x ≠ 0 → {p : PrimeIndex | vertical d (.inr p) x ≠ 1}.Finite)
    (M : Ideal (domain (Set.range F) d)) [M.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime M) := by
  have hconst : ∀ f ∈ Set.range F, constantCoeff f ≠ 0 := by
    rintro _ ⟨i, rfl⟩
    exact hF i
  have hnonzero : ∀ f ∈ Set.range F, f ≠ 0 := by
    rintro f hf rfl
    exact hconst 0 hf (by simp)
  let := SparsePrimaryDomain.fractionRing (Set.range F) d
  let := integerLocalization_of_guard_support d hconst hguard
  let := IntersectionSpectrum.poleAlgebra_isDedekindDomain (Set.range F) hnonzero
  apply IntersectionSpectrum.every_maximal_stalk_isDVR
    (PoleAlgebra.generated (Set.range F)).toSubring (vertical d)
    (firstCenter d) Sum.inr (center_isMaximal _ d) (vertical_isDVR d)
    (paired_radicals F E d hb hq hw) _ M
  intro i
  obtain ⟨f, k, hk, hf⟩ := vertical_isolators F E d hb hq hw i
  exact ⟨f, k, hk, hf⟩

end Generators
end UnconditionalCounterexample.SparseSpectrum
