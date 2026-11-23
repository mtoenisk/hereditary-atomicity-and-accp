import UnconditionalCounterexample.Variations.MultiDomainVerticalResidues
import UnconditionalCounterexample.Variations.MultiDomainDimension
import UnconditionalCounterexample.Variations.MultiDomainLowWords
import UnconditionalCounterexample.PrimaryIsolators
import UnconditionalCounterexample.IntersectionSpectrum
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Height

/-! # Vertical primes and exact dimension of the ordinary multivariate domain

At selected primes the primary and guard isolators multiply to the cube of
the rational prime. At an omitted prime the prime itself isolates its unique
guard. Their radical ideals account for every vertical prime, and localization
identifies each stalk with the corresponding rank-one discrete valuation ring.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open GuardSupport WithZero IntersectionStalks IntersectionDomain NormalizedWords PrimaryWordProfiles

variable {r : ℕ} (A : Data r)

/-- The actual normalized functions are units of the horizontal localization. -/
theorem normalized_pole_mem (E : ℕ → ℕ) (i : ℕ) :
    RawWords.normalizedFactor (rawValue A) E i ∈ poleAlgebra A ∧
    (RawWords.normalizedFactor (rawValue A) E i)⁻¹ ∈ poleAlgebra A := by
  have hr n : rawValue A n ∈ poleAlgebra A := (poleAlgebra A).algebraMap_mem _
  have hi n : (rawValue A n)⁻¹ ∈ poleAlgebra A := by
    exact ⟨1,A.raw n,Submonoid.subset_closure (Set.mem_range_self n),by simp [rawValue]⟩
  exact ⟨PrimaryIsolators.normalizedFactor_mem (poleAlgebra A).toSubring _ E hr hi i,
    PrimaryIsolators.normalizedFactor_inv_mem (poleAlgebra A).toSubring _ E hr hi i⟩

/-- The valuation columns for the triangularly normalized raw generators. -/
structure VerticalProfiles (E : ℕ → ℕ) : Prop where
  b : ∀ n j, A.primary j (RawWords.normalizedFactor (rawValue A) E (Generator.b n).stage) =
    exp (-bWeight n j)
  q : ∀ n j, A.primary j (RawWords.normalizedFactor (rawValue A) E (Generator.q n).stage) =
    exp (-qWeight n j)
  guard : ∀ p i, A.guard p (RawWords.normalizedFactor (rawValue A) E i) = 1

private def firstPlace (picks : ℕ → PrimeIndex) (p : PrimeIndex) : ℕ ⊕ PrimeIndex := by
  classical
  exact if h : p ∈ Set.range picks then .inl h.choose else .inr p

private theorem firstPlace_selected {picks : ℕ → PrimeIndex} (hi : Function.Injective picks) (j : ℕ) :
    firstPlace picks (picks j) = .inl j := by
  classical
  have h : picks j ∈ Set.range picks := ⟨j,rfl⟩
  simp [firstPlace, h, hi h.choose_spec]

private def Isolates (i : ℕ ⊕ PrimeIndex) (f : ordinary A) (k : ℕ) : Prop :=
  (f : FunctionField r)⁻¹ ∈ poleAlgebra A ∧ vertical A i f = exp (-(k : ℤ)) ∧
    ∀ l, l ≠ i → vertical A l f = 1

private theorem isolators_at_prime {A : Data r} {E : ℕ → ℕ}
    (V : VerticalProfiles A E) (H : Clearing A) (hinj : Function.Injective H.primes)
    (p : PrimeIndex) :
    ∃ f g : ordinary A, ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      Isolates A (firstPlace H.primes p) f k ∧ Isolates A (.inr p) g k ∧
      f * g = (p.val : ordinary A)^l := by
  classical
  have hpinv : (p.val : FunctionField r)⁻¹ ∈ poleAlgebra A := by
    have hc := (poleAlgebra A).algebraMap_mem (MvPolynomial.C ((p.val : ℚ)⁻¹))
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, map_inv₀, map_natCast] at hc
    exact hc
  by_cases hp : p ∈ Set.range H.primes
  · obtain ⟨j,rfl⟩ := hp
    obtain ⟨f,g,hfi,hgi,hfj,hfo,hgj,hgo,hfg⟩ :=
      PrimaryIsolators.exists_paired_isolators (poleAlgebra A).toSubring A.primary A.guard _
        V.b V.q (fun i => (normalized_pole_mem A E i).1) (fun i => (normalized_pole_mem A E i).2)
        V.guard j (H.primes j) (H.primes j).val hpinv (H.primary_prime j) (H.guard_prime _) (by
          rintro (k | q) h₁ h₂
          · exact other_prime_value _ (H.primes k) (H.primes j) (H.primary_prime k)
              (fun he => h₁ (congrArg Sum.inl (hinj he)))
          · exact other_prime_value _ q (H.primes j) (H.guard_prime q)
              (fun he => h₂ (congrArg Sum.inr he)))
    rw [firstPlace_selected hinj]
    exact ⟨f,g,3,3,by decide,by decide,⟨hfi,hfj,hfo⟩,⟨hgi,hgj,hgo⟩,hfg⟩
  · simp only [firstPlace, hp, ↓reduceDIte]
    have h : Isolates A (.inr p) (p.val : ordinary A) 1 := by
      refine ⟨hpinv,H.guard_prime p,?_⟩
      rintro (j | q) h
      · exact other_prime_value _ (H.primes j) p (H.primary_prime j) (fun he => hp ⟨j,he⟩)
      · exact other_prime_value _ q p (H.guard_prime q) (fun he => h (congrArg Sum.inr he))
    exact ⟨_,_,1,2,by decide,by decide,h,h,(sq _).symm⟩

/-- Every vertical prime is a maximal centre with a DVR stalk and height one. -/
theorem vertical_height_one {A : Data r} [IsFractionRing (ordinary A) (FunctionField r)]
    {E : ℕ → ℕ} (V : VerticalProfiles A E) (H : Clearing A) (hinj : Function.Injective H.primes)
    (hmax : ∀ i, (center (poleAlgebra A).toSubring (vertical A) i).IsMaximal)
    (t : PrimeSpectrum (ordinary A))
    (ht : ¬ Disjoint (integerDenominators (ordinary A) : Set (ordinary A)) t.asIdeal) :
    Order.height t = 1 := by
  let B := (poleAlgebra A).toSubring
  let v := vertical A
  have hpair (p : PrimeIndex) := isolators_at_prime V H hinj p
  have hrad (p : PrimeIndex) :
      ∃ f g : ordinary A, ∃ k : ℕ, 0 < k ∧ f * g = (p.val : ordinary A)^k ∧
        (Ideal.span ({f} : Set (ordinary A))).radical = center B v (firstPlace H.primes p) ∧
        (Ideal.span ({g} : Set (ordinary A))).radical = center B v (.inr p) := by
    obtain ⟨f,g,k,l,hk,hl,hf,hg,hfg⟩ := hpair p
    exact ⟨f,g,l,hl,hfg,radical_span_isolator _ _ _ _ k hk hf.1 hf.2.1 hf.2.2,
      radical_span_isolator _ _ _ _ k hk hg.1 hg.2.1 hg.2.2⟩
  obtain ⟨i,hi⟩ := (@IntersectionSpectrum.prime_vertical_or_disjoint (FunctionField r) _ _ B v
    (firstPlace H.primes) Sum.inr hmax hrad t.asIdeal t.isPrime).resolve_right ht
  have hiso : ∃ f : ordinary A, ∃ k, 0 < k ∧ Isolates A i f k := by
    cases i with
    | inl j =>
      obtain ⟨f,_,k,_,hk,_,hf,_,_⟩ := hpair (H.primes j)
      exact ⟨f,k,hk,firstPlace_selected hinj j ▸ hf⟩
    | inr p =>
      obtain ⟨_,g,k,_,hk,_,_,hg,_⟩ := hpair p
      exact ⟨g,k,hk,hg⟩
  obtain ⟨f,k,hk,hf⟩ := hiso
  let : IsDiscreteValuationRing (v i).valuationSubring := by
    cases i with
    | inl j => exact isDVR_of_prime_value _ (H.primary_prime j)
    | inr p => exact isDVR_of_prime_value _ (H.guard_prime p)
  let : IsFractionRing (intersection B v) (FunctionField r) := inferInstanceAs
    (IsFractionRing (ordinary A) (FunctionField r))
  let := stalk_isDVR B v i f k hk hf.1 hf.2.1 hf.2.2
  have he := (IsLocalization.AtPrime.ringKrullDim_eq_height (center B v i)
    (Localization.AtPrime (center B v i))).symm.trans (IsDiscreteValuationRing.ringKrullDim_eq_one _)
  exact t.height_eq_orderHeight.symm.trans ((congrArg Ideal.height hi).trans (WithBot.coe_injective he))

/-- The actual ordinary intersection has dimension equal to the number of
variables when its normalized profiles and finite-residue guard models are supplied. -/
theorem Places.ordinary_dimension_of_profiles (P : Places (r+1)) (F : ℕ → Polys (r+1))
    (hF : ∀ n, F n ≠ 0) (c : Fin (r+1) → ℚ)
    (hc : MultivariateFibres.Retained (denominators (P.data F hF)) c)
    {E : ℕ → ℕ} (V : VerticalProfiles (P.data F hF) E) (H : Clearing (P.data F hF))
    (hinj : Function.Injective H.primes)
    (hg : ∀ p, Finite (IsLocalRing.ResidueField (P.guardVal p).valuationSubring)) :
    ringKrullDim (ordinary (P.data F hF)) = (r+1 : ℕ) := by
  let := P.ordinary_fraction F hF
  apply ordinary_dimension c hc H
  intro t ht
  rw [vertical_height_one V H hinj (P.centers_maximal F hF hg) t ht]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)

end UnconditionalCounterexample.Variations.MultiDomain
