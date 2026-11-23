import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Choosing auxiliary irreducibles in unsettled primes

Finite prime avoidance finds a polynomial in the prescribed prime outside all
forbidden primes. Factoring that same polynomial inside a UFD produces a prime
factor still outside every forbidden prime. This gives the punctures in the multivariate polynomial ring over the rationals.
-/

namespace UnconditionalCounterexample.Variations.PrivateGuards

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

omit [IsDomain A] in
private theorem prime_factor_in_ideal {P : Ideal A} [P.IsPrime] (f : A) (hf : f ≠ 0)
    (hp : f ∈ P) : ∃ g : A, Prime g ∧ g ∈ P ∧ g ∣ f := by
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hf rfl).elim
  | h₂ a ha => exact (Ideal.notMem_of_isUnit P ha hp).elim
  | h₃ a g ha hg ih =>
    rcases Ideal.IsPrime.mem_or_mem inferInstance hp with h | h
    · exact ⟨g, hg, h, dvd_mul_right _ _⟩
    · obtain ⟨q, hq, hqp, hqa⟩ := ih ha h
      exact ⟨q, hq, hqp, hqa.trans (dvd_mul_left _ _)⟩

/-- A prime ideal not contained in any of a finite collection of forbidden
prime ideals contains an irreducible avoiding all of them simultaneously. -/
theorem exists_puncture (P : Ideal A) [P.IsPrime] (hp : P ≠ ⊥)
    (V : Finset (Ideal A)) (hv : ∀ Q ∈ V, Q.IsPrime)
    (havoid : ∀ Q ∈ V, ¬ P ≤ Q) :
    ∃ g : A, Irreducible g ∧ g ∈ P ∧ ∀ Q ∈ V, g ∉ Q := by
  classical
  let V' := insert (⊥ : Ideal A) V
  have hprime (Q : Ideal A) (hQ : Q ∈ V') : Q.IsPrime := by
    rcases Finset.mem_insert.mp hQ with rfl | h
    · infer_instance
    · exact hv _ h
  have hnot (Q : Ideal A) (hQ : Q ∈ V') : ¬P ≤ Q := by
    rcases Finset.mem_insert.mp hQ with rfl | h
    · simpa using hp
    · exact havoid _ h
  have hex : ¬ (P : Set A) ⊆ ⋃ Q ∈ (↑V' : Set (Ideal A)), (Q : Set A) := by
    intro h
    obtain ⟨Q,hQ,hle⟩ := (Ideal.subset_union_prime (f := id) (⊥ : Ideal A) ⊥
      (fun Q hQ _ _ => hprime Q hQ)).mp h
    exact hnot Q hQ hle
  obtain ⟨f, hfp, hf⟩ := Set.not_subset.mp hex
  have hav (Q : Ideal A) (hQ : Q ∈ V') : f ∉ Q :=
    fun h => hf (Set.mem_iUnion.mpr ⟨Q, Set.mem_iUnion.mpr ⟨hQ, h⟩⟩)
  have hf0 : f ≠ 0 := by simpa using hav ⊥ (Finset.mem_insert_self ..)
  obtain ⟨g, hg, hgp, hgf⟩ := prime_factor_in_ideal f hf0 hfp
  exact ⟨g, hg.irreducible, hgp, fun Q hQ hgQ =>
    hav Q (Finset.mem_insert_of_mem hQ) (Q.mem_of_dvd hgf hgQ)⟩

/-- In particular a target of strictly larger height than each forbidden prime
admits a new irreducible, preserving the retained prime and all the tests. -/
theorem exists_puncture_of_height (P : Ideal A) [P.IsPrime] (hp : P ≠ ⊥)
    (V : Finset (Ideal A)) (hv : ∀ Q ∈ V, Q.IsPrime)
    (hheight : ∀ Q ∈ V, Q.height < P.height) :
    ∃ g : A, Irreducible g ∧ g ∈ P ∧ ∀ Q ∈ V, g ∉ Q :=
  exists_puncture P hp V hv fun Q hQ h => (hheight Q hQ).not_ge (Ideal.height_mono h)

/-- A puncture in an ideal of height greater than one can avoid the retained
prime and every irreducible divisor of a finite collection of nonzero tests. -/
theorem exists_puncture_avoiding_tests [IsNoetherianRing A] [NormalizationMonoid A]
    (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (hp : P ≠ ⊥)
    (hQ : Q.height < P.height) (h1 : 1 < P.height)
    (tests : Finset A) (ht : ∀ f ∈ tests, f ≠ 0) :
    ∃ g : A, Irreducible g ∧ g ∈ P ∧ g ∉ Q ∧ ∀ f ∈ tests, ¬ g ∣ f := by
  classical
  let fs := tests.biUnion fun f => (UniqueFactorizationMonoid.normalizedFactors f).toFinset
  let qs := fs.image fun f => Ideal.span ({f} : Set A)
  have hprime (f : A) (hf : f ∈ fs) : Prime f := by
    obtain ⟨t, _, h⟩ := Finset.mem_biUnion.mp hf
    exact UniqueFactorizationMonoid.prime_of_normalized_factor _ (Multiset.mem_toFinset.mp h)
  have hi (J : Ideal A) (hJ : J ∈ qs) :
      J.IsPrime ∧ J.height < P.height := by
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hJ
    exact ⟨Ideal.isPrime_span_singleton_of_prime (hprime _ hf),
      (Ideal.height_span_singleton_le_one (hprime _ hf).not_isUnit).trans_lt h1⟩
  obtain ⟨g, hg, hgP, hav⟩ := exists_puncture_of_height P hp (insert Q qs)
    (fun J hJ => (Finset.mem_insert.mp hJ).elim (fun h => h ▸ inferInstanceAs Q.IsPrime)
      (fun h => (hi J h).1))
    (fun J hJ => (Finset.mem_insert.mp hJ).elim (fun h => h ▸ hQ) (fun h => (hi J h).2))
  refine ⟨g, hg, hgP, hav Q (Finset.mem_insert_self ..), ?_⟩
  intro f hf hgf
  obtain ⟨u, hu, hgu⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
    (ht f hf) hg hgf
  have hmem : u ∈ fs := Finset.mem_biUnion.mpr ⟨f, hf, Multiset.mem_toFinset.mpr hu⟩
  exact hav _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hmem))
    (Ideal.mem_span_singleton.mpr hgu.symm.dvd)

end UnconditionalCounterexample.Variations.PrivateGuards
