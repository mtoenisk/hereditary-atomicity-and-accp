import UnconditionalCounterexample.Variations.MultivariateFibres
import UnconditionalCounterexample.GeometricReservations

/-!
# Retained points on surviving prime loci

At the stage indexing a prime, protect a point of its zero locus avoiding the
previous factors. Its existence follows from primeness and the
Nullstellensatz. Subsequent stages only see a finite list of earlier
reservations. This produces the retained points used to recover the localized polynomial ring.
-/

namespace UnconditionalCounterexample.MultivariateReservations

open MvPolynomial MultivariateFibres

variable {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ]

theorem exists_point_avoiding (P : Ideal (MvPolynomial σ k)) (hP : P.IsPrime)
    (s : Finset (MvPolynomial σ k)) (hs : ∀ f ∈ s, f ∉ P) :
    ∃ u : σ → k, P ≤ pointIdeal u ∧ ∀ f ∈ s, eval u f ≠ 0 := by
  classical
  let : P.IsPrime := hP
  by_contra h
  have hprod : (∏ p ∈ s, p) ∈ P := by
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := k) P]
    intro u hu
    by_contra hne
    apply h
    refine ⟨u, fun p hp => hu p hp, ?_⟩
    simp only [map_prod] at hne
    exact Finset.prod_ne_zero_iff.mp hne
  obtain ⟨f,hf,hmem⟩ := (hP.prod_mem_iff_exists_mem s).mp hprod
  exact hs f hf hmem

omit [IsAlgClosed k] in
/-- The prime-ideal enumeration exists over the countable algebraic closure
used by the construction because each ideal has a finite set of generators. -/
theorem exists_ideal_enumeration [Countable k] :
    ∃ p : ℕ → Ideal (MvPolynomial σ k), Function.Surjective p := by
  classical
  let : Countable σ := inferInstance
  have h : Function.Surjective (fun s : Finset (MvPolynomial σ k) => Ideal.span (s : Set (MvPolynomial σ k))) := by
    intro P
    exact (IsNoetherian.noetherian P)
  let : Countable (Ideal (MvPolynomial σ k)) := h.countable
  exact exists_surjective_nat _

/-- The finite set of prior raw factors at the instant the prime is considered. -/
noncomputable def earlier (F : ℕ → MvPolynomial σ k) (n : ℕ) : Finset (MvPolynomial σ k) := by
  classical exact (Finset.range n).image F

/-- An eligible prime receives a witness depending only on its previous factors.
An omitted prime needs no witness and gets the empty finite set. -/
noncomputable def reserve (P : Ideal (MvPolynomial σ k)) (s : Finset (MvPolynomial σ k)) :
    Finset (σ → k) := by
  classical
  exact if h : P.IsPrime ∧ ∀ f ∈ s, f ∉ P then
    {(exists_point_avoiding P h.1 s h.2).choose} else ∅

private theorem reserve_spec (P : Ideal (MvPolynomial σ k)) (hP : P.IsPrime)
    (s : Finset (MvPolynomial σ k)) (hs : ∀ f ∈ s, f ∉ P) :
    ∃ u ∈ reserve P s, P ≤ pointIdeal u ∧ ∀ f ∈ s, eval u f ≠ 0 := by
  classical
  have h : P.IsPrime ∧ ∀ f ∈ s, f ∉ P := ⟨hP,hs⟩
  rw [reserve, dite_eq_left h]
  simp only [Finset.mem_singleton, exists_eq_left]
  exact (exists_point_avoiding P hP s hs).choose_spec

/-- All the prime-locus tests at one stage are finite. -/
noncomputable def reserved (P : ℕ → Ideal (MvPolynomial σ k)) (F : ℕ → MvPolynomial σ k)
    (n : ℕ) : Finset (σ → k) := by
  classical exact (Finset.range (n+1)).biUnion (fun i => reserve (P i) (earlier F i))

/-- If the current polynomial avoids the finite accumulated reservations, every
prime disjoint from the final denominator monoid has a retained point. -/
theorem retained_points (P : ℕ → Ideal (MvPolynomial σ k)) (hP : Function.Surjective P)
    (F : ℕ → MvPolynomial σ k) (hF : ∀ n u, u ∈ reserved P F n → eval u (F n) ≠ 0)
    (Q : Ideal (MvPolynomial σ k)) (hQ : Q.IsPrime)
    (hdisj : Disjoint ((Submonoid.closure (Set.range F)) : Set (MvPolynomial σ k))
      (Q : Set (MvPolynomial σ k))) :
    ∃ u : σ → k, Retained (Submonoid.closure (Set.range F)) u ∧ Q ≤ pointIdeal u := by
  classical
  obtain ⟨n, hn⟩ := hP Q
  have hex (f : MvPolynomial σ k) (hf : f ∈ earlier F n) : f ∉ P n := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    rw [hn]
    exact Set.disjoint_left.mp hdisj (Submonoid.subset_closure ⟨i,rfl⟩)
  obtain ⟨u, hu, hle, hprev⟩ := reserve_spec (P n) (hn ▸ hQ) (earlier F n) hex
  refine ⟨u, ?_, hn ▸ hle⟩
  have hnon (i : ℕ) : eval u (F i) ≠ 0 := by
    by_cases hi : i < n
    · exact hprev _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi,rfl⟩)
    · apply hF i u
      exact Finset.mem_biUnion.mpr ⟨n,Finset.mem_range.mpr (by omega),hu⟩
  intro q
  obtain ⟨f,hf⟩ := q
  change eval u f ≠ 0
  induction hf using Submonoid.closure_induction with
  | mem f hf => obtain ⟨i,rfl⟩ := hf; exact hnon i
  | one => simp
  | mul a b _ _ ha hb => simpa using mul_ne_zero ha hb

end UnconditionalCounterexample.MultivariateReservations
