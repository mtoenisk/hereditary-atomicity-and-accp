import Factorization.Basic

/-!
# Bounded factorization, ACCP and atomicity

The bounded-factorization argument uses a strictly decreasing bound along
`DvdNotUnit`, without cancellation. Domain statements retain the nonzero-element
convention. ACCP is mathlib's well-founded strict-divisibility relation.
-/

namespace Factorization

universe u

section CommMonoidWithZero

variable {R : Type u} [CommMonoidWithZero R]

private theorem acc_dvdNotUnit_of_bound (N : ℕ) (x : R)
    (hN : ∀ s : Multiset R, (∀ p ∈ s, ¬ IsUnit p) →
      Associated s.prod x → s.card ≤ N) : Acc DvdNotUnit x := by
  induction N using Nat.strong_induction_on generalizing x with
  | h N ih =>
    refine Acc.intro x ?_
    rintro y ⟨_, a, ha, rfl⟩
    have hya : ¬ IsUnit (y * a) := fun hu => ha (isUnit_of_mul_isUnit_right hu)
    have hpos : 0 < N := by
      have hsingle := hN {y * a} (by simpa using hya) (by simp)
      simp only [Multiset.card_singleton] at hsingle
      omega
    apply ih (N - 1) (by omega) y
    intro s hs hsy
    have hnon : ∀ p ∈ a ::ₘ s, ¬ IsUnit p := by
      intro p hp
      rcases Multiset.mem_cons.mp hp with rfl | hp
      · exact ha
      · exact hs p hp
    have hprod : Associated (a ::ₘ s).prod (y * a) := by
      simpa only [Multiset.prod_cons, mul_comm y a] using hsy.mul_left a
    have hcard := hN (a ::ₘ s) hnon hprod
    rw [Multiset.card_cons] at hcard
    omega

/-- A bound on all nonunit factorizations makes strict divisibility below the
specified element accessible. Cancellation is not required. -/
theorem HasBoundedFactorizations.acc_dvdNotUnit {x : R}
    (hx : HasBoundedFactorizations x) : Acc DvdNotUnit x := by
  obtain ⟨N, hN⟩ := hx
  exact acc_dvdNotUnit_of_bound N x hN

/-- Bounded nonunit factorizations at every nonzero element imply ACCP.
The zero case is separate because predecessors for `DvdNotUnit` are nonzero. -/
theorem wfDvdMonoid_of_nonzero_hasBoundedFactorizations
    (hR : ∀ x : R, x ≠ 0 → HasBoundedFactorizations x) : WfDvdMonoid R := by
  refine ⟨fun x => ?_⟩
  by_cases hx : x = 0
  · subst x
    refine Acc.intro 0 ?_
    intro y hy
    exact (hR y hy.1).acc_dvdNotUnit
  · exact (hR x hx).acc_dvdNotUnit

/-- ACCP provides an atomic factorization of every nonzero element. -/
theorem hasAtomicFactorization_of_wfDvdMonoid (hR : WfDvdMonoid R)
    {x : R} (hx : x ≠ 0) : HasAtomicFactorization x := by
  let : WfDvdMonoid R := hR
  exact WfDvdMonoid.exists_factors x hx

/-- Failure of ACCP is witnessed by a chain of nonzero elements with nonunit
ratios. The first term of an arbitrary divisibility chain is dropped if needed
so that zero never occurs among the returned endpoints. -/
theorem not_wfDvdMonoid_iff_exists_nonunit_chain :
    ¬ WfDvdMonoid R ↔ ∃ x a : ℕ → R,
      (∀ n, x n ≠ 0) ∧ (∀ n, ¬ IsUnit (a n)) ∧
        ∀ n, x n = x (n + 1) * a n := by
  classical
  constructor
  · intro hR
    have hchain : ∃ f : ℕ → R, ∀ n, DvdNotUnit (f (n + 1)) (f n) := by
      simpa only [WfDvdMonoid, wellFounded_iff_isEmpty_descending_chain,
        not_isEmpty_iff, nonempty_subtype] using hR
    obtain ⟨f, hf⟩ := hchain
    choose a ha hea using fun n => (hf (n + 1)).2
    exact ⟨fun n => f (n + 1), a, fun n => (hf n).1, ha, hea⟩
  · rintro ⟨x, a, hx, ha, hxa⟩ hR
    let : WfDvdMonoid R := hR
    obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := DvdNotUnit) x
    exact hn ⟨hx (n + 1), a n, ha n, hxa n⟩

end CommMonoidWithZero

section Domains

variable {R : Type u} [CommRing R] [IsDomain R]

/-- Every BF domain satisfies ACCP. -/
theorem IsBFDomain.wfDvdMonoid (hR : IsBFDomain R) : WfDvdMonoid R :=
  wfDvdMonoid_of_nonzero_hasBoundedFactorizations hR

/-- Every domain satisfying ACCP is atomic. -/
theorem isAtomicDomain_of_wfDvdMonoid (hR : WfDvdMonoid R) : IsAtomicDomain R :=
  fun _ hx => hasAtomicFactorization_of_wfDvdMonoid hR hx

/-- Every BF domain is atomic. -/
theorem IsBFDomain.isAtomicDomain (hR : IsBFDomain R) : IsAtomicDomain R :=
  isAtomicDomain_of_wfDvdMonoid hR.wfDvdMonoid

end Domains

end Factorization
