import HereditaryAtomicity.DVRBase.MultiplaceDescentFiber
import HereditaryAtomicity.DVRBase.JointSelectionBox

/-! Proper recurrent support for actual singleton-component support descent. -/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped nonZeroDivisors BigOperators
variable {R : Type*} [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R]

/-- Natural component weights with both a zero and a positive coordinate
produce a strict source chain on a nonempty proper recurrent set. -/
theorem exists_proper_recurrent_chain_of_weighted_component_fiber
    (S : Finset (MaximalSpectrum R)) (π : S → R)
    (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hfinite : Set.Finite {P : MaximalSpectrum R | x 0 ∈ P.asIdeal})
    (hrecur : ∀ P : S, Set.Infinite {n | t n ∈ P.val.asIdeal})
    (e : S → ℕ) (hezero : ∃ P, e P = 0) (hepos : ∃ P, 0 < e P)
    (γ : ClassGroup R)
    (hγ : Set.Infinite {n | (∏ P : S, componentClassHom (hU P)
      ⟨x n, mem_nonZeroDivisors_of_ne_zero (hx n)⟩ ^ e P) = γ}) :
    ∃ (S' : Finset (MaximalSpectrum R)) (n₀ : ℕ) (c a : ℕ → R),
      S'.Nonempty ∧ S' ⊂ S ∧ (∀ n, c n ≠ 0) ∧ c 0 = x n₀ ^ ∑ P, e P ∧
      (∀ n, c n = c (n + 1) * a n) ∧ (∀ n, ¬ IsUnit (a n)) ∧
      Set.Finite {P : MaximalSpectrum R | c 0 ∈ P.asIdeal} ∧
      (∀ n (P : MaximalSpectrum R), a n ∈ P.asIdeal ↔ P ∈ S') ∧
      ∀ P : MaximalSpectrum R, Set.Infinite {n | a n ∈ P.asIdeal} ↔ P ∈ S' := by
  classical
  let S' := (Finset.univ.filter fun P : S => 0 < e P).image Subtype.val
  have hmem (P : MaximalSpectrum R) : P ∈ S' ↔ ∃ Q : S, 0 < e Q ∧ P = Q.val := by
    simp only [S', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨Q, he, hQ⟩ <;> exact ⟨Q, he, hQ.symm⟩
  have hne : S'.Nonempty := by
    obtain ⟨P, he⟩ := hepos
    exact ⟨P.val, (hmem P.val).mpr ⟨P, he, rfl⟩⟩
  have hsub : S' ⊂ S := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro P hP
      obtain ⟨Q, _, rfl⟩ := (hmem P).mp hP
      exact Q.property
    · intro heq
      obtain ⟨P, he⟩ := hezero
      have hP : P.val ∈ S' := heq.symm ▸ P.property
      obtain ⟨Q, hQ, hQP⟩ := (hmem P.val).mp hP
      have hPQ : P = Q := Subtype.ext hQP
      rw [← hPQ, he] at hQ
      omega
  obtain ⟨n₀, c, a, hc, hc0, hca, hnonunit, hcfinite, hasupp⟩ :=
    exists_strict_chain_of_infinite_weighted_component_fiber π (fun P : S => {P.val}) hU e
      x t hx hxt hfinite γ hγ (by
        obtain ⟨P, he⟩ := hepos
        exact ⟨P, P.val, he, Set.mem_singleton _, hrecur P⟩)
  have hs (n : ℕ) (P : MaximalSpectrum R) : a n ∈ P.asIdeal ↔ P ∈ S' := by
    rw [hasupp, hmem]
    constructor
    · rintro ⟨Q, he, hP, _⟩
      exact ⟨Q, he, Set.mem_singleton_iff.mp hP⟩
    · rintro ⟨Q, he, rfl⟩
      exact ⟨Q, he, Set.mem_singleton _, hrecur Q⟩
  refine ⟨S', n₀, c, a, hne, hsub, hc, hc0, hca, hnonunit, hcfinite, hs, ?_⟩
  intro P
  simp only [hs]
  by_cases hP : P ∈ S'
  · simp only [hP, Set.ofPred_true, iff_true]
    exact Set.infinite_univ
  · simp only [hP, Set.ofPred_false, iff_false]
    exact Set.finite_empty.not_infinite

end HereditaryAtomicity.DVRBase
