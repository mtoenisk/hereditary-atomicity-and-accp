import UnconditionalCounterexample.Variations.MultivariateStage
import UnconditionalCounterexample.Variations.MultivariateReservations
import UnconditionalCounterexample.Variations.MultivariateProperIntersection

/-!
# Finite test lists for multivariate raw-polynomial selection

Tests at stage `n` use only earlier factors, finitely many enumerated
points, directions and the word denominators at that stage. Every retained
pair and every nonzero tangent direction is eventually tested for all
listed words. A union of the finite earlier intersections supplies exactly
the point exclusions needed to avoid a common zero of `r+1` raws.
-/

namespace UnconditionalCounterexample.MultivariateSchedule

open MvPolynomial MultivariateStage MultivariateFibres
open MultivariateReservations MultivariateProperIntersection

variable {k σ : Type*} [Field k] [Fintype σ]

/-- Earlier `r`-fold intersections whose points must be avoided at stage `n`. -/
def crossings (F : ℕ → MvPolynomial σ k) (r n : ℕ) : Set (σ → k) :=
  ⋃ s ∈ (Finset.range n).powersetCard r, {u | ∀ i ∈ s, eval u (F i) = 0}

theorem finite_crossings (F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ) (r n : ℕ)
    (hl : ∀ i < n, (l i).totalDegree ≤ 1)
    (htop : ∀ i < n, ∃ p : MvPolynomial σ k, p.totalDegree < d i ∧ F i = l i ^ d i + p)
    (hlin : ∀ s : Finset ℕ, s ⊆ Finset.range n → s.card = r → ∀ j : σ,
      ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i) : (crossings F r n).Finite := by
  apply Set.Finite.biUnion (Finset.finite_toSet _)
  intro s hs
  obtain ⟨hsub,hc⟩ := Finset.mem_powersetCard.mp hs
  exact finite_common_zeros s F l d (fun i hi => hl i (Finset.mem_range.mp (hsub hi)))
    (fun i hi => htop i (Finset.mem_range.mp (hsub hi))) (hlin s hsub hc)

omit [Fintype σ] in
theorem no_common_zero (F : ℕ → MvPolynomial σ k) (r : ℕ)
    (havoid : ∀ n u, u ∈ crossings F r n → eval u (F n) ≠ 0)
    (s : Finset ℕ) (hs : s.card = r + 1) (u : σ → k) : ∃ i ∈ s, eval u (F i) ≠ 0 := by
  classical
  by_contra! hall
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  let n := s.max' hne
  have hn : n ∈ s := Finset.max'_mem _ _
  have hsmall : s.erase n ⊆ Finset.range n := by
    intro i hi
    obtain ⟨hne, hi⟩ := Finset.mem_erase.mp hi
    exact Finset.mem_range.mpr (lt_of_le_of_ne (Finset.le_max' _ _ hi) hne)
  have hcross : u ∈ crossings F r n := by
    apply Set.mem_iUnion.mpr
    refine ⟨s.erase n, Set.mem_iUnion.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsmall,?_⟩,?_⟩⟩
    · simp [Finset.card_erase_of_mem hn, hs]
    · exact fun i hi => hall i (Finset.mem_of_mem_erase hi)
  exact havoid n u hcross (hall n hn)

/-- Exact pair and direction tests for the current word list, together with
whatever finite point set the proper-intersection and prime reservations require. -/
noncomputable def tests (point : ℕ → σ → k) (n : ℕ) (protect : Finset (σ → k))
    (W : Finset (ℕ × MvPolynomial σ k)) : Finset (Test k σ) := by
  classical
  let S := (Finset.range (n+1)).image point
  let pairs := (S ×ˢ S) ×ˢ W
  exact ((protect.image Test.point ∪ pairs.image (fun p => Test.pair p.1.1 p.1.2 p.2.1 p.2.2))
    ∪ pairs.image (fun p => Test.tangent p.1.1 p.1.2 p.2.1 p.2.2)).filter Test.Valid

theorem tests_valid (point : ℕ → σ → k) (n : ℕ) (protect : Finset (σ → k))
    (W : Finset (ℕ × MvPolynomial σ k)) {t : Test k σ} (h : t ∈ tests point n protect W) :
    t.Valid := by
  classical exact (Finset.mem_filter.mp h).2

theorem point_mem_tests (point : ℕ → σ → k) (n : ℕ) (protect : Finset (σ → k))
    (W : Finset (ℕ × MvPolynomial σ k)) (u : σ → k) (hu : u ∈ protect) :
    Test.point u ∈ tests point n protect W := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨u,hu,rfl⟩)), trivial⟩

/-- A single cutoff places a given pair of vectors in the pair and tangent
tests for every valid word, independently of which subalgebra will use it. -/
theorem eventually_mem_tests (point : ℕ → σ → k) (hp : Function.Surjective point) (u v : σ → k) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (protect : Finset (σ → k)) (W : Finset (ℕ × MvPolynomial σ k)),
      ∀ w ∈ W,
        ((Test.pair u v w.1 w.2).Valid → Test.pair u v w.1 w.2 ∈ tests point n protect W) ∧
        ((Test.tangent u v w.1 w.2).Valid → Test.tangent u v w.1 w.2 ∈ tests point n protect W) := by
  classical
  obtain ⟨i,rfl⟩ := hp u
  obtain ⟨j,rfl⟩ := hp v
  refine ⟨max i j, ?_⟩
  intro n hn protect W w hw
  have hp' : ((point i, point j), w) ∈
      (((Finset.range (n+1)).image point ×ˢ (Finset.range (n+1)).image point) ×ˢ W) := by
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩, hw⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega),rfl⟩
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega),rfl⟩
  constructor
  · intro hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨_,hp',rfl⟩)), hv⟩
  · intro hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hp',rfl⟩),hv⟩

/-- Additional finite input to the word tests at a stage. It includes prescribed
points, the cumulative prime reservations and all `r`-fold earlier intersections. -/
noncomputable def protection [IsAlgClosed k] (P : ℕ → Ideal (MvPolynomial σ k))
    (F : ℕ → MvPolynomial σ k) (r n : ℕ) (fixed : Finset (σ → k)) (hf : (crossings F r n).Finite) :
    Finset (σ → k) := by classical exact fixed ∪ reserved P F n ∪ hf.toFinset

theorem conclusions_of_protection [IsAlgClosed k] (P : ℕ → Ideal (MvPolynomial σ k))
    (hP : Function.Surjective P) (F : ℕ → MvPolynomial σ k) (r : ℕ) (fixed : Finset (σ → k))
    (hf : ∀ n, (crossings F r n).Finite) (point : ℕ → σ → k)
    (W : ℕ → Finset (ℕ × MvPolynomial σ k))
    (hstage : ∀ n t, t ∈ tests point n (protection P F r n fixed (hf n)) (W n) → t.Holds (F n)) :
    (∀ n u, u ∈ fixed → eval u (F n) ≠ 0) ∧
    (∀ s : Finset ℕ, s.card = r+1 → ∀ u : σ → k, ∃ i ∈ s, eval u (F i) ≠ 0) ∧
    (∀ Q : Ideal (MvPolynomial σ k), Q.IsPrime →
      Disjoint ((Submonoid.closure (Set.range F)) : Set (MvPolynomial σ k)) (Q : Set (MvPolynomial σ k)) →
      ∃ u : σ → k, Retained (Submonoid.closure (Set.range F)) u ∧ Q ≤ pointIdeal u) := by
  classical
  have h (n) (u : σ → k) (hu : u ∈ protection P F r n fixed (hf n)) : eval u (F n) ≠ 0 :=
    hstage n (.point u) (point_mem_tests _ _ _ _ _ hu)
  exact ⟨fun n u hu => h n u (Finset.mem_union_left _ (Finset.mem_union_left _ hu)),
    no_common_zero F r (fun n u hu => h n u (Finset.mem_union_right _ ((hf n).mem_toFinset.mpr hu))),
    retained_points P hP F (fun n u hu => h n u (Finset.mem_union_left _ (Finset.mem_union_right _ hu)))⟩

end UnconditionalCounterexample.MultivariateSchedule
