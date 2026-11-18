import HereditaryAtomicity.SparseRelevantVectors
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual products avoiding finite profile obstructions

Only finite ranges of the first chosen profile and uniform smallness of the
second are used. The branch set need not be finite and no comparison or
rationality hypothesis is imposed on the real values.
-/

noncomputable section
namespace HereditaryAtomicity

/-- Two-product avoidance with both source indices retained. -/
theorem exists_two_product_profile_avoiding
    {K X : Type*} [Field K] [Nonempty X]
    (ν : X → K → ℝ) (b : ℕ → K)
    (hmul : ∀ P x y, x ≠ 0 → y ≠ 0 → ν P (x*y) = ν P x + ν P y)
    (hb0 : ∀ n, b n ≠ 0) (hbpos : ∀ n P, 0 < ν P (b n))
    (hbfinite : ∀ n, (Set.range (fun P => ν P (b n))).Finite)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ P, ν P (b n) < ε)
    (E : Finset ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m n : ℕ, b m * b n ≠ 0 ∧
      (∀ P, 0 < ν P (b m * b n) ∧ ν P (b m * b n) < ε) ∧
      (Set.range (fun P => ν P (b m * b n))).Finite ∧
      ∀ P (q : ℕ), 0 < q → (q : ℝ) * ν P (b m * b n) ∉ E := by
  classical
  obtain ⟨m, hm⟩ := hsmall (ε/2) (by positivity)
  let V := Set.range (fun P => ν P (b m))
  have hvfin : V.Finite := hbfinite m
  let : Fintype V := hvfin.fintype
  have : Nonempty V := ⟨⟨ν (Classical.choice inferInstance) (b m),
    ⟨Classical.choice inferInstance, rfl⟩⟩⟩
  have hpos (a : V) : 0 < (a : ℝ) := by
    obtain ⟨P, hP⟩ := a.property
    rw [← hP]
    exact hbpos m P
  choose δ hδ hgap using fun a : V => real_submultiple_right_gap E a (hpos a)
  let d : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hd : 0 < d := by
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty δ
    dsimp [d]
    rw [ha]
    exact hδ a
  obtain ⟨n, hn⟩ := hsmall (min (ε/2) d) (lt_min (by positivity) hd)
  refine ⟨m, n, mul_ne_zero (hb0 m) (hb0 n), ?_, ?_, ?_⟩
  · intro P
    rw [hmul P _ _ (hb0 m) (hb0 n)]
    exact ⟨add_pos (hbpos m P) (hbpos n P), by
      have := (hn P).trans_le (min_le_left _ _)
      linarith [hm P]⟩
  · simpa only [hmul _ _ _ (hb0 m) (hb0 n)] using
      finite_range_profile_binary _ _ (hbfinite m) (hbfinite n) (fun x y : ℝ => x+y)
  · intro P q hq
    rw [hmul P _ _ (hb0 m) (hb0 n)]
    let a : V := ⟨ν P (b m), ⟨P, rfl⟩⟩
    have hnd : ν P (b n) < δ a :=
      (hn P).trans_le ((min_le_right _ _).trans
        (Finset.inf'_le δ (Finset.mem_univ a)))
    exact hgap a (ν P (b m) + ν P (b n)) (by dsimp [a]; linarith [hbpos n P])
      (by dsimp [a] at *; linarith) q hq

private structure SparseProfilePrefix
    {K X : Type*} [Field K] (ν : X → K → ℝ) (b : ℕ → K)
    (ξ σ : X → ℝ) (η : ℕ → ℝ) (c : ℕ) (n : ℕ) where
  indices : Fin n → ℕ × ℕ
  small : ∀ j P, ν P (b (indices j).1 * b (indices j).2) < η j
  sparse : SparseStageVector.LowInjective
    (fun j P => ν P (b (indices j).1 * b (indices j).2)) ξ σ
    (3*(c : ℝ) - ∑ j ∈ Finset.range n, η j)

/-- Coherent sparse prefixes built from actual two-factor source products.
The positive budget may be any prescribed sequence, hence can be summable. -/
theorem exists_sparse_profile_prefixes
    {K X : Type*} [Field K] [Nonempty X]
    (ν : X → K → ℝ) (b : ℕ → K)
    (hmul : ∀ P x y, x ≠ 0 → y ≠ 0 → ν P (x*y) = ν P x + ν P y)
    (hb0 : ∀ n, b n ≠ 0) (hbpos : ∀ n P, 0 < ν P (b n))
    (hbfinite : ∀ n, (Set.range (fun P => ν P (b n))).Finite)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ P, ν P (b n) < ε)
    (c : ℕ) (hc : 0 < c) (ξ σ : X → ℝ)
    (hξ : ∀ P, (c : ℝ) < ξ P ∧ ξ P < c+1)
    (hσ : ∀ P, 4*(c : ℝ) ≤ σ P)
    (hξfin : (Set.range ξ).Finite) (hσfin : (Set.range σ).Finite)
    (η : ℕ → ℝ) (hη : ∀ n, 0 < η n) :
    ∃ a : ℕ → K,
      (∀ n, (∃ j k, a n = b j * b k) ∧ a n ≠ 0 ∧
        (∀ P, 0 < ν P (a n) ∧ ν P (a n) < η n) ∧
        (Set.range (fun P => ν P (a n))).Finite) ∧
      ∀ n, SparseStageVector.LowInjective (fun j : Fin n => fun P => ν P (a j))
        ξ σ (3*(c : ℝ) - ∑ j ∈ Finset.range n, η j) := by
  classical
  have hprodpos (j k : ℕ) (P) : 0 < ν P (b j*b k) := by
    rw [hmul P _ _ (hb0 j) (hb0 k)]
    exact add_pos (hbpos j P) (hbpos k P)
  have hprodfin (j k : ℕ) : (Set.range (fun P => ν P (b j*b k))).Finite := by
    simpa only [hmul _ _ _ (hb0 j) (hb0 k)] using
      finite_range_profile_binary _ _ (hbfinite j) (hbfinite k) (fun x y : ℝ => x+y)
  let initial : SparseProfilePrefix ν b ξ σ η c 0 := {
    indices := Fin.elim0
    small := fun j => Fin.elim0 j
    sparse := by
      have hfun : (fun j : Fin 0 => fun P => ν P (b (Fin.elim0 j : ℕ × ℕ).1 * b (Fin.elim0 j : ℕ × ℕ).2)) =
          (fun j : Fin 0 => (Fin.elim0 j : X → ℝ)) := Subsingleton.elim _ _
      rw [hfun]
      simpa using SparseStageVector.lowInjective_empty c hc ξ σ hξ hσ }
  have step (n : ℕ) (s : SparseProfilePrefix ν b ξ σ η c n) :
      ∃ t : SparseProfilePrefix ν b ξ σ η c (n+1),
        ∀ j : Fin n, t.indices j.castSucc = s.indices j := by
    obtain ⟨E,hE⟩ := SparseStageVector.exists_extension_obstructions
      (fun j P => ν P (b (s.indices j).1*b (s.indices j).2)) ξ σ
      (fun j P => hprodpos _ _ P) (fun j => hprodfin _ _) hξfin hσfin _ s.sparse
    obtain ⟨j,k,_,ha,_,hav⟩ := exists_two_product_profile_avoiding ν b hmul hb0 hbpos
      hbfinite hsmall E (η n) (hη n)
    have hfun : (fun l : Fin (n+1) => fun P =>
        ν P (b ((Fin.snoc s.indices (j,k) : Fin (n+1) → ℕ × ℕ) l).1 * b ((Fin.snoc s.indices (j,k) : Fin (n+1) → ℕ × ℕ) l).2)) =
        Fin.snoc (fun l P => ν P (b (s.indices l).1*b (s.indices l).2))
          (fun P => ν P (b j*b k)) := by
      funext l
      exact Fin.lastCases (by simp) (fun q => by simp) l
    let t : SparseProfilePrefix ν b ξ σ η c (n+1) := {
      indices := Fin.snoc s.indices (j,k)
      small := by
        intro l
        exact Fin.lastCases (by simpa using fun P => (ha P).2)
          (fun q => by simpa using s.small q) l
      sparse := by
        rw [hfun]
        have hθ : 3*(c : ℝ) - ∑ l ∈ Finset.range (n+1), η l =
            (3*(c : ℝ) - ∑ l ∈ Finset.range n, η l) - η n := by
          rw [Finset.sum_range_succ]
          ring
        rw [hθ]
        exact hE _ _ ha hav }
    exact ⟨t, by intro l; simp [t]⟩
  choose next hnext using step
  let f : (n : ℕ) → SparseProfilePrefix ν b ξ σ η c n := Nat.rec initial (fun n s => next n s)
  have hcompat (n : ℕ) (j : Fin n) : (f (n+1)).indices j.castSucc = (f n).indices j :=
    hnext n (f n) j
  let pairs : ℕ → ℕ × ℕ := fun n => (f (n+1)).indices (Fin.last n)
  have hpref : ∀ n : ℕ, ∀ j : Fin n, (f n).indices j = pairs j := by
    intro n
    induction n with
    | zero => intro j; exact Fin.elim0 j
    | succ n ih =>
      intro j
      exact Fin.lastCases rfl (fun k => (hcompat n k).trans (ih k)) j
  let a := fun n => b (pairs n).1 * b (pairs n).2
  refine ⟨a, ?_, ?_⟩
  · intro n
    refine ⟨⟨_,_,rfl⟩, mul_ne_zero (hb0 _) (hb0 _), ?_, hprodfin _ _⟩
    intro P
    exact ⟨hprodpos _ _ P, by simpa [a,pairs] using (f (n+1)).small (Fin.last n) P⟩
  · intro n
    have heq : (fun j : Fin n => fun P => ν P (a j)) =
        (fun j : Fin n => fun P => ν P (b ((f n).indices j).1*b ((f n).indices j).2)) := by
      funext j P
      rw [hpref]
    rw [heq]
    exact (f n).sparse

/-- The full sparse-profile selection theorem: all relevant finitely supported
vectors are distinct below 2c at every branch. -/
theorem exists_sparse_profile_sequence
    {K X : Type*} [Field K] [Nonempty X]
    (ν : X → K → ℝ) (b : ℕ → K)
    (hmul : ∀ P x y, x ≠ 0 → y ≠ 0 → ν P (x*y) = ν P x + ν P y)
    (hb0 : ∀ n, b n ≠ 0) (hbpos : ∀ n P, 0 < ν P (b n))
    (hbfinite : ∀ n, (Set.range (fun P => ν P (b n))).Finite)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ P, ν P (b n) < ε)
    (c : ℕ) (hc : 0 < c) (ξ σ : X → ℝ)
    (hξ : ∀ P, (c : ℝ) < ξ P ∧ ξ P < c+1)
    (hσ : ∀ P, 4*(c : ℝ) ≤ σ P)
    (hξfin : (Set.range ξ).Finite) (hσfin : (Set.range σ).Finite)
    (η : ℕ → ℝ) (hη : ∀ n, 0 < η n)
    (hηsum : ∀ n, (∑ j ∈ Finset.range n, η j) ≤ c) :
    ∃ a : ℕ → K,
      (∀ n, (∃ j k, a n = b j * b k) ∧ a n ≠ 0 ∧
        (∀ P, 0 < ν P (a n) ∧ ν P (a n) < η n) ∧
        (Set.range (fun P => ν P (a n))).Finite) ∧
      SparseRelevantVector.LowInjective (fun j P => ν P (a j)) ξ σ (2*c) := by
  obtain ⟨a,ha,hinj⟩ := exists_sparse_profile_prefixes ν b hmul hb0 hbpos hbfinite hsmall
    c hc ξ σ hξ hσ hξfin hσfin η hη
  refine ⟨a,ha,SparseRelevantVector.lowInjective_of_prefixes _ _ _ _ _ ?_ hinj⟩
  intro n
  linarith [hηsum n]

/-- A fixed summable choice of profile budgets, independent of the construction. -/
def sparseProfileBudget (n : ℕ) : ℝ := (1/2 : ℝ)^(n+3)

theorem sparseProfileBudget_pos (n : ℕ) : 0 < sparseProfileBudget n := by
  exact pow_pos (by norm_num) _

/-- Every finite collection of selected generator profiles has total budget at
most 1/4, hence strictly below the half-unit window used in the cut proof. -/
theorem sum_sparseProfileBudget_le (s : Finset ℕ) :
    (∑ n ∈ s, sparseProfileBudget n) ≤ 1/4 := by
  have hsum : (∑ n ∈ s, (1/2 : ℝ)^n) ≤ 2 := by
    simpa only [tsum_geometric_two] using
      summable_geometric_two.sum_le_tsum s (fun n _ => pow_nonneg (by norm_num) n)
  simp only [sparseProfileBudget,pow_add]
  rw [← Finset.sum_mul]
  norm_num
  nlinarith

/-- The budget becomes arbitrarily small after any prescribed index. -/
theorem exists_sparseProfileBudget_lt (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, N < n ∧ sparseProfileBudget n < ε := by
  obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one hε (show (1/2 : ℝ)<1 by norm_num)
  refine ⟨max N m + 1, by omega, ?_⟩
  apply lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_) hm
  exact Nat.le_trans (le_max_right N m) (by omega)

end HereditaryAtomicity
