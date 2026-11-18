import HereditaryAtomicity.SparseProfileSelection

/-! Finite-factor combinatorics for the arithmetic sparse conductor cut. -/

noncomputable section
open scoped BigOperators
namespace HereditaryAtomicity
namespace SparseRelevantVector

/-- A pure polynomial term has no endpoint or returned-unit factor and no
negative generator exponent. Its scalar order may be nonzero. -/
def Pure (w : SparseRelevantVector) : Prop :=
  w.endpoint = 0 ∧ w.unit = 0 ∧ ∀ n, 0 ≤ w.powers n

/-- Coordinate sum, without imposing an irrelevant additive structure on the
restricted class of relevant vectors. -/
def sum {ι : Type*} (s : Finset ι) (w : ι → SparseRelevantVector) : SparseRelevantVector :=
  ⟨∑ i ∈ s, (w i).scalar, ∑ i ∈ s, (w i).powers,
    ∑ i ∈ s, (w i).endpoint, ∑ i ∈ s, (w i).unit⟩

@[simp] theorem eval_sum {X ι : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ)
    (P : X) (s : Finset ι) (w : ι → SparseRelevantVector) :
    (sum s w).eval γ ξ σ P = ∑ i ∈ s, (w i).eval γ ξ σ P := by
  classical
  have hsum : (∑ i ∈ s, (w i).powers).sum (fun j k => (k : ℝ)*γ j P) =
      ∑ i ∈ s, (w i).powers.sum (fun j k => (k : ℝ)*γ j P) := by
    symm
    apply Finsupp.sum_finsetSum_index
    · simp
    · intros
      simp only [Int.cast_add, add_mul]
  simp only [sum, eval, hsum, Nat.cast_sum, Finset.sum_add_distrib, Finset.sum_mul]

/-- An endpoint vector is always relevant. -/
def endpointVector : SparseRelevantVector := ⟨0, 0, 1, 0⟩

@[simp] theorem endpointVector_relevant : endpointVector.Relevant := by
  simp [endpointVector, Relevant]

@[simp] theorem eval_endpointVector {X : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ)
    (P : X) : endpointVector.eval γ ξ σ P = ξ P := by
  simp [endpointVector, eval]

/-- Pure sums remain relevant. -/
theorem relevant_sum_of_pure {ι : Type*} (s : Finset ι) (w : ι → SparseRelevantVector)
    (hw : ∀ i ∈ s, (w i).Pure) : (sum s w).Relevant := by
  classical
  constructor
  · simp only [sum, Finset.sum_eq_zero (fun i hi => (hw i hi).1),
      Finset.sum_eq_zero (fun i hi => (hw i hi).2.1), Nat.zero_le, zero_add]
  · intro n
    have hnonneg : 0 ≤ ∑ i ∈ s, (w i).powers n :=
      Finset.sum_nonneg (fun i hi => (hw i hi).2.2 n)
    simpa only [sum, Finsupp.coe_finsetSum, Finset.sum_apply] using
      (show (-1 : ℤ) ≤ ∑ i ∈ s, (w i).powers n by omega)

/-- A sum of pure vectors and one relevant vector is relevant. -/
theorem relevant_sum_of_one_exception {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → SparseRelevantVector) {j : ι} (hj : j ∈ s)
    (hwj : (w j).Relevant) (hw : ∀ i ∈ s, i ≠ j → (w i).Pure) :
    (sum s w).Relevant := by
  have he : ∑ i ∈ s, (w i).endpoint = (w j).endpoint :=
    Finset.sum_eq_single_of_mem j hj (fun i hi hij => (hw i hi hij).1)
  have hu : ∑ i ∈ s, (w i).unit = (w j).unit :=
    Finset.sum_eq_single_of_mem j hj (fun i hi hij => (hw i hi hij).2.1)
  refine ⟨by simpa only [sum, he, hu] using hwj.1, ?_⟩
  intro n
  have hrest : 0 ≤ ∑ i ∈ s.erase j, (w i).powers n := by
    apply Finset.sum_nonneg
    intro i hi
    exact (hw i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)).2.2 n
  have heq := Finset.sum_erase_add s (fun i => (w i).powers n) hj
  have hn : (w j).powers n ≤ ∑ i ∈ s, (w i).powers n := by omega
  simpa only [sum, Finsupp.coe_finsetSum, Finset.sum_apply] using (hwj.2 n).trans hn

/-- At most one factor is above c when all orders are positive and their total
is below 2c. Relevance and low-window injectivity then identify all low factors
as squarefree pure terms of scalar order zero. -/
theorem unique_high_factor_of_endpoint_sum
    {X ι : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ)
    (c : ℝ) (hinj : LowInjective γ ξ σ (2*c))
    (P : X) (s : Finset ι) (f : ι → ℝ) (w : ι → SparseRelevantVector)
    (hpos : ∀ i ∈ s, 0 < f i) (hsum : ∑ i ∈ s, f i = ξ P)
    (hξ : ξ P < 2*c) (hw : ∀ i ∈ s, (w i).Relevant)
    (heval : ∀ i ∈ s, (w i).eval γ ξ σ P = f i)
    (hlow : ∀ i ∈ s, f i ≤ c → (w i).Pure) :
    ∃ j ∈ s, c < f j ∧ (∀ i ∈ s, c < f i → i = j) ∧
      (∀ i ∈ s, (w i).scalar = 0) ∧
      ∀ i ∈ s, i ≠ j → (w i).Pure ∧ ∀ n, (w i).powers n = 0 ∨ (w i).powers n = 1 := by
  classical
  have hatmost : ∀ i ∈ s, ∀ j ∈ s, c < f i → c < f j → i = j := by
    intro i hi j hj hci hcj
    by_contra hij
    have hsub : ({i,j} : Finset ι) ⊆ s := by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hi,hj⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k hk _ => (hpos k hk).le)
    have hijsum : f i + f j ≤ ξ P := by simpa [hij,hsum] using hle
    linarith
  have hrel : (sum s w).Relevant := by
    by_cases hh : ∃ j ∈ s, c < f j
    · obtain ⟨j,hj,hcj⟩ := hh
      apply relevant_sum_of_one_exception s w hj (hw j hj)
      intro i hi hij
      apply hlow i hi
      exact le_of_not_gt (fun hci => hij (hatmost i hi j hj hci hcj))
    · apply relevant_sum_of_pure s w
      intro i hi
      exact hlow i hi (le_of_not_gt (fun hci => hh ⟨i,hi,hci⟩))
  have hval : (sum s w).eval γ ξ σ P = ξ P := by
    rw [eval_sum]
    exact (Finset.sum_congr rfl heval).trans hsum
  have heq : sum s w = endpointVector := hinj P _ _ hrel endpointVector_relevant
    (by rw [hval]; exact hξ.le) (by simpa using hξ.le) (by simpa using hval)
  have hscalar : ∑ i ∈ s, (w i).scalar = 0 := congrArg scalar heq
  have hendpoint : ∑ i ∈ s, (w i).endpoint = 1 := congrArg endpoint heq
  have hpowers (n) : ∑ i ∈ s, (w i).powers n = 0 := by
    have h := congrArg (fun z : SparseRelevantVector => z.powers n) heq
    simpa only [sum,endpointVector,Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.zero_apply] using h
  have hex : ∃ j ∈ s, (w j).endpoint ≠ 0 := by
    by_contra! hz
    have hzero := Finset.sum_eq_zero hz
    omega
  obtain ⟨j,hj,hjend⟩ := hex
  have hcj : c < f j := lt_of_not_ge (fun hle => hjend (hlow j hj hle).1)
  have hpure : ∀ i ∈ s, i ≠ j → (w i).Pure := by
    intro i hi hij
    exact hlow i hi (le_of_not_gt (fun hci => hij (hatmost i hi j hj hci hcj)))
  refine ⟨j,hj,hcj,(fun i hi hci => hatmost i hi j hj hci hcj),?_,?_⟩
  · intro i hi
    have hle : (w i).scalar ≤ ∑ k ∈ s, (w k).scalar :=
      Finset.single_le_sum (f := fun k => (w k).scalar) (fun k _ => Nat.zero_le _) hi
    omega
  · intro i hi hij
    refine ⟨hpure i hi hij, fun n => ?_⟩
    have h0 := (hpure i hi hij).2.2 n
    have hneg := (hw j hj).2 n
    have hrest : (w i).powers n ≤ ∑ k ∈ s.erase j, (w k).powers n := by
      apply Finset.single_le_sum _ (Finset.mem_erase.mpr ⟨hij,hi⟩)
      intro k hk
      exact (hpure k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)).2.2 n
    have htotal := Finset.sum_erase_add s (fun k => (w k).powers n) hj
    have hzero := hpowers n
    omega

/-- A pure squarefree scalar-zero term is bounded at every branch by the sum of
its generator budgets. -/
theorem eval_pure_squarefree_le_budget
    {X : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ) (b : ℕ → ℝ) (B : ℝ)
    (hγ : ∀ j P, γ j P ≤ b j) (hb : ∀ s : Finset ℕ, ∑ j ∈ s, b j ≤ B)
    (w : SparseRelevantVector) (hw : w.Pure) (hs : w.scalar = 0)
    (hp : ∀ n, w.powers n = 0 ∨ w.powers n = 1) (P : X) :
    w.eval γ ξ σ P ≤ B := by
  classical
  have hp' : ∀ n ∈ w.powers.support, w.powers n = 1 := by
    intro n hn
    exact (hp n).resolve_left (Finsupp.mem_support_iff.mp hn)
  simp only [eval,hs,hw.1,hw.2.1,Nat.cast_zero,zero_mul,zero_add,add_zero,Finsupp.sum]
  calc
    (∑ n ∈ w.powers.support, (w.powers n : ℝ)*γ n P) =
        ∑ n ∈ w.powers.support, γ n P := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [hp' n hn]
    _ ≤ ∑ n ∈ w.powers.support, b n := Finset.sum_le_sum (fun n _ => hγ n P)
    _ ≤ B := hb _

/-- The chosen geometric budgets put every low squarefree term below one half. -/
theorem eval_pure_squarefree_le_quarter
    {X : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ)
    (hγ : ∀ j P, γ j P ≤ sparseProfileBudget j)
    (w : SparseRelevantVector) (hw : w.Pure) (hs : w.scalar = 0)
    (hp : ∀ n, w.powers n = 0 ∨ w.powers n = 1) (P : X) :
    w.eval γ ξ σ P ≤ 1/4 :=
  eval_pure_squarefree_le_budget γ ξ σ sparseProfileBudget (1/4) hγ
    sum_sparseProfileBudget_le w hw hs hp P

end SparseRelevantVector
end HereditaryAtomicity
