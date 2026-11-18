import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Sparse source selection for finitely many real valuation orders

The real avoidance arguments do not require rational values. Source witnesses
are subsequently obtained using only powers, sums and products.
-/

noncomputable section

namespace HereditaryAtomicity

/-- A finite subset of the real line leaves a right-hand gap at every point. -/
theorem finite_real_right_gap (E : Finset ℝ) (a : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, a < x → x < a + δ → x ∉ E := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert d E hd ih =>
    obtain ⟨δ, hδ, hgap⟩ := ih
    by_cases had : a < d
    · refine ⟨min δ (d - a), lt_min hδ (sub_pos.mpr had), ?_⟩
      intro x hax hx
      have hxδ : x < a + δ := lt_of_lt_of_le hx (add_le_add_right (min_le_left _ _) _)
      have hxd : x < d := by linarith [min_le_right δ (d - a)]
      simp only [Finset.mem_insert, not_or]
      exact ⟨ne_of_lt hxd, hgap x hax hxδ⟩
    · refine ⟨δ, hδ, ?_⟩
      intro x hax hx
      simp only [Finset.mem_insert, not_or]
      exact ⟨ne_of_gt (lt_of_le_of_lt (le_of_not_gt had) hax), hgap x hax hx⟩

/-- Integral submultiples of a fixed real number have a right-hand gap above a
fixed positive point. This is the local finiteness used in sparse selection. -/
theorem real_submultiple_right_gap_single (d a : ℝ) (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, a < x → x < a + δ →
      ∀ q : ℕ, 0 < q → (q : ℝ) * x ≠ d := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (d / a)
  obtain ⟨δ, hδ, hgap⟩ := finite_real_right_gap
    ((Finset.range N).image fun q : ℕ => d / (q : ℝ)) a
  refine ⟨δ, hδ, ?_⟩
  intro x hax hx q hq hqd
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqa : (q : ℝ) * a < d := by nlinarith
  have hqbound : (q : ℝ) < N := lt_trans ((lt_div_iff₀ ha).mpr hqa) hN
  have hqN : q < N := by exact_mod_cast hqbound
  apply hgap x hax hx
  apply Finset.mem_image.mpr
  refine ⟨q, Finset.mem_range.mpr hqN, ?_⟩
  exact (div_eq_iff (ne_of_gt hqr)).mpr (by simpa [mul_comm] using hqd.symm)

/-- Finitely many positive endpoint values can be avoided simultaneously by
all positive integral multiples in a sufficiently short right-hand interval. -/
theorem real_submultiple_right_gap (E : Finset ℝ) (a : ℝ) (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, a < x → x < a + δ →
      ∀ q : ℕ, 0 < q → (q : ℝ) * x ∉ E := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert d E hd ih =>
    obtain ⟨δ, hδ, hgap⟩ := ih
    obtain ⟨η, hη, hav⟩ := real_submultiple_right_gap_single d a ha
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro x hax hx q hq
    simp only [Finset.mem_insert, not_or]
    exact ⟨hav x hax (lt_of_lt_of_le hx (add_le_add_right (min_le_right _ _) _)) q hq,
      hgap x hax (lt_of_lt_of_le hx (add_le_add_right (min_le_left _ _) _)) q hq⟩


/-- Small positive source elements whose same branch is always minimal can avoid
finitely many integral-submultiple obstructions by taking an actual product. -/
theorem exists_small_source_avoiding_submultiples
    {K ι : Type*} [Field K] (C : Subring K) (ν : ι → K → ℝ) (i₀ : ι)
    (hmul : ∀ i x y, x ≠ 0 → y ≠ 0 → ν i (x * y) = ν i x + ν i y)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ x : K, x ∈ C ∧ x ≠ 0 ∧
      ∀ i, 0 < ν i x ∧ ν i x < ε ∧ ν i₀ x ≤ ν i x)
    (E : Finset ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : K, a ∈ C ∧ a ≠ 0 ∧
      (∀ i, 0 < ν i a ∧ ν i a < ε ∧ ν i₀ a ≤ ν i a) ∧
      ∀ q : ℕ, 0 < q → (q : ℝ) * ν i₀ a ∉ E := by
  obtain ⟨x, hxC, hx0, hx⟩ := hsmall (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hgap⟩ := real_submultiple_right_gap E (ν i₀ x) (hx i₀).1
  obtain ⟨y, hyC, hy0, hy⟩ := hsmall (min (ε / 2) δ) (by positivity)
  refine ⟨x * y, C.mul_mem hxC hyC, mul_ne_zero hx0 hy0, ?_, ?_⟩
  · intro i
    rw [hmul i x y hx0 hy0, hmul i₀ x y hx0 hy0]
    have hyε : ν i y < ε / 2 := lt_of_lt_of_le (hy i).2.1 (min_le_left _ _)
    exact ⟨add_pos (hx i).1 (hy i).1, by linarith [(hx i).2.1],
      add_le_add (hx i).2.2 (hy i).2.2⟩
  · rw [hmul i₀ x y hx0 hy0]
    exact hgap _ (by linarith [(hy i₀).1])
      (by linarith [lt_of_lt_of_le (hy i₀).2.1 (min_le_right (ε / 2) δ)])

/-- A finite set of branches has a fixed minimum branch along a simultaneously
coinitial family of actual source elements. No subsequence hypothesis is needed. -/
theorem exists_coinitial_minimum_branch
    {K ι : Type*} [Field K] [Fintype ι] [Nonempty ι]
    (C : Subring K) (ν : ι → K → ℝ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ x : K, x ∈ C ∧ x ≠ 0 ∧
      ∀ i, 0 < ν i x ∧ ν i x < ε) :
    ∃ i₀ : ι, ∀ ε : ℝ, 0 < ε → ∃ x : K, x ∈ C ∧ x ≠ 0 ∧
      ∀ i, 0 < ν i x ∧ ν i x < ε ∧ ν i₀ x ≤ ν i x := by
  classical
  by_contra h
  push Not at h
  choose ε hε hfail using h
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty ε
  have hδ : 0 < δ := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty ε
    dsimp [δ]
    rw [hj]
    exact hε j
  obtain ⟨x, hxC, hx0, hx⟩ := hsmall δ hδ
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => ν i x)
  obtain ⟨i, hi⟩ := hfail i₀ x hxC hx0
  have hmin : ν i₀ x ≤ ν i x := by
    rw [← hi₀]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  exact (not_lt_of_ge hmin) (hi (hx i).1
    (lt_of_lt_of_le (hx i).2 (Finset.inf'_le _ (Finset.mem_univ i₀))))


/-- The nonnegative integral combinations of a finite positive real family have
only finitely many coefficient vectors below any fixed bound. -/
theorem finite_nat_weighted_sum_le
    {ι : Type*} [Fintype ι] (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i) (B : ℝ) :
    Set.Finite {d : ι → ℕ | (∑ i, (d i : ℝ) * γ i) ≤ B} := by
  classical
  choose N hN using fun i => exists_nat_gt (B / γ i)
  have hfinite : Set.Finite {d : ι → ℕ | ∀ i, d i ∈ Set.Iio (N i)} :=
    Set.Finite.pi' (fun i => Set.finite_Iio (N i))
  apply hfinite.subset
  intro d hd i
  have hterm : (d i : ℝ) * γ i ≤ ∑ j, (d j : ℝ) * γ j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hγ j).le)
      (Finset.mem_univ i)
  have hbound : (d i : ℝ) < N i :=
    lt_of_le_of_lt ((le_div_iff₀ (hγ i)).mpr (hterm.trans hd)) (hN i)
  exact_mod_cast hbound

/-- A coefficient scalar and a finite vector of natural exponents. -/
def sparseCombination {ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (r : ℕ) (d : ι → ℕ) : ℝ :=
  (r : ℝ) + ∑ i, (d i : ℝ) * γ i

theorem sparseCombination_nonneg {ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (hγ : ∀ i, 0 ≤ γ i) (r : ℕ) (d : ι → ℕ) :
    0 ≤ sparseCombination γ r d := by
  exact add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (hγ i)))

/-- A finitely generated positive real monoid together with natural scalar
coefficients is finite in every bounded interval. -/
theorem finite_sparseCombination_le
    {ι : Type*} [Fintype ι] (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i) (B : ℝ) :
    Set.Finite {x : ℝ | ∃ r : ℕ, ∃ d : ι → ℕ,
      x = sparseCombination γ r d ∧ x ≤ B} := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt B
  have hfinite : Set.Finite {p : ℕ × (ι → ℕ) | sparseCombination γ p.1 p.2 ≤ B} := by
    apply ((Set.finite_Iio N).prod (finite_nat_weighted_sum_le γ hγ B)).subset
    rintro ⟨r, d⟩ hp
    have hsum : 0 ≤ ∑ i, (d i : ℝ) * γ i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hγ i).le)
    change (r : ℝ) + ∑ i, (d i : ℝ) * γ i ≤ B at hp
    constructor
    · have hr : (r : ℝ) < N := by linarith
      exact_mod_cast hr
    · change (∑ i, (d i : ℝ) * γ i) ≤ B
      linarith [Nat.cast_nonneg (α := ℝ) r]
  apply (hfinite.image (fun p => sparseCombination γ p.1 p.2)).subset
  rintro x ⟨r, d, rfl, hrd⟩
  exact ⟨(r, d), hrd, rfl⟩


/-- Finite-stage low-value injectivity and endpoint avoidance. -/
structure SparsePrefix (c β : ℝ) {n : ℕ} (γ : Fin n → ℝ) : Prop where
  positive : ∀ i, 0 < γ i
  low_injective : ∀ (r s : ℕ) (d e : Fin n → ℕ),
    sparseCombination γ r d ≤ c → sparseCombination γ s e ≤ c →
    sparseCombination γ r d = sparseCombination γ s e → r = s ∧ d = e
  avoids : ∀ (r : ℕ) (d : Fin n → ℕ), sparseCombination γ r d ≠ β

theorem sparseCombination_snoc {n : ℕ} (γ : Fin n → ℝ) (g : ℝ)
    (r : ℕ) (d : Fin (n + 1) → ℕ) :
    sparseCombination (Fin.snoc γ g) r d =
      sparseCombination γ r (fun i => d i.castSucc) + (d (Fin.last n) : ℝ) * g := by
  simp only [sparseCombination, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- The empty family starts the sparse induction when its endpoint is not a
natural coefficient value. -/
theorem sparsePrefix_empty (c β : ℝ) (hβ : ∀ r : ℕ, (r : ℝ) ≠ β) :
    SparsePrefix c β (fun i : Fin 0 => Fin.elim0 i) := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro r s d e _ _ heq
    have hrs : r = s := by simpa [sparseCombination] using heq
    exact ⟨hrs, Subsingleton.elim _ _⟩
  · intro r d
    simpa [sparseCombination] using hβ r

/-- Adding a positive generator preserves sparse low values and endpoint
avoidance if its positive multiples avoid finitely many old differences. -/
theorem sparsePrefix_extension
    {n : ℕ} {c β : ℝ} (γ : Fin n → ℝ) (hγ : SparsePrefix c β γ) :
    ∃ E : Finset ℝ, ∀ g : ℝ, 0 < g →
      (∀ q : ℕ, 0 < q → (q : ℝ) * g ∉ E) →
      SparsePrefix c β (Fin.snoc γ g) := by
  classical
  let L : Finset ℝ := (finite_sparseCombination_le γ hγ.positive (max c β)).toFinset
  have hmem (r : ℕ) (d : Fin n → ℕ) (h : sparseCombination γ r d ≤ max c β) :
      sparseCombination γ r d ∈ L := by
    exact (finite_sparseCombination_le γ hγ.positive (max c β)).mem_toFinset.mpr
      ⟨r, d, rfl, h⟩
  let E : Finset ℝ := L.biUnion (fun u => L.image (fun v => v - u)) ∪
    L.image (fun u => β - u)
  refine ⟨E, ?_⟩
  intro g hg hav
  constructor
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa using hg
    · intro j
      simpa using hγ.positive j
  · intro r s d e hd he heq
    let u := sparseCombination γ r (fun i => d i.castSucc)
    let v := sparseCombination γ s (fun i => e i.castSucc)
    let k := d (Fin.last n)
    let l := e (Fin.last n)
    simp only [sparseCombination_snoc] at hd he heq
    have hsum : u + (k : ℝ) * g = v + (l : ℝ) * g := heq
    have hu : u ≤ c := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      dsimp [u, k] at *
      nlinarith
    have hv : v ≤ c := by
      have : (0 : ℝ) ≤ l := Nat.cast_nonneg _
      dsimp [v, l] at *
      nlinarith
    have huL : u ∈ L := hmem _ _ (hu.trans (le_max_left _ _))
    have hvL : v ∈ L := hmem _ _ (hv.trans (le_max_left _ _))
    have hkl : k = l := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hdiff : ((l - k : ℕ) : ℝ) * g = u - v := by
          rw [Nat.cast_sub hlt.le]
          nlinarith
        apply hav (l - k) (Nat.sub_pos_of_lt hlt)
        rw [hdiff]
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        exact ⟨v, hvL, Finset.mem_image.mpr ⟨u, huL, rfl⟩⟩
      · have hdiff : ((k - l : ℕ) : ℝ) * g = v - u := by
          rw [Nat.cast_sub hgt.le]
          nlinarith
        apply hav (k - l) (Nat.sub_pos_of_lt hgt)
        rw [hdiff]
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        exact ⟨u, huL, Finset.mem_image.mpr ⟨v, hvL, rfl⟩⟩
    have huv : u = v := by rw [hkl] at hsum; linarith
    obtain ⟨hrs, hde⟩ := hγ.low_injective _ _ _ _ hu hv huv
    refine ⟨hrs, funext (fun i => ?_)⟩
    exact Fin.lastCases hkl (fun j => congrFun hde j) i
  · intro r d heq
    rw [sparseCombination_snoc] at heq
    let u := sparseCombination γ r (fun i => d i.castSucc)
    let k := d (Fin.last n)
    have hsum : u + (k : ℝ) * g = β := heq
    by_cases hk : k = 0
    · have huβ : u = β := by simpa [hk] using hsum
      exact hγ.avoids _ _ huβ
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have huβ : u ≤ β := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
      have huL : u ∈ L := hmem _ _ (huβ.trans (le_max_right _ _))
      apply hav k hkpos
      have hdiff : (k : ℝ) * g = β - u := by linarith
      rw [hdiff]
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨u, huL, rfl⟩


/-- The additive order of a monomial with finitely supported natural exponents. -/
def sparseWeight (γ : ℕ → ℝ) (d : ℕ →₀ ℕ) : ℝ :=
  d.sum (fun n k => (k : ℝ) * γ n)

private structure SparseSourcePrefix
    {K ι : Type*} [Field K] (C : Subring K) (ν : ι → K → ℝ)
    (i₀ : ι) (c β : ℝ) (n : ℕ) where
  values : Fin n → K
  good : ∀ k, values k ∈ C ∧ values k ≠ 0 ∧
    ∀ i, 0 < ν i (values k) ∧ ν i (values k) < 1 / ((k : ℝ) + 1) ∧
      ν i₀ (values k) ≤ ν i (values k)
  sparse : SparsePrefix c β (fun k => ν i₀ (values k))

/-- Actual source elements can be chosen with coherent sparse prefixes and
simultaneously vanishing upper bounds on all their branch orders. -/
theorem exists_sparse_source_prefixes
    {K ι : Type*} [Field K] (C : Subring K) (ν : ι → K → ℝ) (i₀ : ι)
    (hmul : ∀ i x y, x ≠ 0 → y ≠ 0 → ν i (x * y) = ν i x + ν i y)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ x : K, x ∈ C ∧ x ≠ 0 ∧
      ∀ i, 0 < ν i x ∧ ν i x < ε ∧ ν i₀ x ≤ ν i x)
    (c β : ℝ) (hβ : ∀ r : ℕ, (r : ℝ) ≠ β) :
    ∃ a : ℕ → K,
      (∀ k, a k ∈ C ∧ a k ≠ 0 ∧ ∀ i,
        0 < ν i (a k) ∧ ν i (a k) < 1 / ((k : ℝ) + 1) ∧ ν i₀ (a k) ≤ ν i (a k)) ∧
      ∀ n : ℕ, SparsePrefix c β (fun k : Fin n => ν i₀ (a k)) := by
  classical
  let initial : SparseSourcePrefix C ν i₀ c β 0 := {
    values := Fin.elim0
    good := fun k => Fin.elim0 k
    sparse := by
      have heq : (fun k : Fin 0 => ν i₀ (Fin.elim0 k)) =
          (fun k : Fin 0 => (Fin.elim0 k : ℝ)) := Subsingleton.elim _ _
      rw [heq]
      exact sparsePrefix_empty c β hβ }
  have step (n : ℕ) (s : SparseSourcePrefix C ν i₀ c β n) :
      ∃ t : SparseSourcePrefix C ν i₀ c β (n + 1),
        ∀ k : Fin n, t.values k.castSucc = s.values k := by
    obtain ⟨E, hE⟩ := sparsePrefix_extension _ s.sparse
    obtain ⟨x, hxC, hx0, hx, hav⟩ := exists_small_source_avoiding_submultiples
      C ν i₀ hmul hsmall E (1 / ((n : ℝ) + 1)) (by positivity)
    have hfun : (fun k : Fin (n + 1) => ν i₀ ((Fin.snoc s.values x : Fin (n + 1) → K) k)) =
        Fin.snoc (fun k => ν i₀ (s.values k)) (ν i₀ x) := by
      funext k
      refine Fin.lastCases ?_ ?_ k <;> simp
    let t : SparseSourcePrefix C ν i₀ c β (n + 1) := {
      values := Fin.snoc s.values x
      good := by
        intro k
        refine Fin.lastCases ?_ ?_ k
        · simpa using And.intro hxC (And.intro hx0 hx)
        · intro j
          simpa using s.good j
      sparse := by
        rw [hfun]
        exact hE _ (hx i₀).1 hav }
    exact ⟨t, by intro k; simp [t]⟩
  choose next hnext using step
  let f : (n : ℕ) → SparseSourcePrefix C ν i₀ c β n :=
    Nat.rec initial (fun n s => next n s)
  have hcompat (n : ℕ) (k : Fin n) : (f (n + 1)).values k.castSucc = (f n).values k :=
    hnext n (f n) k
  let a : ℕ → K := fun n => (f (n + 1)).values (Fin.last n)
  have hpref : ∀ n : ℕ, ∀ k : Fin n, (f n).values k = a k := by
    intro n
    induction n with
    | zero => intro k; exact Fin.elim0 k
    | succ n ih =>
      intro k
      refine Fin.lastCases ?_ ?_ k
      · rfl
      · intro j
        exact (hcompat n j).trans (ih j)
  refine ⟨a, ?_, ?_⟩
  · intro k
    simpa [a] using (f (k + 1)).good (Fin.last k)
  · intro n
    have heq : (fun k : Fin n => ν i₀ (a k)) =
        (fun k : Fin n => ν i₀ ((f n).values k)) := by
      funext k
      rw [hpref]
    rw [heq]
    exact (f n).sparse


/-- Evaluate a finitely supported exponent vector inside any prefix containing
its support. -/
theorem sparseWeight_eq_sum_fin (γ : ℕ → ℝ) (d : ℕ →₀ ℕ) (n : ℕ)
    (hd : ∀ k ∈ d.support, k < n) :
    sparseWeight γ d = ∑ k : Fin n, (d k : ℝ) * γ k := by
  classical
  rw [sparseWeight, Finsupp.sum_of_support_subset d
    (show d.support ⊆ Finset.range n from fun k hk => Finset.mem_range.mpr (hd k hk))
    (fun k m => (m : ℝ) * γ k) (by simp)]
  exact (Fin.sum_univ_eq_sum_range (fun k => (d k : ℝ) * γ k) n).symm

/-- Coherent finite sparse prefixes give low-value injectivity for arbitrary
finitely supported exponent vectors. -/
theorem sparse_prefixes_low_injective
    (γ : ℕ → ℝ) (c β : ℝ)
    (h : ∀ n : ℕ, SparsePrefix c β (fun k : Fin n => γ k))
    (r s : ℕ) (d e : ℕ →₀ ℕ)
    (hd : (r : ℝ) + sparseWeight γ d ≤ c)
    (he : (s : ℝ) + sparseWeight γ e ≤ c)
    (heq : (r : ℝ) + sparseWeight γ d = (s : ℝ) + sparseWeight γ e) :
    r = s ∧ d = e := by
  classical
  let n := (d.support ∪ e.support).sup id + 1
  have hdn : ∀ k ∈ d.support, k < n := by
    intro k hk
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_union_left _ hk))
  have hen : ∀ k ∈ e.support, k < n := by
    intro k hk
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_union_right _ hk))
  rw [sparseWeight_eq_sum_fin γ d n hdn] at hd heq
  rw [sparseWeight_eq_sum_fin γ e n hen] at he heq
  obtain ⟨hrs, hde⟩ := (h n).low_injective r s (fun k => d k) (fun k => e k) hd he heq
  refine ⟨hrs, Finsupp.ext (fun k => ?_)⟩
  by_cases hk : k < n
  · exact congrFun hde ⟨k, hk⟩
  · have hdk : k ∉ d.support := fun hmem => hk (hdn k hmem)
    have hek : k ∉ e.support := fun hmem => hk (hen k hmem)
    rw [Finsupp.notMem_support_iff.mp hdk, Finsupp.notMem_support_iff.mp hek]

/-- Endpoint exclusion passes from finite prefixes to all finitely supported
monomials. -/
theorem sparse_prefixes_avoid
    (γ : ℕ → ℝ) (c β : ℝ)
    (h : ∀ n : ℕ, SparsePrefix c β (fun k : Fin n => γ k))
    (r : ℕ) (d : ℕ →₀ ℕ) : (r : ℝ) + sparseWeight γ d ≠ β := by
  classical
  let n := d.support.sup id + 1
  have hdn : ∀ k ∈ d.support, k < n := by
    intro k hk
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  rw [sparseWeight_eq_sum_fin γ d n hdn]
  exact (h n).avoids r (fun k => d k)

/-- Sparse actual-source sequence, with full finitely supported low-value and
endpoint contracts. The construction uses no rationality of valuation values. -/
theorem exists_sparse_source_sequence
    {K ι : Type*} [Field K] (C : Subring K) (ν : ι → K → ℝ) (i₀ : ι)
    (hmul : ∀ i x y, x ≠ 0 → y ≠ 0 → ν i (x * y) = ν i x + ν i y)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ x : K, x ∈ C ∧ x ≠ 0 ∧
      ∀ i, 0 < ν i x ∧ ν i x < ε ∧ ν i₀ x ≤ ν i x)
    (c β : ℝ) (hβ : ∀ r : ℕ, (r : ℝ) ≠ β) :
    ∃ a : ℕ → K,
      (∀ k, a k ∈ C ∧ a k ≠ 0 ∧ ∀ i,
        0 < ν i (a k) ∧ ν i (a k) < 1 / ((k : ℝ) + 1) ∧ ν i₀ (a k) ≤ ν i (a k)) ∧
      (∀ (r s : ℕ) (d e : ℕ →₀ ℕ),
        (r : ℝ) + sparseWeight (fun k => ν i₀ (a k)) d ≤ c →
        (s : ℝ) + sparseWeight (fun k => ν i₀ (a k)) e ≤ c →
        (r : ℝ) + sparseWeight (fun k => ν i₀ (a k)) d =
          (s : ℝ) + sparseWeight (fun k => ν i₀ (a k)) e → r = s ∧ d = e) ∧
      ∀ (r : ℕ) (d : ℕ →₀ ℕ),
        (r : ℝ) + sparseWeight (fun k => ν i₀ (a k)) d ≠ β := by
  obtain ⟨a, ha, hp⟩ := exists_sparse_source_prefixes C ν i₀ hmul hsmall c β hβ
  exact ⟨a, ha, sparse_prefixes_low_injective _ c β hp, sparse_prefixes_avoid _ c β hp⟩


/-- A finite positive real matrix admits uniformly bounded positive integer row
multipliers making every column pairwise distinct. -/
theorem exists_bounded_distinct_multiples
    {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) (hf : ∀ i j, 0 < f i j) :
    ∃ e : ι → ℕ,
      (∀ i, 1 ≤ e i ∧ e i ≤ Fintype.card ι * Fintype.card ι + 1) ∧
      ∀ i j, i ≠ j → ∀ k, (e i : ℝ) * f i k ≠ (e j : ℝ) * f j k := by
  classical
  let t := Fintype.card ι
  let N := t * t + 1
  let pool := Finset.Icc 1 N
  have hpool : pool.card = N := by simp [pool]
  have aux (s : Finset ι) : ∃ e : ι → ℕ,
      (∀ i ∈ s, 1 ≤ e i ∧ e i ≤ N) ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ k,
        (e i : ℝ) * f i k ≠ (e j : ℝ) * f j k := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => 1, by simp, by simp⟩
    | @insert a s has ih =>
      obtain ⟨e, he, hpair⟩ := ih
      let bad : Finset ℕ := s.biUnion (fun j => Finset.univ.biUnion (fun k : ι =>
        pool.filter (fun q : ℕ => (q : ℝ) * f a k = (e j : ℝ) * f j k)))
      have hone (j k : ι) :
          (pool.filter (fun q : ℕ => (q : ℝ) * f a k = (e j : ℝ) * f j k)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro q hq r hr
        have hq' := (Finset.mem_filter.mp hq).2
        have hr' := (Finset.mem_filter.mp hr).2
        have hqr : (q : ℝ) = r := by nlinarith [hf a k]
        exact_mod_cast hqr
      have hbad : bad.card ≤ s.card * t := by
        calc
          bad.card ≤ ∑ j ∈ s, (Finset.univ.biUnion (fun k : ι =>
              pool.filter (fun q : ℕ => (q : ℝ) * f a k = (e j : ℝ) * f j k))).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ j ∈ s, ∑ k : ι,
              (pool.filter (fun q : ℕ => (q : ℝ) * f a k = (e j : ℝ) * f j k)).card :=
            Finset.sum_le_sum (fun j _ => Finset.card_biUnion_le)
          _ ≤ ∑ _j ∈ s, ∑ _k : ι, 1 :=
            Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hone j k))
          _ = s.card * t := by simp [t]
      have hbadlt : bad.card < pool.card := by
        rw [hpool]
        calc
          bad.card ≤ s.card * t := hbad
          _ ≤ t * t := Nat.mul_le_mul_right t (Finset.card_le_univ s)
          _ < N := Nat.lt_succ_self _
      obtain ⟨q, hq, hqnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hbadlt
      have hqbounds : 1 ≤ q ∧ q ≤ N := Finset.mem_Icc.mp hq
      have havoid (j : ι) (hjs : j ∈ s) (k : ι) :
          (q : ℝ) * f a k ≠ (e j : ℝ) * f j k := by
        intro heq
        apply hqnot
        exact Finset.mem_biUnion.mpr ⟨j, hjs, Finset.mem_biUnion.mpr
          ⟨k, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hq, heq⟩⟩⟩
      refine ⟨Function.update e a q, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | his
        · simpa using hqbounds
        · have hia : i ≠ a := fun h => has (h ▸ his)
          simpa [Function.update_of_ne hia] using he i his
      · intro i hi j hj hij k
        rcases Finset.mem_insert.mp hi with rfl | his
        · have hja : j ≠ i := Ne.symm hij
          have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hja
          simpa [Function.update_of_ne hja] using havoid j hjs k
        · have hia : i ≠ a := fun h => has (h ▸ his)
          rcases Finset.mem_insert.mp hj with rfl | hjs
          · simpa [Function.update_of_ne hia] using (havoid i his k).symm
          · have hja : j ≠ a := fun h => has (h ▸ hjs)
            simpa [Function.update_of_ne hia, Function.update_of_ne hja] using
              hpair i his j hjs hij k
  obtain ⟨e, he, hp⟩ := aux Finset.univ
  exact ⟨e, fun i => he i (Finset.mem_univ _),
    fun i j hij k => hp i (Finset.mem_univ _) j (Finset.mem_univ _) hij k⟩


@[simp] theorem sparseWeight_zero (γ : ℕ → ℝ) : sparseWeight γ 0 = 0 := by
  simp [sparseWeight]

@[simp] theorem sparseWeight_add (γ : ℕ → ℝ) (d e : ℕ →₀ ℕ) :
    sparseWeight γ (d + e) = sparseWeight γ d + sparseWeight γ e := by
  simp [sparseWeight, Finsupp.sum_add_index, Nat.cast_add, add_mul]

@[simp] theorem sparseWeight_single (γ : ℕ → ℝ) (n k : ℕ) :
    sparseWeight γ (Finsupp.single n k) = (k : ℝ) * γ n := by
  simp [sparseWeight]

/-- The literal additive monoid of natural coefficient values and selected
monomial orders. -/
def sparseValueMonoid (γ : ℕ → ℝ) : AddSubmonoid ℝ where
  carrier := {x | ∃ r : ℕ, ∃ d : ℕ →₀ ℕ, x = (r : ℝ) + sparseWeight γ d}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨r, d, rfl⟩ ⟨s, e, rfl⟩
    refine ⟨r + s, d + e, ?_⟩
    simp only [Nat.cast_add, sparseWeight_add]
    ring

@[simp] theorem mem_sparseValueMonoid (γ : ℕ → ℝ) (x : ℝ) :
    x ∈ sparseValueMonoid γ ↔ ∃ r : ℕ, ∃ d : ℕ →₀ ℕ,
      x = (r : ℝ) + sparseWeight γ d := Iff.rfl

theorem one_mem_sparseValueMonoid (γ : ℕ → ℝ) : 1 ∈ sparseValueMonoid γ :=
  ⟨1, 0, by simp⟩

theorem generator_mem_sparseValueMonoid (γ : ℕ → ℝ) (n : ℕ) :
    γ n ∈ sparseValueMonoid γ := ⟨0, Finsupp.single n 1, by simp⟩


/-- A finite sum with distinct finite orders has the order of its unique least
term, and is nonzero. -/
theorem finite_sum_order_min
    {K ι : Type*} [Field K] (ν : K → ℝ)
    (hadd : ∀ x y, x ≠ 0 → y ≠ 0 → ν x ≠ ν y →
      x + y ≠ 0 ∧ ν (x + y) = min (ν x) (ν y))
    (s : Finset ι) (x : ι → K) (hs : s.Nonempty)
    (hx : ∀ i ∈ s, x i ≠ 0)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ν (x i) ≠ ν (x j)) :
    (∑ i ∈ s, x i) ≠ 0 ∧
      ∃ j ∈ s, ν (∑ i ∈ s, x i) = ν (x j) ∧ ∀ i ∈ s, ν (x j) ≤ ν (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s has ih =>
    by_cases hs0 : s = ∅
    · subst s
      simp only [Finset.sum_empty, Finset.sum_insert, Finset.notMem_empty, not_false_eq_true,
        add_zero]
      exact ⟨hx a (Finset.mem_insert_self _ _), a, Finset.mem_insert_self _ _, rfl,
        by intro i hi; have hie : i = a := by simpa using hi
           subst i; exact le_rfl⟩
    · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
      obtain ⟨hsum, j, hjs, hjval, hjmin⟩ := ih hsne
        (fun i hi => hx i (Finset.mem_insert_of_mem hi))
        (fun i hi k hk hik => hpair i (Finset.mem_insert_of_mem hi)
          k (Finset.mem_insert_of_mem hk) hik)
      have haj : a ≠ j := fun h => has (h ▸ hjs)
      have hav : ν (x a) ≠ ν (∑ i ∈ s, x i) := by
        rw [hjval]
        exact hpair a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hjs) haj
      obtain ⟨hnz, hv⟩ := hadd (x a) (∑ i ∈ s, x i)
        (hx a (Finset.mem_insert_self _ _)) hsum hav
      rw [Finset.sum_insert has]
      refine ⟨hnz, ?_⟩
      by_cases hle : ν (x a) ≤ ν (x j)
      · refine ⟨a, Finset.mem_insert_self _ _, ?_, ?_⟩
        · simpa [hjval, min_eq_left hle] using hv
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact le_rfl
          · exact hle.trans (hjmin i his)
      · have hle' : ν (x j) ≤ ν (x a) := le_of_not_ge hle
        refine ⟨j, Finset.mem_insert_of_mem hjs, ?_, ?_⟩
        · simpa [hjval, min_eq_right hle'] using hv
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact hle'
          · exact hjmin i his

/-- Separate positive source witnesses at finitely many branches combine, by
bounded powers and a literal sum, into one simultaneously small source element. -/
theorem exists_simultaneously_small_source
    {K ι : Type*} [Field K] [Fintype ι] [Nonempty ι]
    (C : Subring K) (ν : ι → K → ℝ)
    (hmul : ∀ i x y, x ≠ 0 → y ≠ 0 → ν i (x * y) = ν i x + ν i y)
    (hadd : ∀ i x y, x ≠ 0 → y ≠ 0 → ν i x ≠ ν i y →
      x + y ≠ 0 ∧ ν i (x + y) = min (ν i x) (ν i y))
    (hbranch : ∀ i (ε : ℝ), 0 < ε → ∃ x : K,
      x ∈ C ∧ x ≠ 0 ∧ (∀ j, 0 < ν j x) ∧ ν i x < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : K, y ∈ C ∧ y ≠ 0 ∧ ∀ i, 0 < ν i y ∧ ν i y < ε := by
  classical
  let N := Fintype.card ι * Fintype.card ι + 1
  have hN : (0 : ℝ) < N := by positivity
  choose x hxC hx0 hxpos hxsmall using fun i => hbranch i (ε / N) (div_pos hε hN)
  obtain ⟨e, he, hpair⟩ := exists_bounded_distinct_multiples
    (fun i j => ν j (x i)) (fun i j => hxpos i j)
  have hone (i : ι) : ν i 1 = 0 := by
    have h := hmul i 1 1 one_ne_zero one_ne_zero
    simp only [one_mul] at h
    linarith
  have hpow (i : ι) (z : K) (hz : z ≠ 0) (n : ℕ) :
      ν i (z ^ n) = (n : ℝ) * ν i z := by
    induction n with
    | zero => simp [hone]
    | succ n ih =>
      rw [pow_succ, hmul i (z ^ n) z (pow_ne_zero _ hz) hz, ih]
      push_cast
      ring
  let y : K := ∑ i : ι, x i ^ e i
  have hmin (i : ι) : y ≠ 0 ∧ ∃ j : ι,
      ν i y = (e j : ℝ) * ν i (x j) ∧
      ∀ k : ι, (e j : ℝ) * ν i (x j) ≤ (e k : ℝ) * ν i (x k) := by
    obtain ⟨hy, j, _, hj, hleast⟩ := finite_sum_order_min (ν i) (hadd i)
      Finset.univ (fun j => x j ^ e j) Finset.univ_nonempty
      (fun j _ => pow_ne_zero _ (hx0 j)) (by
        intro j _ k _ hjk
        rw [hpow i _ (hx0 j), hpow i _ (hx0 k)]
        exact hpair j k hjk i)
    refine ⟨hy, j, ?_, ?_⟩
    · rw [hpow i _ (hx0 j)] at hj
      exact hj
    · intro k
      simpa only [hpow i _ (hx0 j), hpow i _ (hx0 k)] using
        hleast k (Finset.mem_univ k)
  refine ⟨y, C.sum_mem (fun i _ => C.pow_mem (hxC i) _), (hmin (Classical.choice inferInstance)).1, ?_⟩
  intro i
  obtain ⟨_, j, hj, hleast⟩ := hmin i
  rw [hj]
  have hej : (0 : ℝ) < e j := by exact_mod_cast (he j).1
  have hei : (e i : ℝ) ≤ N := by exact_mod_cast (he i).2
  refine ⟨mul_pos hej (hxpos j i), lt_of_le_of_lt (hleast i) ?_⟩
  have hmulsmall : (N : ℝ) * ν i (x i) < ε := by
    simpa [mul_comm] using (lt_div_iff₀ hN).mp (hxsmall i)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hei (hxpos i i).le) hmulsmall

end HereditaryAtomicity
