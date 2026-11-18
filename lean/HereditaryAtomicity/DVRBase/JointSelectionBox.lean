import HereditaryAtomicity.DVRBase.JointSelectionDegrees
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Fin.InsertNth
import Mathlib.Data.Fintype.Lattice

/-!
# Joint box avoidance from finite fibers

The block-selection argument uses finite fibres of the given map. Geometric
applications must establish this arithmetic hypothesis for their chosen family.
-/

noncomputable section
open scoped BigOperators
namespace HereditaryAtomicity.DVRBase

/-- A coefficient column distinguishes at least two places. -/
def JointNonconstant {ι : Type*} (η : ι → ℤ) : Prop := ∃ i j, η i ≠ η j

/-- Joint finite fibres mean that every nonconstant integer combination of
the place classes has finite fibers. -/
def JointFiniteFibers {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (θ : ℕ → ι → G) : Prop :=
  ∀ η : ι → ℤ, JointNonconstant η → ∀ g : G,
    Set.Finite {n | ∑ i, η i • θ n i = g}

/-- At one stage, arbitrary bounded combinations of the already selected
columns and every bounded nonconstant new column can be excluded at once.
The desired next index remains in any prescribed infinite candidate set. -/
theorem exists_joint_box_avoidance
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (θ : ℕ → ι → G) (hfinite : JointFiniteFibers θ)
    (j : ℕ) (χ : Fin j → ι → G) (bounds : Fin j → ℕ) (C a : ℕ)
    (candidates : Set ℕ) (hinfinite : candidates.Infinite) :
    ∃ n ∈ candidates,
      ∀ (ν : (l : Fin j) → ι → Fin (bounds l + 1)) (η : ι → Fin (C + 1)),
        JointNonconstant (fun i => (η i : ℤ)) →
        (∑ l : Fin j, ∑ i, (ν l i : ℤ) • χ l i) +
          (∑ i, (η i : ℤ) • (θ n i - θ a i)) ≠ 0 := by
  classical
  let New := {η : ι → Fin (C + 1) // JointNonconstant (fun i => (η i : ℤ))}
  let bad : Set ℕ := ⋃ (ν : (l : Fin j) → ι → Fin (bounds l + 1)) (η : New),
    {n | ∑ i, (η.val i : ℤ) • θ n i =
      (∑ i, (η.val i : ℤ) • θ a i) - ∑ l : Fin j, ∑ i, (ν l i : ℤ) • χ l i}
  have hbad : bad.Finite := Set.finite_iUnion fun ν => Set.finite_iUnion fun η =>
    hfinite (fun i => (η.val i : ℤ)) η.property _
  obtain ⟨n, hn, hnot⟩ := (hinfinite.sdiff hbad).nonempty
  refine ⟨n, hn, fun ν η hη heq => ?_⟩
  apply hnot
  apply Set.mem_iUnion.mpr ⟨ν, ?_⟩
  apply Set.mem_iUnion.mpr ⟨⟨η, hη⟩, ?_⟩
  change (∑ i, (η i : ℤ) • θ n i) =
    (∑ i, (η i : ℤ) • θ a i) - ∑ l : Fin j, ∑ i, (ν l i : ℤ) • χ l i
  simp only [smul_sub, Finset.sum_sub_distrib] at heq
  exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact sub_eq_zero.mp (by abel_nf at heq ⊢; exact heq))

/-- Subtracting a constant column preserves its value when the classes sum
to zero. This is the normalization step that turns spread bounds into boxes. -/
theorem joint_column_normalize
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (χ : ι → G) (hχ : ∑ i, χ i = 0) (η : ι → ℤ) (c : ℤ) :
    (∑ i, (η i - c) • χ i) = ∑ i, η i • χ i := by
  simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hχ, smul_zero, sub_zero]

/-- Integer-coordinate version of one-stage box avoidance. -/
theorem exists_joint_box_avoidance_int
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (θ : ℕ → ι → G) (hfinite : JointFiniteFibers θ)
    (j : ℕ) (χ : Fin j → ι → G) (bounds : Fin j → ℕ) (C a : ℕ)
    (candidates : Set ℕ) (hinfinite : candidates.Infinite) :
    ∃ n ∈ candidates,
      ∀ (ν : Fin j → ι → ℤ) (η : ι → ℤ),
        (∀ l i, 0 ≤ ν l i ∧ ν l i ≤ bounds l) →
        (∀ i, 0 ≤ η i ∧ η i ≤ C) → JointNonconstant η →
        (∑ l : Fin j, ∑ i, ν l i • χ l i) +
          (∑ i, η i • (θ n i - θ a i)) ≠ 0 := by
  obtain ⟨n, hn, h⟩ := exists_joint_box_avoidance θ hfinite j χ bounds C a candidates hinfinite
  refine ⟨n, hn, fun ν η hν hη hnc => ?_⟩
  let ν' (l : Fin j) (i : ι) : Fin (bounds l + 1) :=
    ⟨(ν l i).toNat, by have := (hν l i).2; omega⟩
  let η' (i : ι) : Fin (C + 1) := ⟨(η i).toNat, by have := (hη i).2; omega⟩
  have hν' : ∀ l i, (ν' l i : ℤ) = ν l i := fun l i => Int.toNat_of_nonneg (hν l i).1
  have hη' : ∀ i, (η' i : ℤ) = η i := fun i => Int.toNat_of_nonneg (hη i).1
  simpa only [hν', hη'] using h ν' η' (by simpa only [hη'] using hnc)

/-- The actual finite index history, with its already fixed coefficient bounds. -/
structure JointBoxPrefix (n : ℕ) where
  index : Fin (n + 1) → ℕ
  zero : index 0 = 0
  increasing : StrictMono index
  bound : Fin n → ℕ

namespace JointBoxPrefix

def initial : JointBoxPrefix 0 where
  index := fun _ => 0
  zero := rfl
  increasing := by intro a b hab; omega
  bound := Fin.elim0

/-- Appending an index greater than the final old index retains a valid history. -/
def append {n : ℕ} (s : JointBoxPrefix n) (q C : ℕ)
    (hq : s.index (Fin.last n) < q) : JointBoxPrefix (n + 1) where
  index := Fin.snoc s.index q
  zero := by simpa only [Fin.snoc_apply_zero] using s.zero
  increasing := by
    simpa only [Fin.insertNth_last'] using Fin.strictMono_insertNth_last s.increasing q hq
  bound := Fin.snoc s.bound C

end JointBoxPrefix

section Recursion
variable {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (θ : ℕ → ι → G) (hfinite : JointFiniteFibers θ)
    (bound : (n : ℕ) → (Fin (n + 1) → ℕ) → ℕ)
    (candidates : (n : ℕ) → (Fin (n + 1) → ℕ) → Set ℕ)
    (hinfinite : ∀ n (s : JointBoxPrefix n), (candidates n s.index).Infinite)
    (hgreater : ∀ n (s : JointBoxPrefix n), ∀ q ∈ candidates n s.index,
      s.index (Fin.last n) < q)

/-- A successor index with all the finitely many new box relations excluded. -/
structure JointBoxChoice (n : ℕ) (s : JointBoxPrefix n) where
  next : ℕ
  mem : next ∈ candidates n s.index
  greater : s.index (Fin.last n) < next
  avoids : ∀ (ν : Fin n → ι → ℤ) (η : ι → ℤ),
    (∀ l i, 0 ≤ ν l i ∧ ν l i ≤ s.bound l) →
    (∀ i, 0 ≤ η i ∧ η i ≤ bound n s.index) → JointNonconstant η →
    (∑ l : Fin n, ∑ i, ν l i • (θ (s.index l.succ) i - θ (s.index l.castSucc) i)) +
      (∑ i, η i • (θ next i - θ (s.index (Fin.last n)) i)) ≠ 0

include hfinite hinfinite hgreater

/-- The successor choice follows from joint finite fibres, with no independence or
selection-existence premise. -/
theorem jointBoxChoice_nonempty (n : ℕ) (s : JointBoxPrefix n) :
    Nonempty (JointBoxChoice θ bound candidates n s) := by
  obtain ⟨q, hq, ha⟩ := exists_joint_box_avoidance_int θ hfinite n
    (fun l i => θ (s.index l.succ) i - θ (s.index l.castSucc) i)
    s.bound (bound n s.index) (s.index (Fin.last n)) (candidates n s.index) (hinfinite n s)
  exact ⟨⟨q, hq, hgreater n s q hq, ha⟩⟩

def jointBoxChoose (n : ℕ) (s : JointBoxPrefix n) : JointBoxChoice θ bound candidates n s :=
  Classical.choice (jointBoxChoice_nonempty θ hfinite bound candidates hinfinite hgreater n s)

/-- The infinite recursion stores only the actual preceding finite history. -/
def jointBoxPrefix : (n : ℕ) → JointBoxPrefix n
  | 0 => JointBoxPrefix.initial
  | n + 1 =>
    let s := jointBoxPrefix n
    let q := jointBoxChoose θ hfinite bound candidates hinfinite hgreater n s
    s.append q.next (bound n s.index) q.greater

def jointBoxIndex (n : ℕ) : ℕ :=
  (jointBoxPrefix θ hfinite bound candidates hinfinite hgreater n).index (Fin.last n)

def jointBoxBound (n : ℕ) : ℕ :=
  bound n (jointBoxPrefix θ hfinite bound candidates hinfinite hgreater n).index

@[simp] theorem jointBoxIndex_zero :
    jointBoxIndex θ hfinite bound candidates hinfinite hgreater 0 = 0 := rfl

@[simp] theorem jointBoxIndex_succ (n : ℕ) :
    jointBoxIndex θ hfinite bound candidates hinfinite hgreater (n + 1) =
      (jointBoxChoose θ hfinite bound candidates hinfinite hgreater n
        (jointBoxPrefix θ hfinite bound candidates hinfinite hgreater n)).next := by
  simp only [jointBoxIndex, jointBoxPrefix, JointBoxPrefix.append, Fin.snoc_last]

/-- Every finite history is the prefix of the resulting infinite index sequence. -/
theorem jointBoxPrefix_index (n : ℕ) (i : Fin (n + 1)) :
    (jointBoxPrefix θ hfinite bound candidates hinfinite hgreater n).index i =
      jointBoxIndex θ hfinite bound candidates hinfinite hgreater i.val := by
  induction n with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
  | succ n ih =>
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simpa only [jointBoxPrefix, JointBoxPrefix.append, Fin.snoc_castSucc,
        Fin.val_castSucc] using ih i
    · rfl

/-- Every stored coefficient bound is the bound fixed at its original stage. -/
theorem jointBoxPrefix_bound (n : ℕ) (i : Fin n) :
    (jointBoxPrefix θ hfinite bound candidates hinfinite hgreater n).bound i =
      jointBoxBound θ hfinite bound candidates hinfinite hgreater i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simpa only [jointBoxPrefix, JointBoxPrefix.append, Fin.snoc_castSucc,
        Fin.val_castSucc] using ih i
    · simp only [jointBoxPrefix, JointBoxPrefix.append, Fin.snoc_last, Fin.val_last,
        jointBoxBound]

theorem jointBoxIndex_strictMono :
    StrictMono (jointBoxIndex θ hfinite bound candidates hinfinite hgreater) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [jointBoxIndex_succ]
  exact (jointBoxChoose θ hfinite bound candidates hinfinite hgreater n
    (jointBoxPrefix θ hfinite bound candidates hinfinite hgreater n)).greater

/-- The selected indices belong to the prescribed history-dependent candidate sets. -/
theorem jointBoxIndex_mem (n : ℕ) :
    jointBoxIndex θ hfinite bound candidates hinfinite hgreater (n + 1) ∈
      candidates n (fun i => jointBoxIndex θ hfinite bound candidates hinfinite hgreater i.val) := by
  rw [jointBoxIndex_succ]
  have heq : (jointBoxPrefix θ hfinite bound candidates hinfinite hgreater n).index =
      fun i => jointBoxIndex θ hfinite bound candidates hinfinite hgreater i.val :=
    funext (jointBoxPrefix_index θ hfinite bound candidates hinfinite hgreater n)
  rw [← heq]
  exact (jointBoxChoose θ hfinite bound candidates hinfinite hgreater n
    (jointBoxPrefix θ hfinite bound candidates hinfinite hgreater n)).mem

/-- The actual class increment at one selected block. -/
def jointBoxIncrement (n : ℕ) (i : ι) : G :=
  θ (jointBoxIndex θ hfinite bound candidates hinfinite hgreater (n + 1)) i -
    θ (jointBoxIndex θ hfinite bound candidates hinfinite hgreater n) i

/-- At each stage every bounded array with nonconstant final column has
nonzero total class in the actual selected sequence. -/
theorem jointBox_last_nonconstant (n : ℕ) (ν : Fin (n + 1) → ι → ℤ)
    (hν : ∀ l i, 0 ≤ ν l i ∧ ν l i ≤
      jointBoxBound θ hfinite bound candidates hinfinite hgreater l.val)
    (hlast : JointNonconstant (ν (Fin.last n))) :
    (∑ l : Fin (n + 1), ∑ i, ν l i •
      jointBoxIncrement θ hfinite bound candidates hinfinite hgreater l.val i) ≠ 0 := by
  let s := jointBoxPrefix θ hfinite bound candidates hinfinite hgreater n
  let q := jointBoxChoose θ hfinite bound candidates hinfinite hgreater n s
  have h := q.avoids (fun l => ν l.castSucc) (ν (Fin.last n))
    (fun l i => ⟨(hν l.castSucc i).1, by
      rw [jointBoxPrefix_bound]
      exact (hν l.castSucc i).2⟩)
    (fun i => hν (Fin.last n) i) hlast
  rw [Fin.sum_univ_castSucc]
  simpa only [s, q, jointBoxPrefix_index, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    jointBoxIncrement, jointBoxIndex_succ] using h

/-- Constant coefficient columns contribute zero because every selected
increment is a difference of two equal total place classes. -/
theorem jointBoxIncrement_sum
    (hsum : ∀ n, ∑ i, θ n i = ∑ i, θ 0 i) (n : ℕ) :
    (∑ i, jointBoxIncrement θ hfinite bound candidates hinfinite hgreater n i) = 0 := by
  simp only [jointBoxIncrement, Finset.sum_sub_distrib, hsum, sub_self]

/-- Full finite-array independence for normalized boxes, including arrays
whose final columns are constant. -/
theorem jointBox_normalized_independent [Nonempty ι]
    (hsum : ∀ n, ∑ i, θ n i = ∑ i, θ 0 i)
    (n : ℕ) (ν : Fin n → ι → ℤ)
    (hν : ∀ l i, 0 ≤ ν l i ∧ ν l i ≤
      jointBoxBound θ hfinite bound candidates hinfinite hgreater l.val)
    (hnc : ∃ l, JointNonconstant (ν l)) :
    (∑ l : Fin n, ∑ i, ν l i •
      jointBoxIncrement θ hfinite bound candidates hinfinite hgreater l.val i) ≠ 0 := by
  classical
  induction n with
  | zero => obtain ⟨l, _⟩ := hnc; exact Fin.elim0 l
  | succ n ih =>
    by_cases hlast : JointNonconstant (ν (Fin.last n))
    · exact jointBox_last_nonconstant θ hfinite bound candidates hinfinite hgreater n ν hν hlast
    · let i₀ : ι := Classical.choice inferInstance
      have hconstant : ∀ i, ν (Fin.last n) i = ν (Fin.last n) i₀ := by
        intro i
        by_contra hi
        exact hlast ⟨i, i₀, hi⟩
      have hzero : (∑ i, ν (Fin.last n) i •
          jointBoxIncrement θ hfinite bound candidates hinfinite hgreater n i) = 0 := by
        simp only [hconstant, ← Finset.smul_sum,
          jointBoxIncrement_sum θ hfinite bound candidates hinfinite hgreater hsum, smul_zero]
      rw [Fin.sum_univ_castSucc, Fin.val_last, hzero, add_zero]
      apply ih (fun l => ν l.castSucc) (fun l i => hν l.castSucc i)
      obtain ⟨l, hl⟩ := hnc
      obtain ⟨l, rfl⟩ | rfl := l.eq_castSucc_or_eq_last
      · exact ⟨l, hl⟩
      · exact (hlast hl).elim

/-- joint selection in its full spread-bound form. The pairwise inequalities are exactly
the finite-column condition `max ν - min ν ≤ C`. Constant columns are allowed
and need no absolute coefficient bound. -/
theorem jointBox_spread_independent [Nonempty ι]
    (hsum : ∀ n, ∑ i, θ n i = ∑ i, θ 0 i)
    (n : ℕ) (ν : Fin n → ι → ℤ)
    (hspread : ∀ l i j, ν l i - ν l j ≤
      jointBoxBound θ hfinite bound candidates hinfinite hgreater l.val)
    (hnc : ∃ l, JointNonconstant (ν l)) :
    (∑ l : Fin n, ∑ i, ν l i •
      jointBoxIncrement θ hfinite bound candidates hinfinite hgreater l.val i) ≠ 0 := by
  choose m hm using fun l => Finite.exists_min (ν l)
  let μ (l : Fin n) (i : ι) : ℤ := ν l i - ν l (m l)
  have hμ : ∀ l i, 0 ≤ μ l i ∧ μ l i ≤
      jointBoxBound θ hfinite bound candidates hinfinite hgreater l.val := by
    intro l i
    exact ⟨sub_nonneg.mpr (hm l i), hspread l i (m l)⟩
  have hμnc : ∃ l, JointNonconstant (μ l) := by
    obtain ⟨l, i, j, hij⟩ := hnc
    exact ⟨l, i, j, fun h => hij (sub_left_injective h)⟩
  have h := jointBox_normalized_independent θ hfinite bound candidates hinfinite hgreater
    hsum n μ hμ hμnc
  have heq : (∑ l : Fin n, ∑ i, μ l i •
      jointBoxIncrement θ hfinite bound candidates hinfinite hgreater l.val i) =
      ∑ l : Fin n, ∑ i, ν l i •
        jointBoxIncrement θ hfinite bound candidates hinfinite hgreater l.val i := by
    apply Finset.sum_congr rfl
    intro l _
    exact joint_column_normalize _
      (jointBoxIncrement_sum θ hfinite bound candidates hinfinite hgreater hsum l.val)
      (ν l) (ν l (m l))
  exact heq ▸ h

/-- The stored stage bound is literally the prescribed bound evaluated on
the selected finite index history. -/
theorem jointBoxBound_eq (n : ℕ) :
    jointBoxBound θ hfinite bound candidates hinfinite hgreater n =
      bound n (fun i => jointBoxIndex θ hfinite bound candidates hinfinite hgreater i.val) := by
  unfold jointBoxBound
  congr 1
  exact funext (jointBoxPrefix_index θ hfinite bound candidates hinfinite hgreater n)

end Recursion

/-- Joint box independence with exactly the original finite-fiber hypothesis,
zero-sum increment identity, and arbitrary finite-history-dependent bounds and
infinite candidate sets. Every finite array with a nonconstant column and the
prescribed column-spread bounds has nonzero class. -/
theorem exists_joint_box_independent
    {ι G : Type*} [Fintype ι] [Nonempty ι] [AddCommGroup G]
    (θ : ℕ → ι → G) (hfinite : JointFiniteFibers θ)
    (hsum : ∀ n, ∑ i, θ n i = ∑ i, θ 0 i)
    (bound : (n : ℕ) → (Fin (n + 1) → ℕ) → ℕ)
    (candidates : (n : ℕ) → (Fin (n + 1) → ℕ) → Set ℕ)
    (hinfinite : ∀ n (s : Fin (n + 1) → ℕ), s 0 = 0 → StrictMono s →
      (candidates n s).Infinite)
    (hgreater : ∀ n (s : Fin (n + 1) → ℕ), s 0 = 0 → StrictMono s →
      ∀ q ∈ candidates n s, s (Fin.last n) < q) :
    ∃ f : ℕ → ℕ, f 0 = 0 ∧ StrictMono f ∧
      (∀ n, f (n + 1) ∈ candidates n (fun i => f i.val)) ∧
      ∀ n (ν : Fin n → ι → ℤ),
        (∀ l i j, ν l i - ν l j ≤ bound l.val (fun r => f r.val)) →
        (∃ l, JointNonconstant (ν l)) →
        (∑ l : Fin n, ∑ i, ν l i • (θ (f (l.val + 1)) i - θ (f l.val) i)) ≠ 0 := by
  let hi := fun n (s : JointBoxPrefix n) => hinfinite n s.index s.zero s.increasing
  let hg := fun n (s : JointBoxPrefix n) => hgreater n s.index s.zero s.increasing
  refine ⟨jointBoxIndex θ hfinite bound candidates hi hg, rfl,
    jointBoxIndex_strictMono θ hfinite bound candidates hi hg,
    jointBoxIndex_mem θ hfinite bound candidates hi hg, ?_⟩
  intro n ν hν hnc
  apply jointBox_spread_independent θ hfinite bound candidates hi hg hsum n ν _ hnc
  intro l i j
  rw [jointBoxBound_eq]
  exact hν l i j

/-- Scalar block selection for a map with finite fibres. -/
theorem exists_box_independent_of_finite_fibers
    {G : Type*} [AddCommGroup G] (θ : ℕ → G)
    (hfinite : ∀ h : ℤ, h ≠ 0 → ∀ g : G, Set.Finite {n | h • θ n = g})
    (bound : (n : ℕ) → (Fin (n + 1) → ℕ) → ℕ)
    (candidates : (n : ℕ) → (Fin (n + 1) → ℕ) → Set ℕ)
    (hinfinite : ∀ n (s : Fin (n + 1) → ℕ), s 0 = 0 → StrictMono s →
      (candidates n s).Infinite)
    (hgreater : ∀ n (s : Fin (n + 1) → ℕ), s 0 = 0 → StrictMono s →
      ∀ q ∈ candidates n s, s (Fin.last n) < q) :
    ∃ f : ℕ → ℕ, f 0 = 0 ∧ StrictMono f ∧
      (∀ n, f (n + 1) ∈ candidates n (fun i => f i.val)) ∧
      ∀ n (ν : Fin n → ℤ),
        (∀ l, |ν l| ≤ bound l.val (fun r => f r.val)) →
        (∃ l, ν l ≠ 0) →
        (∑ l : Fin n, ν l • (θ (f (l.val + 1)) - θ (f l.val))) ≠ 0 := by
  classical
  let Θ (n : ℕ) (i : Fin 2) : G := if i = 0 then θ n else -θ n
  have hΘ : JointFiniteFibers Θ := by
    intro η hη g
    have hne : η 0 - η 1 ≠ 0 := by
      intro h
      have heq := sub_eq_zero.mp h
      obtain ⟨i, j, hij⟩ := hη
      fin_cases i <;> fin_cases j <;> simp_all
    simpa only [Θ, Fin.sum_univ_two, ↓reduceIte, Fin.zero_ne_one, one_ne_zero,
      smul_neg, ← sub_eq_add_neg, ← sub_smul] using hfinite (η 0 - η 1) hne g
  have hsum : ∀ n, (∑ i, Θ n i) = ∑ i, Θ 0 i := by
    intro n
    simp [Θ, Fin.sum_univ_two]
  obtain ⟨f, hf0, hfmono, hmem, hind⟩ := exists_joint_box_independent Θ hΘ hsum
    bound candidates hinfinite hgreater
  refine ⟨f, hf0, hfmono, hmem, fun n ν hν hne => ?_⟩
  let μ (l : Fin n) (i : Fin 2) : ℤ := if i = 0 then ν l else 0
  have hspread : ∀ l i j, μ l i - μ l j ≤ bound l.val (fun r => f r.val) := by
    intro l i j
    have h := abs_le.mp (hν l)
    fin_cases i <;> fin_cases j <;> simp only [μ] <;> omega
  have hnc : ∃ l, JointNonconstant (μ l) := by
    obtain ⟨l, hl⟩ := hne
    exact ⟨l, 0, 1, by simpa [μ] using hl⟩
  simpa [Θ, μ, Fin.sum_univ_two] using hind n μ hspread hnc

end HereditaryAtomicity.DVRBase
