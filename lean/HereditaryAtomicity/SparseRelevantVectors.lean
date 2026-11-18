import HereditaryAtomicity.SparseSelection

/-!
# Relevant exponent vectors for sparse conductor cuts

Negative generator exponents are bounded below by minus one. At most one
endpoint or returned-unit factor occurs. These are the precise vectors needed
when a high generator is divided once by fresh selected source elements.
-/

noncomputable section
namespace HereditaryAtomicity

/-- A pointwise operation preserves finite profile range. -/
theorem finite_range_profile_binary {X A B C : Type*} (f : X → A) (g : X → B)
    (hf : (Set.range f).Finite) (hg : (Set.range g).Finite) (op : A → B → C) :
    (Set.range (fun x => op (f x) (g x))).Finite := by
  apply ((hf.prod hg).image (fun p => op p.1 p.2)).subset
  rintro y ⟨x, rfl⟩
  exact ⟨(f x, g x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩


/-- Exponent data; scalar order is kept separate from the algebraic coefficient. -/
@[ext] structure SparseRelevantVector where
  scalar : ℕ
  powers : ℕ →₀ ℤ
  endpoint : ℕ
  unit : ℕ
  deriving DecidableEq

namespace SparseRelevantVector

def Relevant (w : SparseRelevantVector) : Prop :=
  w.endpoint + w.unit ≤ 1 ∧ ∀ j, -1 ≤ w.powers j

def Supported (n : ℕ) (w : SparseRelevantVector) : Prop :=
  ∀ j, n ≤ j → w.powers j = 0

def eval {X : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ)
    (P : X) (w : SparseRelevantVector) : ℝ :=
  (w.scalar : ℝ) + w.powers.sum (fun j k => (k : ℝ) * γ j P) +
    (w.endpoint : ℝ) * ξ P + (w.unit : ℝ) * σ P

end SparseRelevantVector

/-- Finite-stage exponent data used during selection. -/
@[ext] structure SparseStageVector (n : ℕ) where
  scalar : ℕ
  powers : Fin n → ℤ
  endpoint : ℕ
  unit : ℕ

namespace SparseStageVector

def Relevant {n : ℕ} (w : SparseStageVector n) : Prop :=
  w.endpoint + w.unit ≤ 1 ∧ ∀ j, -1 ≤ w.powers j

def eval {X : Type*} {n : ℕ} (γ : Fin n → X → ℝ) (ξ σ : X → ℝ)
    (P : X) (w : SparseStageVector n) : ℝ :=
  (w.scalar : ℝ) + (∑ j, (w.powers j : ℝ) * γ j P) +
    (w.endpoint : ℝ) * ξ P + (w.unit : ℝ) * σ P

def truncate {n : ℕ} (w : SparseStageVector (n+1)) : SparseStageVector n :=
  ⟨w.scalar, fun j => w.powers j.castSucc, w.endpoint, w.unit⟩

theorem relevant_truncate {n : ℕ} {w : SparseStageVector (n+1)}
    (h : w.Relevant) : w.truncate.Relevant :=
  ⟨h.1, fun j => h.2 j.castSucc⟩

theorem eval_snoc {X : Type*} {n : ℕ} (γ : Fin n → X → ℝ)
    (g ξ σ : X → ℝ) (P : X) (w : SparseStageVector (n+1)) :
    eval (Fin.snoc γ g) ξ σ P w = eval γ ξ σ P w.truncate +
      (w.powers (Fin.last n) : ℝ) * g P := by
  simp only [eval, truncate, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- Integer exponents bounded below by -1 form a locally finite set of values. -/
theorem finite_integer_combination_values {n : ℕ} (γ : Fin n → ℝ)
    (hγ : ∀ j, 0 < γ j) (B : ℝ) :
    Set.Finite {x : ℝ | ∃ r : ℕ, ∃ k : Fin n → ℤ,
      (∀ j, -1 ≤ k j) ∧ x = (r : ℝ) + ∑ j, (k j : ℝ) * γ j ∧ x ≤ B} := by
  classical
  let L := {x : ℝ | ∃ r : ℕ, ∃ d : Fin n → ℕ,
    x = sparseCombination γ r d ∧ x ≤ B + ∑ j, γ j}
  have hL : L.Finite := finite_sparseCombination_le γ hγ _
  apply (hL.image (fun x => x - ∑ j, γ j)).subset
  rintro x ⟨r, k, hk, rfl, hbound⟩
  let d : Fin n → ℕ := fun j => (k j + 1).toNat
  have hd (j) : (d j : ℝ) = (k j : ℝ) + 1 := by
    have hdZ : (d j : ℤ) = k j + 1 := Int.toNat_of_nonneg (by have := hk j; omega)
    exact_mod_cast hdZ
  have heq : sparseCombination γ r d = (r : ℝ) + ∑ j, (k j : ℝ) * γ j + ∑ j, γ j := by
    simp only [sparseCombination, hd, add_mul, one_mul, Finset.sum_add_distrib]
    ring
  refine ⟨sparseCombination γ r d, ?_, ?_⟩
  · exact ⟨r, d, rfl, by rw [heq]; linarith⟩
  · rw [heq]
    ring

/-- For one fixed profile pattern there are only finitely many relevant values
below a fixed window. -/
theorem finite_relevant_values {n : ℕ} (γ : Fin n → ℝ)
    (hγ : ∀ j, 0 < γ j) (ξ σ B : ℝ) :
    Set.Finite {x : ℝ | ∃ w : SparseStageVector n,
      w.Relevant ∧ x = eval (fun j (_ : Unit) => γ j) (fun _ => ξ) (fun _ => σ) () w ∧ x ≤ B} := by
  classical
  let L (d : ℝ) := {x : ℝ | ∃ r : ℕ, ∃ k : Fin n → ℤ,
    (∀ j, -1 ≤ k j) ∧ x = (r : ℝ) + ∑ j, (k j : ℝ) * γ j ∧ x ≤ B-d}
  have hL (d) : (L d).Finite := finite_integer_combination_values γ hγ (B-d)
  have hfin : (((L 0).image (fun x => x)) ∪ ((L ξ).image (fun x => x+ξ)) ∪
      ((L σ).image (fun x => x+σ))).Finite :=
    ((hL 0).image _).union ((hL ξ).image _) |>.union ((hL σ).image _)
  apply hfin.subset
  rintro x ⟨w, hw, rfl, hb⟩
  rcases w with ⟨r,k,e,d⟩
  simp only [Relevant] at hw
  simp only [eval] at hb ⊢
  have hed : (e = 0 ∧ d = 0) ∨ (e = 1 ∧ d = 0) ∨ (e = 0 ∧ d = 1) := by omega
  rcases hed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simp only [Nat.cast_zero, zero_mul, add_zero] at hb ⊢
    exact Or.inl (Or.inl ⟨_, ⟨r,k,hw.2,rfl,by simpa using hb⟩, rfl⟩)
  · simp only [Nat.cast_zero, Nat.cast_one, one_mul, zero_mul, add_zero] at hb ⊢
    exact Or.inl (Or.inr ⟨_, ⟨r,k,hw.2,rfl,by linarith⟩, rfl⟩)
  · simp only [Nat.cast_zero, Nat.cast_one, one_mul, zero_mul, add_zero] at hb ⊢
    exact Or.inr ⟨_, ⟨r,k,hw.2,rfl,by linarith⟩, rfl⟩

/-- Finite ranges of individual profiles give finitely many relevant values
in a fixed window, simultaneously over the entire branch space. -/
theorem finite_profile_relevant_values {X : Type*} {n : ℕ}
    (γ : Fin n → X → ℝ) (ξ σ : X → ℝ)
    (hγ : ∀ j P, 0 < γ j P)
    (hγfin : ∀ j, (Set.range (γ j)).Finite)
    (hξ : (Set.range ξ).Finite) (hσ : (Set.range σ).Finite) (B : ℝ) :
    Set.Finite {x : ℝ | ∃ P, ∃ w : SparseStageVector n,
      w.Relevant ∧ x = eval γ ξ σ P w ∧ x ≤ B} := by
  classical
  let patterns := Set.range (fun P => ((fun j => γ j P), ξ P, σ P))
  have hfun : (Set.range (fun P => fun j => γ j P)).Finite := by
    apply (Set.Finite.pi' hγfin).subset
    rintro f ⟨P,rfl⟩ j
    exact ⟨P,rfl⟩
  have hp : patterns.Finite := by
    apply (hfun.prod (hξ.prod hσ)).subset
    rintro p ⟨P,rfl⟩
    exact ⟨⟨P,rfl⟩, ⟨P,rfl⟩, ⟨P,rfl⟩⟩
  let V (p : (Fin n → ℝ) × ℝ × ℝ) := {x : ℝ | ∃ w : SparseStageVector n,
    w.Relevant ∧ x = eval (fun j (_ : Unit) => p.1 j)
      (fun _ => p.2.1) (fun _ => p.2.2) () w ∧ x ≤ B}
  have hv : (⋃ p ∈ patterns, V p).Finite := hp.biUnion (by
    rintro p ⟨P,rfl⟩
    exact finite_relevant_values _ (fun j => hγ j P) _ _ _)
  apply hv.subset
  rintro x ⟨P,w,hw,rfl,hb⟩
  exact Set.mem_iUnion.mpr ⟨((fun j => γ j P), ξ P, σ P),
    Set.mem_iUnion.mpr ⟨⟨P,rfl⟩, ⟨w,hw,rfl,hb⟩⟩⟩

/-- Injectivity is required only for relevant vectors in the current window. -/
def LowInjective {X : Type*} {n : ℕ} (γ : Fin n → X → ℝ)
    (ξ σ : X → ℝ) (θ : ℝ) : Prop :=
  ∀ P (w z : SparseStageVector n), w.Relevant → z.Relevant →
    eval γ ξ σ P w ≤ θ → eval γ ξ σ P z ≤ θ →
    eval γ ξ σ P w = eval γ ξ σ P z → w = z

/-- A finite obstruction set suffices to extend a sparse profile prefix.
The shrinking window compensates exactly for an exponent equal to -1. -/
theorem exists_extension_obstructions {X : Type*} {n : ℕ}
    (γ : Fin n → X → ℝ) (ξ σ : X → ℝ)
    (hγ : ∀ j P, 0 < γ j P)
    (hγfin : ∀ j, (Set.range (γ j)).Finite)
    (hξ : (Set.range ξ).Finite) (hσ : (Set.range σ).Finite)
    (θ : ℝ) (hinj : LowInjective γ ξ σ θ) :
    ∃ E : Finset ℝ, ∀ (g : X → ℝ) (η : ℝ),
      (∀ P, 0 < g P ∧ g P < η) →
      (∀ P (q : ℕ), 0 < q → (q : ℝ) * g P ∉ E) →
      LowInjective (Fin.snoc γ g) ξ σ (θ-η) := by
  classical
  let L := (finite_profile_relevant_values γ ξ σ hγ hγfin hξ hσ θ).toFinset
  have hL (P) (w : SparseStageVector n) (hw : w.Relevant)
      (hb : eval γ ξ σ P w ≤ θ) : eval γ ξ σ P w ∈ L :=
    (finite_profile_relevant_values γ ξ σ hγ hγfin hξ hσ θ).mem_toFinset.mpr
      ⟨P,w,hw,rfl,hb⟩
  let E := L.biUnion (fun u => L.image (fun v => v-u))
  refine ⟨E, ?_⟩
  intro g η hg hav P w z hw hz hwb hzb heq
  simp only [eval_snoc] at hwb hzb heq
  have hwlast : (-1 : ℝ) ≤ w.powers (Fin.last n) := by exact_mod_cast hw.2 (Fin.last n)
  have hzlast : (-1 : ℝ) ≤ z.powers (Fin.last n) := by exact_mod_cast hz.2 (Fin.last n)
  have hwold : eval γ ξ σ P w.truncate ≤ θ := by
    nlinarith [hg P]
  have hzold : eval γ ξ σ P z.truncate ≤ θ := by
    nlinarith [hg P]
  have hwL := hL P w.truncate (relevant_truncate hw) hwold
  have hzL := hL P z.truncate (relevant_truncate hz) hzold
  have hlast : w.powers (Fin.last n) = z.powers (Fin.last n) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let q := (z.powers (Fin.last n) - w.powers (Fin.last n)).toNat
      have hqZ : (q : ℤ) = z.powers (Fin.last n) - w.powers (Fin.last n) :=
        Int.toNat_of_nonneg (by omega)
      have hq : 0 < q := by omega
      have hqR : (q : ℝ) = (z.powers (Fin.last n) : ℝ) - (w.powers (Fin.last n) : ℝ) := by
        exact_mod_cast hqZ
      apply hav P q hq
      have hdiff : (q : ℝ) * g P = eval γ ξ σ P w.truncate - eval γ ξ σ P z.truncate := by
        rw [hqR]
        nlinarith [heq]
      rw [hdiff]
      exact Finset.mem_biUnion.mpr ⟨_,hzL,Finset.mem_image.mpr ⟨_,hwL,rfl⟩⟩
    · let q := (w.powers (Fin.last n) - z.powers (Fin.last n)).toNat
      have hqZ : (q : ℤ) = w.powers (Fin.last n) - z.powers (Fin.last n) :=
        Int.toNat_of_nonneg (by omega)
      have hq : 0 < q := by omega
      have hqR : (q : ℝ) = (w.powers (Fin.last n) : ℝ) - (z.powers (Fin.last n) : ℝ) := by
        exact_mod_cast hqZ
      apply hav P q hq
      have hdiff : (q : ℝ) * g P = eval γ ξ σ P z.truncate - eval γ ξ σ P w.truncate := by
        rw [hqR]
        nlinarith [heq]
      rw [hdiff]
      exact Finset.mem_biUnion.mpr ⟨_,hwL,Finset.mem_image.mpr ⟨_,hzL,rfl⟩⟩
  have hold : w.truncate = z.truncate := hinj P _ _ (relevant_truncate hw)
    (relevant_truncate hz) hwold hzold (by rw [hlast] at heq; linarith)
  have hs : w.scalar = z.scalar := congrArg (fun v : SparseStageVector n => v.scalar) hold
  have he : w.endpoint = z.endpoint := congrArg (fun v : SparseStageVector n => v.endpoint) hold
  have hu : w.unit = z.unit := congrArg (fun v : SparseStageVector n => v.unit) hold
  have hp := congrArg SparseStageVector.powers hold
  apply SparseStageVector.ext hs _ he hu
  funext j
  exact Fin.lastCases hlast (fun i => congrFun hp i) j

/-- A value strictly between consecutive natural integers cannot become a
natural integer after adding a natural scalar. -/
theorem nat_add_ne_of_between {c : ℕ} {x : ℝ} (hx : (c : ℝ) < x ∧ x < c+1)
    (r s : ℕ) : (r : ℝ) + x ≠ s := by
  intro heq
  have hlo : r+c < s := by
    exact_mod_cast (show (r : ℝ) + c < s by linarith [hx.1])
  have hhi : s < r+c+1 := by
    exact_mod_cast (show (s : ℝ) < r+c+1 by linarith [hx.2])
  omega

/-- The endpoint is nonintegral and the unit increment starts above the
initial window. This supplies the empty prefix of the sparse construction. -/
theorem lowInjective_empty {X : Type*} (c : ℕ) (hc : 0 < c) (ξ σ : X → ℝ)
    (hξ : ∀ P, (c : ℝ) < ξ P ∧ ξ P < c+1)
    (hσ : ∀ P, 4*(c : ℝ) ≤ σ P) :
    LowInjective (fun j : Fin 0 => Fin.elim0 j) ξ σ (3*c) := by
  intro P w z hw hz hwb hzb heq
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hξpos : 0 < ξ P := lt_trans hcR (hξ P).1
  have hσpos : 0 < σ P := by linarith [hσ P]
  simp only [eval, Fin.sum_univ_zero, add_zero] at hwb hzb heq
  have unit_zero (v : SparseStageVector 0)
      (hv : (v.scalar : ℝ) + v.endpoint * ξ P + v.unit * σ P ≤ 3*c) : v.unit=0 := by
    by_contra h
    have hd : (1 : ℝ) ≤ v.unit := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
    have hnonneg : 0 ≤ (v.endpoint : ℝ) * ξ P := mul_nonneg (Nat.cast_nonneg _) hξpos.le
    nlinarith [Nat.cast_nonneg (α := ℝ) v.scalar, hσ P]
  have hwunit := unit_zero w hwb
  have hzunit := unit_zero z hzb
  have hew : w.endpoint=0 ∨ w.endpoint=1 := by have := hw.1; omega
  have hez : z.endpoint=0 ∨ z.endpoint=1 := by have := hz.1; omega
  have hsc : w.scalar=z.scalar ∧ w.endpoint=z.endpoint := by
    rcases hew with hew | hew <;> rcases hez with hez | hez
    · simp only [hwunit,hzunit,hew,hez,Nat.cast_zero,zero_mul,add_zero] at heq
      exact ⟨by exact_mod_cast heq, hew.trans hez.symm⟩
    · simp only [hwunit,hzunit,hew,hez,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero] at heq
      exact False.elim (nat_add_ne_of_between (hξ P) z.scalar w.scalar heq.symm)
    · simp only [hwunit,hzunit,hew,hez,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero] at heq
      exact False.elim (nat_add_ne_of_between (hξ P) w.scalar z.scalar heq)
    · simp only [hwunit,hzunit,hew,hez,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero] at heq
      exact ⟨by exact_mod_cast (add_right_cancel heq), hew.trans hez.symm⟩
  exact SparseStageVector.ext hsc.1 (Subsingleton.elim _ _) hsc.2 (hwunit.trans hzunit.symm)

end SparseStageVector

namespace SparseRelevantVector

def toStage (n : ℕ) (w : SparseRelevantVector) : SparseStageVector n :=
  ⟨w.scalar, fun j => w.powers j, w.endpoint, w.unit⟩

theorem relevant_toStage {w : SparseRelevantVector} (hw : w.Relevant) (n : ℕ) :
    (w.toStage n).Relevant := ⟨hw.1, fun j => hw.2 j⟩

theorem eval_toStage {X : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ)
    (P : X) (w : SparseRelevantVector) (n : ℕ)
    (hw : ∀ j ∈ w.powers.support, j < n) :
    w.eval γ ξ σ P = (w.toStage n).eval (fun j : Fin n => γ j) ξ σ P := by
  classical
  have hsum : w.powers.sum (fun j k => (k : ℝ)*γ j P) =
      ∑ j : Fin n, (w.powers j : ℝ)*γ j P := by
    rw [Finsupp.sum_of_support_subset w.powers
      (show w.powers.support ⊆ Finset.range n from fun j hj => Finset.mem_range.mpr (hw j hj))
      (fun j k => (k : ℝ)*γ j P) (by simp)]
    exact (Fin.sum_univ_eq_sum_range (fun j => (w.powers j : ℝ)*γ j P) n).symm
  simp only [eval,SparseStageVector.eval,toStage,hsum]

/-- Low-window injectivity for all finitely supported relevant vectors. -/
def LowInjective {X : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ) (B : ℝ) : Prop :=
  ∀ P (w z : SparseRelevantVector), w.Relevant → z.Relevant →
    w.eval γ ξ σ P ≤ B → z.eval γ ξ σ P ≤ B →
    w.eval γ ξ σ P = z.eval γ ξ σ P → w=z

/-- A uniform lower bound on the prefix windows gives injectivity for arbitrary
finite supports. -/
theorem lowInjective_of_prefixes {X : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ)
    (θ : ℕ → ℝ) (B : ℝ) (hθ : ∀ n, B ≤ θ n)
    (hinj : ∀ n, SparseStageVector.LowInjective (fun j : Fin n => γ j) ξ σ (θ n)) :
    LowInjective γ ξ σ B := by
  classical
  intro P w z hw hz hwb hzb heq
  let n := (w.powers.support ∪ z.powers.support).sup id + 1
  have hwn : ∀ j ∈ w.powers.support, j < n := by
    intro j hj
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_union_left _ hj))
  have hzn : ∀ j ∈ z.powers.support, j < n := by
    intro j hj
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_union_right _ hj))
  rw [eval_toStage γ ξ σ P w n hwn] at hwb heq
  rw [eval_toStage γ ξ σ P z n hzn] at hzb heq
  have hs := hinj n P (w.toStage n) (z.toStage n) (relevant_toStage hw n)
    (relevant_toStage hz n) (hwb.trans (hθ n)) (hzb.trans (hθ n)) heq
  have hscalar : w.scalar=z.scalar := congrArg (fun v : SparseStageVector n => v.scalar) hs
  have hendpoint : w.endpoint=z.endpoint := congrArg (fun v : SparseStageVector n => v.endpoint) hs
  have hunit : w.unit=z.unit := congrArg (fun v : SparseStageVector n => v.unit) hs
  have hp := congrArg (fun v : SparseStageVector n => v.powers) hs
  apply SparseRelevantVector.ext hscalar _ hendpoint hunit
  apply Finsupp.ext
  intro j
  by_cases hj : j<n
  · exact congrFun hp ⟨j,hj⟩
  · have hw0 : w.powers j=0 := Finsupp.notMem_support_iff.mp (fun h => hj (hwn j h))
    have hz0 : z.powers j=0 := Finsupp.notMem_support_iff.mp (fun h => hj (hzn j h))
    exact hw0.trans hz0.symm

/-- Every fixed relevant expression retains finite profile range. -/
theorem finite_range_eval {X : Type*} (γ : ℕ → X → ℝ) (ξ σ : X → ℝ)
    (hγ : ∀ j, (Set.range (γ j)).Finite)
    (hξ : (Set.range ξ).Finite) (hσ : (Set.range σ).Finite) (w : SparseRelevantVector) :
    (Set.range (fun P => w.eval γ ξ σ P)).Finite := by
  classical
  have hsum (s : Finset ℕ) : (Set.range (fun P => ∑ j ∈ s, (w.powers j : ℝ)*γ j P)).Finite := by
    induction s using Finset.induction_on with
    | empty =>
      apply (Set.finite_singleton (0 : ℝ)).subset
      rintro x ⟨P,rfl⟩
      simp
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      have hjfin : (Set.range (fun P => (w.powers j : ℝ)*γ j P)).Finite := by
        rw [Set.range_comp']
        exact (hγ j).image _
      exact finite_range_profile_binary _ _ hjfin ih (fun x y : ℝ => x+y)
  have hbase : (Set.range (fun P => (w.scalar : ℝ) +
      ∑ j ∈ w.powers.support, (w.powers j : ℝ)*γ j P)).Finite := by
    rw [Set.range_comp']
    exact (hsum w.powers.support).image _
  have hend : (Set.range (fun P => (w.endpoint : ℝ)*ξ P)).Finite := by
    rw [Set.range_comp']
    exact hξ.image _
  have hunit : (Set.range (fun P => (w.unit : ℝ)*σ P)).Finite := by
    rw [Set.range_comp']
    exact hσ.image _
  exact finite_range_profile_binary _ _
    (finite_range_profile_binary _ _ hbase hend (fun x y : ℝ => x+y)) hunit (fun x y : ℝ => x+y)

end SparseRelevantVector
end HereditaryAtomicity
