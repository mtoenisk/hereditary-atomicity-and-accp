import HereditaryAtomicity.SparseProductCut
import HereditaryAtomicity.SparseRelevantVectors
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.Order

/-!
# Collected Laurent terms for conductor cuts

Coefficients are collected at the actual Laurent exponent key before their
DVR order is measured. This is essential when several products have one key.
-/

open scoped NNReal

noncomputable section
namespace HereditaryAtomicity

abbrev SparseLaurentKey := (ℕ →₀ ℤ) × ℕ × ℕ

namespace SparseLaurentKey

def Pure (w : SparseLaurentKey) : Prop :=
  w.2.1 = 0 ∧ w.2.2 = 0 ∧ ∀ j, 0 ≤ w.1 j

def Relevant (w : SparseLaurentKey) : Prop :=
  w.2.1 + w.2.2 ≤ 1 ∧ ∀ j, -1 ≤ w.1 j

theorem pure_zero : Pure 0 := by simp [Pure]

theorem Pure.relevant {w : SparseLaurentKey} (h : Pure w) : Relevant w := by
  rcases h with ⟨h₁,h₂,h₃⟩
  exact ⟨by simp [h₁,h₂], fun j => (by omega : (-1:ℤ) ≤ 0).trans (h₃ j)⟩

theorem Pure.add {u w : SparseLaurentKey} (hu : Pure u) (hw : Pure w) : Pure (u+w) := by
  refine ⟨by simp [hu.1,hw.1], by simp [hu.2.1,hw.2.1], ?_⟩
  intro j
  exact add_nonneg (hu.2.2 j) (hw.2.2 j)

theorem Pure.add_relevant {u w : SparseLaurentKey} (hu : Pure u)
    (hw : Relevant w) : Relevant (u+w) := by
  refine ⟨by simpa [hu.1,hu.2.1] using hw.1, ?_⟩
  intro j
  change -1 ≤ u.1 j + w.1 j
  linarith [hu.2.2 j,hw.2 j]

theorem Relevant.add_pure {u w : SparseLaurentKey} (hu : Relevant u)
    (hw : Pure w) : Relevant (u+w) := by
  simpa only [add_comm] using hw.add_relevant hu

end SparseLaurentKey

variable {K : Type*} [Field K]

/-- Evaluate the Laurent key in actual nonzero field elements. -/
def sparseLaurentMonomial (a : ℕ → Kˣ) (x y : Kˣ) :
    Multiplicative SparseLaurentKey →* K where
  toFun w := ((w.toAdd.1.prod fun j k => a j ^ k) * x ^ w.toAdd.2.1 * y ^ w.toAdd.2.2 : Kˣ)
  map_one' := by simp
  map_mul' u w := by
    rw [← Units.val_mul]
    apply congrArg Units.val
    change ((u.toAdd.1 + w.toAdd.1).prod fun j k => a j ^ k) *
      x ^ (u.toAdd.2.1 + w.toAdd.2.1) * y ^ (u.toAdd.2.2 + w.toAdd.2.2) = _
    rw [Finsupp.prod_add_index (by simp) (by intros; simp [zpow_add])]
    simp only [pow_add]
    ac_rfl

/-- Evaluate a collected Laurent polynomial over a literal coefficient ring. -/
def sparseLaurentEval (A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ) :
    AddMonoidAlgebra A SparseLaurentKey →+* K :=
  AddMonoidAlgebra.liftNCRingHom A.subtype (sparseLaurentMonomial a x y)
    (fun _ _ => Commute.all _ _)

def sparseLaurentTerm (A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ)
    (p : AddMonoidAlgebra A SparseLaurentKey) (w : SparseLaurentKey) : K :=
  (p.coeff w : K) * sparseLaurentMonomial a x y (.ofAdd w)

@[simp] theorem sparseLaurentMonomial_ne_zero (a : ℕ → Kˣ) (x y : Kˣ)
    (w : SparseLaurentKey) : sparseLaurentMonomial a x y (.ofAdd w) ≠ 0 := by
  change ((w.1.prod fun j k => a j ^ k) * x ^ w.2.1 * y ^ w.2.2 : Kˣ).val ≠ 0
  exact Units.ne_zero _

theorem sparseLaurentEval_eq_sum (A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ)
    (p : AddMonoidAlgebra A SparseLaurentKey) :
    sparseLaurentEval A a x y p = ∑ w ∈ p.coeff.support, sparseLaurentTerm A a x y p w := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  simp only [Finsupp.sum, map_sum, sparseLaurentEval, AddMonoidAlgebra.liftNCRingHom_single,
    sparseLaurentTerm, Subring.subtype_apply]

@[simp] theorem sparseLaurentTerm_add (A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ)
    (p q : AddMonoidAlgebra A SparseLaurentKey) (w : SparseLaurentKey) :
    sparseLaurentTerm A a x y (p+q) w =
      sparseLaurentTerm A a x y p w + sparseLaurentTerm A a x y q w := by
  simp [sparseLaurentTerm, add_mul]

@[simp] theorem sparseLaurentTerm_neg (A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ)
    (p : AddMonoidAlgebra A SparseLaurentKey) (w : SparseLaurentKey) :
    sparseLaurentTerm A a x y (-p) w = -sparseLaurentTerm A a x y p w := by
  simp [sparseLaurentTerm]

@[simp] theorem sparseLaurentTerm_zero (A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ)
    (w : SparseLaurentKey) : sparseLaurentTerm A a x y 0 w = 0 := by
  simp [sparseLaurentTerm]

theorem sparseLaurentTerm_mul (A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ)
    (p q : AddMonoidAlgebra A SparseLaurentKey) (w : SparseLaurentKey) :
    sparseLaurentTerm A a x y (p*q) w =
      ∑ u ∈ p.coeff.support, ∑ z ∈ q.coeff.support,
        if u+z=w then sparseLaurentTerm A a x y p u * sparseLaurentTerm A a x y q z else 0 := by
  classical
  simp only [sparseLaurentTerm, AddMonoidAlgebra.coeff_mul, Finsupp.sum,
    AddSubmonoidClass.coe_finsetSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : u+z=w
  · subst w
    simp only [↓reduceIte, Subring.coe_mul]
    rw [show Multiplicative.ofAdd (u+z) = Multiplicative.ofAdd u * Multiplicative.ofAdd z from rfl,
      map_mul]
    ring
  · simp [h]

/-- The common strict order bound is closed under addition and negation. -/
def realOrderAbove {ι : Type*} (v : ι → Valuation K ℝ≥0) (c : ℝ) : AddSubgroup K where
  carrier := {z | z=0 ∨ ∀ i, c < realValuationOrder (v i) z}
  zero_mem' := Or.inl rfl
  neg_mem' := by
    rintro z (rfl | hz)
    · exact Or.inl (neg_zero)
    · exact Or.inr (by simpa only [realValuationOrder_neg] using hz)
  add_mem' := by
    rintro z t (rfl | hz) ht
    · simpa using ht
    rcases ht with rfl | ht
    · simpa using Or.inr hz
    by_cases hzt : z+t=0
    · exact Or.inl hzt
    right
    intro i
    by_cases hz0 : z=0
    · simpa [hz0] using ht i
    by_cases ht0 : t=0
    · simpa [ht0] using hz i
    exact realValuationOrder_lt_add (v i) hz0 ht0 hzt (hz i) (ht i)

@[simp] theorem mem_realOrderAbove {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (c : ℝ) (z : K) : z ∈ realOrderAbove v c ↔ z=0 ∨ ∀ i, c < realValuationOrder (v i) z :=
  Iff.rfl

theorem realOrderAbove_mul {ι : Type*} (v : ι → Valuation K ℝ≥0)
    {c d : ℝ} {z t : K} (hz : z ∈ realOrderAbove v c) (ht : t ∈ realOrderAbove v d) :
    z*t ∈ realOrderAbove v (c+d) := by
  rcases hz with rfl | hz
  · simp
  rcases ht with rfl | ht
  · simp
  by_cases hz0 : z=0
  · simp [hz0]
  by_cases ht0 : t=0
  · simp [ht0]
  right
  intro i
  rw [realValuationOrder_mul (v i) hz0 ht0]
  exact add_lt_add (hz i) (ht i)

theorem realOrderAbove_mul_nonneg {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (R : Subring K) (hR : ∀ z ∈ R, z ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) z)
    {c : ℝ} {z t : K} (hz : z ∈ realOrderAbove v c) (ht : t ∈ R) :
    z*t ∈ realOrderAbove v c := by
  rcases hz with rfl | hz
  · simp
  by_cases hz0 : z=0
  · simp [hz0]
  by_cases ht0 : t=0
  · simp [ht0]
  right
  intro i
  rw [realValuationOrder_mul (v i) hz0 ht0]
  exact lt_of_lt_of_le (hz i) (le_add_of_nonneg_right (hR t ht ht0 i))

/-- Support conditions retained by collecting and multiplying polynomials.
Non-pure terms are above c; non-relevant terms are above 2c. -/
def SparseCollected {ι : Type*} (v : ι → Valuation K ℝ≥0) (R A : Subring K)
    (a : ℕ → Kˣ) (x y : Kˣ) (c : ℝ) (p : AddMonoidAlgebra A SparseLaurentKey) : Prop :=
  ∀ w, sparseLaurentTerm A a x y p w ∈ R ∧
    (¬ w.Pure → sparseLaurentTerm A a x y p w ∈ realOrderAbove v c) ∧
    (¬ w.Relevant → sparseLaurentTerm A a x y p w ∈ realOrderAbove v (2*c))

namespace SparseCollected

variable {ι : Type*} {v : ι → Valuation K ℝ≥0} {R A : Subring K}
  {a : ℕ → Kˣ} {x y : Kˣ} {c : ℝ}
  {p q : AddMonoidAlgebra A SparseLaurentKey}

theorem zero : SparseCollected v R A a x y c 0 := by
  intro w
  simp

theorem add (hp : SparseCollected v R A a x y c p)
    (hq : SparseCollected v R A a x y c q) : SparseCollected v R A a x y c (p+q) := by
  intro w
  rw [sparseLaurentTerm_add]
  exact ⟨R.add_mem (hp w).1 (hq w).1,
    fun h => (realOrderAbove v c).add_mem ((hp w).2.1 h) ((hq w).2.1 h),
    fun h => (realOrderAbove v (2*c)).add_mem ((hp w).2.2 h) ((hq w).2.2 h)⟩

theorem neg (hp : SparseCollected v R A a x y c p) :
    SparseCollected v R A a x y c (-p) := by
  intro w
  rw [sparseLaurentTerm_neg]
  exact ⟨R.neg_mem (hp w).1,
    fun h => (realOrderAbove v c).neg_mem ((hp w).2.1 h),
    fun h => (realOrderAbove v (2*c)).neg_mem ((hp w).2.2 h)⟩

theorem mul (hR : ∀ z ∈ R, z ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) z)
    (hp : SparseCollected v R A a x y c p)
    (hq : SparseCollected v R A a x y c q) : SparseCollected v R A a x y c (p*q) := by
  classical
  intro w
  rw [sparseLaurentTerm_mul]
  refine ⟨R.sum_mem (fun u _ => R.sum_mem (fun z _ => ?_)), ?_, ?_⟩
  · split_ifs
    · exact R.mul_mem (hp u).1 (hq z).1
    · exact R.zero_mem
  · intro hw
    apply (realOrderAbove v c).sum_mem
    intro u _
    apply (realOrderAbove v c).sum_mem
    intro z _
    split_ifs with huz
    · subst w
      by_cases hu : u.Pure
      · have hz : ¬ z.Pure := fun hz => hw (hu.add hz)
        simpa only [mul_comm] using
          realOrderAbove_mul_nonneg v R hR ((hq z).2.1 hz) (hp u).1
      · exact realOrderAbove_mul_nonneg v R hR ((hp u).2.1 hu) (hq z).1
    · exact (realOrderAbove v c).zero_mem
  · intro hw
    apply (realOrderAbove v (2*c)).sum_mem
    intro u _
    apply (realOrderAbove v (2*c)).sum_mem
    intro z _
    split_ifs with huz
    · subst w
      by_cases hu : u.Relevant
      · by_cases hz : z.Relevant
        · have hup : ¬ u.Pure := fun h => hw (h.add_relevant hz)
          have hzp : ¬ z.Pure := fun h => hw (hu.add_pure h)
          simpa only [two_mul] using realOrderAbove_mul v ((hp u).2.1 hup) ((hq z).2.1 hzp)
        · simpa only [mul_comm] using
            realOrderAbove_mul_nonneg v R hR ((hq z).2.2 hz) (hp u).1
      · exact realOrderAbove_mul_nonneg v R hR ((hp u).2.2 hu) (hq z).1
    · exact (realOrderAbove v (2*c)).zero_mem

theorem single {w : SparseLaurentKey} {b : A}
    (hR : (b:K)*sparseLaurentMonomial a x y (.ofAdd w) ∈ R)
    (hc : ¬ w.Pure → (b:K)*sparseLaurentMonomial a x y (.ofAdd w) ∈ realOrderAbove v c)
    (hcc : ¬ w.Relevant → (b:K)*sparseLaurentMonomial a x y (.ofAdd w) ∈ realOrderAbove v (2*c)) :
    SparseCollected v R A a x y c (AddMonoidAlgebra.single w b) := by
  classical
  intro z
  by_cases h : z=w
  · subst z
    simpa [sparseLaurentTerm] using And.intro hR (And.intro hc hcc)
  · simp [sparseLaurentTerm, AddMonoidAlgebra.coeff_single, Ne.symm h]

theorem one : SparseCollected v R A a x y c 1 := by
  change SparseCollected v R A a x y c (AddMonoidAlgebra.single 0 1)
  apply single
  · simp
  · exact fun h => (h SparseLaurentKey.pure_zero).elim
  · exact fun h => (h SparseLaurentKey.pure_zero.relevant).elim

theorem eval_mem (hp : SparseCollected v R A a x y c p) :
    sparseLaurentEval A a x y p ∈ R := by
  rw [sparseLaurentEval_eq_sum]
  exact R.sum_mem fun w _ => (hp w).1

end SparseCollected

/-- The subring of collected polynomials with the two source-tail bounds. -/
def sparseCollectedSubring {ι : Type*} (v : ι → Valuation K ℝ≥0) (R A : Subring K)
    (hR : ∀ z ∈ R, z ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) z)
    (a : ℕ → Kˣ) (x y : Kˣ) (c : ℝ) : Subring (AddMonoidAlgebra A SparseLaurentKey) where
  carrier := SparseCollected v R A a x y c
  zero_mem' := SparseCollected.zero
  one_mem' := SparseCollected.one
  add_mem' := SparseCollected.add
  neg_mem' := SparseCollected.neg
  mul_mem' := SparseCollected.mul hR

/-- Scalar order and Laurent key are determined by a sufficiently low value. -/
def SparseLaurentSeparated {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (a : ℕ → Kˣ) (x y : Kˣ) (d : ℝ) : Prop :=
  ∀ (i : ι) (w z : SparseLaurentKey) (r s : ℕ), w.Relevant → z.Relevant →
    (r:ℝ) + realValuationOrder (v i) (sparseLaurentMonomial a x y (.ofAdd w)) ≤ d →
    (s:ℝ) + realValuationOrder (v i) (sparseLaurentMonomial a x y (.ofAdd z)) ≤ d →
    (r:ℝ) + realValuationOrder (v i) (sparseLaurentMonomial a x y (.ofAdd w)) =
      (s:ℝ) + realValuationOrder (v i) (sparseLaurentMonomial a x y (.ofAdd z)) → r=s ∧ w=z

theorem sparseLaurentTerm_ne_zero (A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ)
    (p : AddMonoidAlgebra A SparseLaurentKey) {w : SparseLaurentKey} (hw : w ∈ p.coeff.support) :
    sparseLaurentTerm A a x y p w ≠ 0 :=
  mul_ne_zero (Subtype.coe_ne_coe.mpr (Finsupp.mem_support_iff.mp hw))
    (sparseLaurentMonomial_ne_zero a x y w)

theorem sparseLaurentTerm_order (A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ)
    (v : Valuation K ℝ≥0) (p : AddMonoidAlgebra A SparseLaurentKey)
    {w : SparseLaurentKey} (hw : w ∈ p.coeff.support) :
    realValuationOrder v (sparseLaurentTerm A a x y p w) =
      realValuationOrder v (p.coeff w : K) +
      realValuationOrder v (sparseLaurentMonomial a x y (.ofAdd w)) :=
  realValuationOrder_mul v (Subtype.coe_ne_coe.mpr (Finsupp.mem_support_iff.mp hw))
    (sparseLaurentMonomial_ne_zero a x y w)

theorem sparseLaurent_leading {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (R A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ) (c : ℝ)
    (hcoeff : ∀ b:A, b≠0 → ∃ r:ℕ, ∀ i, realValuationOrder (v i) (b:K)=r)
    (hsep : SparseLaurentSeparated v a x y (2*c))
    (p : AddMonoidAlgebra A SparseLaurentKey) (hp : SparseCollected v R A a x y c p)
    (i : ι) {w : SparseLaurentKey} (hw : w ∈ p.coeff.support)
    (hlo : realValuationOrder (v i) (sparseLaurentTerm A a x y p w) ≤ 2*c) :
    ∃ z ∈ p.coeff.support,
      realValuationOrder (v i) (sparseLaurentTerm A a x y p z) ≤
        realValuationOrder (v i) (sparseLaurentTerm A a x y p w) ∧
      sparseLaurentEval A a x y p ≠ 0 ∧
      realValuationOrder (v i) (sparseLaurentEval A a x y p) =
        realValuationOrder (v i) (sparseLaurentTerm A a x y p z) := by
  classical
  obtain ⟨z,hz,hzmin⟩ := p.coeff.support.exists_min_image
    (fun z => realValuationOrder (v i) (sparseLaurentTerm A a x y p z)) ⟨w,hw⟩
  have hzlo := (hzmin w hw).trans hlo
  have rel : ∀ u ∈ p.coeff.support,
      realValuationOrder (v i) (sparseLaurentTerm A a x y p u) ≤ 2*c → u.Relevant := by
    intro u hu hle
    by_contra h
    rcases (hp u).2.2 h with hzero | hhigh
    · exact sparseLaurentTerm_ne_zero A a x y p hu hzero
    · exact (not_lt_of_ge hle) (hhigh i)
  have hstrict : ∀ u ∈ p.coeff.support, u≠z →
      realValuationOrder (v i) (sparseLaurentTerm A a x y p z) <
      realValuationOrder (v i) (sparseLaurentTerm A a x y p u) := by
    intro u hu hne
    apply lt_of_le_of_ne (hzmin u hu)
    intro heq
    obtain ⟨r,hr⟩ := hcoeff (p.coeff z) (Finsupp.mem_support_iff.mp hz)
    obtain ⟨s,hs⟩ := hcoeff (p.coeff u) (Finsupp.mem_support_iff.mp hu)
    have hzo := sparseLaurentTerm_order A a x y (v i) p hz
    have huo := sparseLaurentTerm_order A a x y (v i) p hu
    rw [hr i] at hzo
    rw [hs i] at huo
    exact hne (hsep i z u r s (rel z hz hzlo) (rel u hu (heq ▸ hzlo))
      (hzo ▸ hzlo) (huo ▸ heq ▸ hzlo) (hzo.symm.trans (heq.trans huo))).2.symm
  obtain ⟨heval0,heval⟩ := realValuationOrder_sum_eq_of_unique_min (v i)
    p.coeff.support (fun u => sparseLaurentTerm A a x y p u)
    (fun u hu => sparseLaurentTerm_ne_zero A a x y p hu) hz hstrict
  rw [← sparseLaurentEval_eq_sum] at heval0 heval
  exact ⟨z,hz,hzmin w hw,heval0,heval⟩

/-- Every nonzero value at most twice the cutoff has an actual collected,
relevant leading term. The scalar order is shared by all branches. -/
theorem sparseLaurent_low_vector {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (R A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ) (c : ℝ)
    (hcoeff : ∀ b:A, b≠0 → ∃ r:ℕ, ∀ i, realValuationOrder (v i) (b:K)=r)
    (hsep : SparseLaurentSeparated v a x y (2*c))
    (p : AddMonoidAlgebra A SparseLaurentKey) (hp : SparseCollected v R A a x y c p)
    (i : ι) (hp0 : sparseLaurentEval A a x y p ≠ 0)
    (hlo : realValuationOrder (v i) (sparseLaurentEval A a x y p) ≤ 2*c) :
    ∃ w ∈ p.coeff.support, ∃ r:ℕ,
      (∀ j, realValuationOrder (v j) (p.coeff w : K)=r) ∧ w.Relevant ∧
      realValuationOrder (v i) (sparseLaurentEval A a x y p) =
        (r:ℝ) + realValuationOrder (v i) (sparseLaurentMonomial a x y (.ofAdd w)) ∧
      (realValuationOrder (v i) (sparseLaurentEval A a x y p) ≤ c → w.Pure) := by
  classical
  have hex : ∃ w ∈ p.coeff.support,
      realValuationOrder (v i) (sparseLaurentTerm A a x y p w) ≤ 2*c := by
    by_contra h
    push Not at h
    have hh : sparseLaurentEval A a x y p ∈ realOrderAbove (fun _ : Unit => v i) (2*c) := by
      rw [sparseLaurentEval_eq_sum]
      apply (realOrderAbove (fun _ : Unit => v i) (2*c)).sum_mem
      intro w hw
      exact Or.inr (fun _ => h w hw)
    rcases hh with heq | hh
    · exact hp0 heq
    · exact (not_lt_of_ge hlo) (hh ())
  obtain ⟨w,hw,hwl⟩ := hex
  obtain ⟨z,hz,_,_,heq⟩ := sparseLaurent_leading v R A a x y c hcoeff hsep p hp i hw hwl
  obtain ⟨r,hr⟩ := hcoeff (p.coeff z) (Finsupp.mem_support_iff.mp hz)
  have hz0 := sparseLaurentTerm_ne_zero A a x y p hz
  refine ⟨z,hz,r,hr,?_,?_,?_⟩
  · by_contra h
    rcases (hp z).2.2 h with hz' | hh
    · exact hz0 hz'
    · exact (not_lt_of_ge (heq ▸ hlo)) (hh i)
  · rw [heq, sparseLaurentTerm_order A a x y (v i) p hz, hr i]
  · intro hlow
    by_contra h
    rcases (hp z).2.1 h with hz' | hh
    · exact hz0 hz'
    · exact (not_lt_of_ge (heq ▸ hlow)) (hh i)

/-- A high polynomial value cannot conceal a low collected term. -/
theorem sparseLaurent_terms_high {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (R A : Subring K) (a : ℕ → Kˣ) (x y : Kˣ) (c : ℝ) (hc : 0 ≤ c)
    (hcoeff : ∀ b:A, b≠0 → ∃ r:ℕ, ∀ i, realValuationOrder (v i) (b:K)=r)
    (hsep : SparseLaurentSeparated v a x y (2*c))
    (p : AddMonoidAlgebra A SparseLaurentKey) (hp : SparseCollected v R A a x y c p)
    (i : ι) (hhigh : c < realValuationOrder (v i) (sparseLaurentEval A a x y p)) :
    ∀ w ∈ p.coeff.support, c < realValuationOrder (v i) (sparseLaurentTerm A a x y p w) := by
  intro w hw
  by_contra h
  have hwc : realValuationOrder (v i) (sparseLaurentTerm A a x y p w) ≤ c := le_of_not_gt h
  obtain ⟨z,_,hz,_,heq⟩ := sparseLaurent_leading v R A a x y c hcoeff hsep p hp i hw
    (hwc.trans (by linarith))
  exact (not_lt_of_ge (heq ▸ hz.trans hwc)) hhigh

/-- The key and its scalar order give exactly the vector used by selection. -/
def SparseLaurentKey.vector (w : SparseLaurentKey) (r : ℕ) : SparseRelevantVector :=
  ⟨r,w.1,w.2.1,w.2.2⟩

theorem realValuationOrder_zpow (v : Valuation K ℝ≥0) (z : K) (n : ℤ) :
    realValuationOrder v (z^n) = (n:ℝ)*realValuationOrder v z := by
  simp only [realValuationOrder, map_zpow₀, NNReal.coe_zpow, Real.log_zpow]
  ring

theorem sparseLaurentMonomial_order (v : Valuation K ℝ≥0)
    (a : ℕ → Kˣ) (x y : Kˣ) (w : SparseLaurentKey) :
    realValuationOrder v (sparseLaurentMonomial a x y (.ofAdd w)) =
      w.1.sum (fun j k => (k:ℝ)*realValuationOrder v (a j)) +
      (w.2.1:ℝ)*realValuationOrder v x + (w.2.2:ℝ)*realValuationOrder v y := by
  change realValuationOrder v (((w.1.prod fun j k => a j ^ k) * x ^ w.2.1 * y ^ w.2.2 : Kˣ):K) = _
  simp only [Finsupp.prod, Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod,
    Units.val_zpow_eq_zpow_val]
  rw [realValuationOrder_mul v (mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun j _ => zpow_ne_zero _ (a j).ne_zero))
    (pow_ne_zero _ x.ne_zero)) (pow_ne_zero _ y.ne_zero),
    realValuationOrder_mul v
      (Finset.prod_ne_zero_iff.mpr (fun j _ => zpow_ne_zero _ (a j).ne_zero)) (pow_ne_zero _ x.ne_zero),
    realValuationOrder_prod v _ _ (fun j _ => zpow_ne_zero _ (a j).ne_zero)]
  simp only [realValuationOrder_zpow, realValuationOrder_pow, Finsupp.sum]

theorem SparseLaurentKey.vector_eval {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (a : ℕ → Kˣ) (x y : Kˣ) (w : SparseLaurentKey) (r : ℕ) (i : ι) :
    (w.vector r).eval (fun n j => realValuationOrder (v j) (a n))
      (fun j => realValuationOrder (v j) x) (fun j => realValuationOrder (v j) y) i =
      (r:ℝ) + realValuationOrder (v i) (sparseLaurentMonomial a x y (.ofAdd w)) := by
  rw [sparseLaurentMonomial_order]
  simp only [SparseRelevantVector.eval, SparseLaurentKey.vector]
  ring

theorem sparseLaurentSeparated_of_lowInjective {ι : Type*} (v : ι → Valuation K ℝ≥0)
    (a : ℕ → Kˣ) (x y : Kˣ) (d : ℝ)
    (h : SparseRelevantVector.LowInjective (fun n j => realValuationOrder (v j) (a n))
      (fun j => realValuationOrder (v j) x) (fun j => realValuationOrder (v j) y) d) :
    SparseLaurentSeparated v a x y d := by
  intro i w z r s hw hz hwr hzs heq
  have H := h i (w.vector r) (z.vector s) hw hz
    (by simpa only [SparseLaurentKey.vector_eval] using hwr)
    (by simpa only [SparseLaurentKey.vector_eval] using hzs)
    (by simpa only [SparseLaurentKey.vector_eval] using heq)
  refine ⟨congrArg SparseRelevantVector.scalar H, ?_⟩
  have hp := congrArg SparseRelevantVector.powers H
  have he := congrArg SparseRelevantVector.endpoint H
  have hu := congrArg SparseRelevantVector.unit H
  exact Prod.ext hp (Prod.ext he hu)

end HereditaryAtomicity
