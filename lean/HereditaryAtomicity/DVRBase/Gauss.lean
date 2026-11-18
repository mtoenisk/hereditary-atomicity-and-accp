import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Basic.NNReal.Basic
import Mathlib.Tactic
import HereditaryAtomicity.DVRBase.Laurent

/-!
# Weighted Gauss values of finite Laurent polynomials

A multiplicative coefficient valuation and positive multiplicative weights on the
exponent group give the Gauss valuation. The ordered-group formulation permits
lexicographically ordered finite integer vectors and dependent weights.
-/

noncomputable section
open scoped BigOperators NNReal

namespace HereditaryAtomicity.DVRBase

variable {K G : Type*} [Field K] [AddCommGroup G]

/-- The multiplicative weight of an exponent. -/
def exponentWeight (w : Multiplicative G →* ℝ≥0ˣ) (g : G) : ℝ≥0 :=
  w (Multiplicative.ofAdd g)

@[simp] theorem exponentWeight_zero (w : Multiplicative G →* ℝ≥0ˣ) :
    exponentWeight w 0 = 1 := by
  simp [exponentWeight]

@[simp] theorem exponentWeight_add (w : Multiplicative G →* ℝ≥0ˣ) (a b : G) :
    exponentWeight w (a + b) = exponentWeight w a * exponentWeight w b := by
  simp [exponentWeight, ofAdd_add]

theorem exponentWeight_pos (w : Multiplicative G →* ℝ≥0ˣ) (g : G) :
    0 < exponentWeight w g :=
  pos_iff_ne_zero.mpr (Units.ne_zero _)

/-- The weighted value of one collected coefficient; a zero coefficient has value zero. -/
def gaussTerm (v : Valuation K ℝ≥0) (w : Multiplicative G →* ℝ≥0ˣ)
    (f : AddMonoidAlgebra K G) (g : G) : ℝ≥0 :=
  v (f.coeff g) * exponentWeight w g

@[simp] theorem gaussTerm_eq_zero_iff (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G) (g : G) :
    gaussTerm v w f g = 0 ↔ f.coeff g = 0 := by
  simp [gaussTerm, (exponentWeight_pos w g).ne']

theorem gaussTerm_pos (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G) {g : G}
    (hg : f.coeff g ≠ 0) : 0 < gaussTerm v w f g :=
  pos_iff_ne_zero.mpr ((gaussTerm_eq_zero_iff v w f g).not.mpr hg)

/-- The largest weighted coefficient value, with value zero on the zero polynomial. -/
def gaussValue (v : Valuation K ℝ≥0) (w : Multiplicative G →* ℝ≥0ˣ)
    (f : AddMonoidAlgebra K G) : ℝ≥0 :=
  f.coeff.support.sup (gaussTerm v w f)

theorem gaussTerm_le_gaussValue (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G) (g : G) :
    gaussTerm v w f g ≤ gaussValue v w f := by
  classical
  by_cases hg : f.coeff g = 0
  · simp [gaussTerm, hg]
  · exact Finset.le_sup (f := gaussTerm v w f) (Finsupp.mem_support_iff.mpr hg)

theorem gaussValue_le (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G) {a : ℝ≥0}
    (h : ∀ g, gaussTerm v w f g ≤ a) : gaussValue v w f ≤ a := by
  exact Finset.sup_le fun g _ => h g

@[simp] theorem gaussValue_zero (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) : gaussValue v w (0 : AddMonoidAlgebra K G) = 0 := by
  simp [gaussValue]

@[simp] theorem gaussValue_eq_zero_iff (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G) :
    gaussValue v w f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext g
    apply (gaussTerm_eq_zero_iff v w f g).mp
    exact le_antisymm (h ▸ gaussTerm_le_gaussValue v w f g) zero_le
  · rintro rfl
    exact gaussValue_zero v w

theorem gaussValue_pos (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) {f : AddMonoidAlgebra K G} (hf : f ≠ 0) :
    0 < gaussValue v w f := pos_iff_ne_zero.mpr ((gaussValue_eq_zero_iff v w f).not.mpr hf)

@[simp] theorem gaussValue_single (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (g : G) (c : K) :
    gaussValue v w (AddMonoidAlgebra.single g c) = v c * exponentWeight w g := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · simp [gaussValue, gaussTerm, hc]

@[simp] theorem gaussValue_one (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) : gaussValue v w (1 : AddMonoidAlgebra K G) = 1 := by
  change gaussValue v w (AddMonoidAlgebra.single 0 1) = 1
  simp

theorem gaussValue_add_le (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f q : AddMonoidAlgebra K G) :
    gaussValue v w (f + q) ≤ max (gaussValue v w f) (gaussValue v w q) := by
  apply gaussValue_le
  intro g
  have h := mul_le_mul_of_nonneg_right (v.map_add (f.coeff g) (q.coeff g))
    (show (0 : ℝ≥0) ≤ exponentWeight w g from zero_le)
  rw [max_mul] at h
  exact h.trans (max_le_max (gaussTerm_le_gaussValue v w f g)
    (gaussTerm_le_gaussValue v w q g))

theorem weighted_coefficient_mul (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f q : AddMonoidAlgebra K G) (a b : G) :
    v (f.coeff a * q.coeff b) * exponentWeight w (a + b) =
      gaussTerm v w f a * gaussTerm v w q b := by
  simp only [map_mul, exponentWeight_add, gaussTerm]
  ring

private theorem weighted_sum_le (v : Valuation K ℝ≥0) {ι : Type*}
    (s : Finset ι) (f : ι → K) {c a : ℝ≥0} (hc : 0 < c)
    (h : ∀ i ∈ s, v (f i) * c ≤ a) : v (∑ i ∈ s, f i) * c ≤ a := by
  apply (le_div_iff₀ hc).mp
  apply v.map_sum_le
  intro i hi
  exact (le_div_iff₀ hc).mpr (h i hi)

private theorem weighted_sum_lt (v : Valuation K ℝ≥0) {ι : Type*}
    (s : Finset ι) (f : ι → K) {c a : ℝ≥0} (hc : 0 < c) (ha : 0 < a)
    (h : ∀ i ∈ s, v (f i) * c < a) : v (∑ i ∈ s, f i) * c < a := by
  apply (lt_div_iff₀ hc).mp
  apply v.map_sum_lt' (div_pos ha hc)
  intro i hi
  exact (lt_div_iff₀ hc).mpr (h i hi)

theorem gaussTerm_mul_le (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f q : AddMonoidAlgebra K G) (g : G) :
    gaussTerm v w (f * q) g ≤ gaussValue v w f * gaussValue v w q := by
  classical
  unfold gaussTerm
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  apply weighted_sum_le v _ _ (exponentWeight_pos w g)
  intro a _
  have hsum : a + (-a + g) = g := by abel
  have hw := weighted_coefficient_mul v w f q a (-a + g)
  rw [hsum] at hw
  change v (f.coeff a * q.coeff (-a + g)) * exponentWeight w g ≤ _
  rw [hw]
  exact mul_le_mul' (gaussTerm_le_gaussValue v w f a)
    (gaussTerm_le_gaussValue v w q (-a + g))

theorem gaussValue_mul_le (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f q : AddMonoidAlgebra K G) :
    gaussValue v w (f * q) ≤ gaussValue v w f * gaussValue v w q :=
  gaussValue_le v w _ (gaussTerm_mul_le v w f q)

section Ordered

variable [LinearOrder G] [IsOrderedAddMonoid G]

/-- A least exponent among the terms of largest weighted value. -/
structure IsGaussInitial (v : Valuation K ℝ≥0) (w : Multiplicative G →* ℝ≥0ˣ)
    (f : AddMonoidAlgebra K G) (a : G) : Prop where
  coeff_ne_zero : f.coeff a ≠ 0
  term_le : ∀ g, gaussTerm v w f g ≤ gaussTerm v w f a
  term_lt : ∀ g, g < a → gaussTerm v w f g < gaussTerm v w f a

omit [IsOrderedAddMonoid G] in
theorem IsGaussInitial.value_eq {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f : AddMonoidAlgebra K G} {a : G}
    (h : IsGaussInitial v w f a) : gaussValue v w f = gaussTerm v w f a :=
  le_antisymm (gaussValue_le v w f h.term_le) (gaussTerm_le_gaussValue v w f a)

omit [IsOrderedAddMonoid G] in
theorem exists_gaussInitial (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G) (hf : f ≠ 0) :
    ∃ a, IsGaussInitial v w f a := by
  classical
  have hs : f.coeff.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro h
    apply hf
    ext g
    simpa using congrArg (fun q : G →₀ K => q g) h
  obtain ⟨b, hb, hval⟩ := Finset.exists_mem_eq_sup f.coeff.support hs (gaussTerm v w f)
  let s := f.coeff.support.filter fun g => gaussTerm v w f g = gaussValue v w f
  have hbs : b ∈ s := Finset.mem_filter.mpr ⟨hb, hval.symm⟩
  let a := s.min' ⟨b, hbs⟩
  have ha : a ∈ s := Finset.min'_mem _ _
  have hac : f.coeff a ≠ 0 := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp ha).1
  have hav : gaussTerm v w f a = gaussValue v w f := (Finset.mem_filter.mp ha).2
  refine ⟨a, hac, ?_, ?_⟩
  · intro g
    rw [hav]
    exact gaussTerm_le_gaussValue v w f g
  · intro g hga
    apply lt_of_le_of_ne
      (hav.symm ▸ gaussTerm_le_gaussValue v w f g)
    intro heq
    have hgc : f.coeff g ≠ 0 := by
      intro hgc
      have : gaussTerm v w f g = 0 := (gaussTerm_eq_zero_iff v w f g).mpr hgc
      exact (gaussTerm_pos v w f hac).ne' (heq.symm.trans this)
    have hgs : g ∈ s := Finset.mem_filter.mpr
      ⟨Finsupp.mem_support_iff.mpr hgc, heq.trans hav⟩
    exact (not_le_of_gt hga) (Finset.min'_le s g hgs)

private theorem initial_product_pair_lt {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f q : AddMonoidAlgebra K G} {a b i : G}
    (hf : IsGaussInitial v w f a) (hq : IsGaussInitial v w q b) (hi : i ≠ a) :
    gaussTerm v w f i * gaussTerm v w q (-i + (a + b)) <
      gaussTerm v w f a * gaussTerm v w q b := by
  rcases lt_or_gt_of_ne hi with hia | hai
  · calc
      _ ≤ gaussTerm v w f i * gaussTerm v w q b :=
        mul_le_mul_of_nonneg_left (hq.term_le _) zero_le
      _ < _ := mul_lt_mul_of_pos_right (hf.term_lt _ hia)
        (gaussTerm_pos v w q hq.coeff_ne_zero)
  · have hjb : -i + (a + b) < b := by
      have h := add_lt_add_left hai (-i + b)
      convert h using 1 <;> abel
    calc
      _ ≤ gaussTerm v w f a * gaussTerm v w q (-i + (a + b)) :=
        mul_le_mul_of_nonneg_right (hf.term_le _) zero_le
      _ < _ := mul_lt_mul_of_pos_left (hq.term_lt _ hjb)
        (gaussTerm_pos v w f hf.coeff_ne_zero)

theorem IsGaussInitial.product_term_eq {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f q : AddMonoidAlgebra K G} {a b : G}
    (hf : IsGaussInitial v w f a) (hq : IsGaussInitial v w q b) :
    gaussTerm v w (f * q) (a + b) = gaussTerm v w f a * gaussTerm v w q b := by
  classical
  have heq : v ((f * q).coeff (a + b)) = v (f.coeff a * q.coeff b) := by
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    change v (∑ i ∈ f.coeff.support, f.coeff i * q.coeff (-i + (a + b))) = _
    have h := v.map_sum_eq_of_lt
      (f := fun i => f.coeff i * q.coeff (-i + (a + b)))
      (Finsupp.mem_support_iff.mpr hf.coeff_ne_zero) ?_
    · simpa only [neg_add_cancel_left] using h
    intro i hi
    have hia : i ≠ a := by simpa using (Finset.mem_sdiff.mp hi).2
    have hp := initial_product_pair_lt hf hq hia
    have hw := weighted_coefficient_mul v w f q i (-i + (a + b))
    have hs : i + (-i + (a + b)) = a + b := by abel
    rw [hs] at hw
    rw [← hw, ← weighted_coefficient_mul v w f q a b] at hp
    have hlt := (mul_lt_mul_iff_left₀ (exponentWeight_pos w (a + b))).mp hp
    simpa only [neg_add_cancel_left] using hlt
  change v ((f * q).coeff (a + b)) * exponentWeight w (a + b) = _
  rw [heq, weighted_coefficient_mul]

theorem IsGaussInitial.product_coefficient_value {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f q : AddMonoidAlgebra K G} {a b : G}
    (hf : IsGaussInitial v w f a) (hq : IsGaussInitial v w q b) :
    v ((f * q).coeff (a + b)) = v (f.coeff a * q.coeff b) := by
  have h := hf.product_term_eq hq
  rw [← weighted_coefficient_mul v w f q a b] at h
  exact mul_right_cancel₀ (exponentWeight_pos w (a + b)).ne' h

theorem IsGaussInitial.mul {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f q : AddMonoidAlgebra K G} {a b : G}
    (hf : IsGaussInitial v w f a) (hq : IsGaussInitial v w q b) :
    IsGaussInitial v w (f * q) (a + b) := by
  have hpos : 0 < gaussTerm v w f a * gaussTerm v w q b :=
    mul_pos (gaussTerm_pos v w f hf.coeff_ne_zero)
      (gaussTerm_pos v w q hq.coeff_ne_zero)
  refine ⟨?_, ?_, ?_⟩
  · apply (gaussTerm_eq_zero_iff v w (f * q) (a + b)).not.mp
    rw [hf.product_term_eq hq]
    exact hpos.ne'
  · intro g
    rw [hf.product_term_eq hq]
    simpa only [hf.value_eq, hq.value_eq] using gaussTerm_mul_le v w f q g
  · intro g hg
    classical
    rw [hf.product_term_eq hq]
    unfold gaussTerm at ⊢
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    apply weighted_sum_lt v _ _ (exponentWeight_pos w g) hpos
    intro i _
    change v (f.coeff i * q.coeff (-i + g)) * exponentWeight w g < _
    have hw := weighted_coefficient_mul v w f q i (-i + g)
    have hs : i + (-i + g) = g := by abel
    rw [hs] at hw
    rw [hw]
    rcases lt_or_ge i a with hia | hai
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hq.term_le _) zero_le)
        (mul_lt_mul_of_pos_right (hf.term_lt _ hia)
          (gaussTerm_pos v w q hq.coeff_ne_zero))
    · have hjb : -i + g < b := by
        have hgi : g < i + b := hg.trans_le (add_le_add hai le_rfl)
        have h := add_lt_add_left hgi (-i)
        convert h using 1 <;> abel
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hf.term_le _) zero_le)
        (mul_lt_mul_of_pos_left (hq.term_lt _ hjb)
          (gaussTerm_pos v w f hf.coeff_ne_zero))

/-- Multiplicativity of the finite weighted Gauss value, including zero. -/
theorem gaussValue_mul (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f q : AddMonoidAlgebra K G) :
    gaussValue v w (f * q) = gaussValue v w f * gaussValue v w q := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hq : q = 0
  · simp [hq]
  obtain ⟨a, ha⟩ := exists_gaussInitial v w f hf
  obtain ⟨b, hb⟩ := exists_gaussInitial v w q hq
  rw [(ha.mul hb).value_eq, ha.product_term_eq hb, ha.value_eq, hb.value_eq]

/-- A greatest exponent among the terms of largest weighted value. -/
structure IsGaussFinal (v : Valuation K ℝ≥0) (w : Multiplicative G →* ℝ≥0ˣ)
    (f : AddMonoidAlgebra K G) (a : G) : Prop where
  coeff_ne_zero : f.coeff a ≠ 0
  term_le : ∀ g, gaussTerm v w f g ≤ gaussTerm v w f a
  term_lt : ∀ g, a < g → gaussTerm v w f g < gaussTerm v w f a

omit [IsOrderedAddMonoid G] in
theorem exists_gaussFinal (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G) (hf : f ≠ 0) :
    ∃ a, IsGaussFinal v w f a := by
  obtain ⟨a, h⟩ := exists_gaussInitial (G := Gᵒᵈ) v w f hf
  exact ⟨a, h.coeff_ne_zero, h.term_le, h.term_lt⟩

theorem IsGaussFinal.mul {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f q : AddMonoidAlgebra K G} {a b : G}
    (hf : IsGaussFinal v w f a) (hq : IsGaussFinal v w q b) :
    IsGaussFinal v w (f * q) (a + b) := by
  have hf' : IsGaussInitial (G := Gᵒᵈ) v w f a :=
    ⟨hf.coeff_ne_zero, hf.term_le, hf.term_lt⟩
  have hq' : IsGaussInitial (G := Gᵒᵈ) v w q b :=
    ⟨hq.coeff_ne_zero, hq.term_le, hq.term_lt⟩
  have h := hf'.mul hq'
  exact ⟨h.coeff_ne_zero, h.term_le, h.term_lt⟩

omit [IsOrderedAddMonoid G] in
theorem IsGaussInitial.le_final {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f : AddMonoidAlgebra K G} {a b : G}
    (ha : IsGaussInitial v w f a) (hb : IsGaussFinal v w f b) : a ≤ b := by
  by_contra h
  exact (not_lt_of_ge (ha.term_le b)) (hb.term_lt a (lt_of_not_ge h))

/-- A polynomial has one and only one term of maximal weighted value. -/
structure IsUniqueGaussTerm (v : Valuation K ℝ≥0) (w : Multiplicative G →* ℝ≥0ˣ)
    (f : AddMonoidAlgebra K G) (a : G) : Prop where
  coeff_ne_zero : f.coeff a ≠ 0
  term_lt : ∀ g, g ≠ a → gaussTerm v w f g < gaussTerm v w f a

omit [LinearOrder G] [IsOrderedAddMonoid G] in
theorem IsUniqueGaussTerm.value_eq {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f : AddMonoidAlgebra K G} {a : G}
    (h : IsUniqueGaussTerm v w f a) : gaussValue v w f = gaussTerm v w f a := by
  apply le_antisymm _ (gaussTerm_le_gaussValue v w f a)
  apply gaussValue_le
  intro g
  by_cases hg : g = a
  · simp [hg]
  · exact (h.term_lt g hg).le

omit [IsOrderedAddMonoid G] in
theorem IsUniqueGaussTerm.initial {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f : AddMonoidAlgebra K G} {a : G}
    (h : IsUniqueGaussTerm v w f a) : IsGaussInitial v w f a := by
  refine ⟨h.coeff_ne_zero, ?_, fun g hg => h.term_lt g hg.ne⟩
  intro g
  by_cases hg : g = a
  · simp [hg]
  · exact (h.term_lt g hg).le

omit [IsOrderedAddMonoid G] in
theorem IsUniqueGaussTerm.final {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f : AddMonoidAlgebra K G} {a : G}
    (h : IsUniqueGaussTerm v w f a) : IsGaussFinal v w f a := by
  exact ⟨h.coeff_ne_zero, h.initial.term_le, fun g hg => h.term_lt g hg.ne'⟩

omit [IsOrderedAddMonoid G] in
theorem uniqueGaussTerm_of_initial_final {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f : AddMonoidAlgebra K G} {a : G}
    (hi : IsGaussInitial v w f a) (hf : IsGaussFinal v w f a) :
    IsUniqueGaussTerm v w f a := by
  refine ⟨hi.coeff_ne_zero, fun g hg => ?_⟩
  rcases lt_or_gt_of_ne hg with h | h
  · exact hi.term_lt g h
  · exact hf.term_lt g h

omit [IsOrderedAddMonoid G] in
theorem IsGaussInitial.eq_of_unique {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f : AddMonoidAlgebra K G} {a b : G}
    (ha : IsGaussInitial v w f a) (hb : IsUniqueGaussTerm v w f b) : a = b := by
  by_contra h
  exact (not_lt_of_ge (ha.term_le b)) (hb.term_lt a h)

omit [IsOrderedAddMonoid G] in
theorem IsGaussFinal.eq_of_unique {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f : AddMonoidAlgebra K G} {a b : G}
    (ha : IsGaussFinal v w f a) (hb : IsUniqueGaussTerm v w f b) : a = b := by
  by_contra h
  exact (not_lt_of_ge (ha.term_le b)) (hb.term_lt a h)

theorem IsUniqueGaussTerm.mul {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f q : AddMonoidAlgebra K G} {a b : G}
    (hf : IsUniqueGaussTerm v w f a) (hq : IsUniqueGaussTerm v w q b) :
    IsUniqueGaussTerm v w (f * q) (a + b) :=
  uniqueGaussTerm_of_initial_final (hf.initial.mul hq.initial) (hf.final.mul hq.final)

/-- Unique initial terms descend to both factors. No condition on weight ties is needed. -/
theorem IsUniqueGaussTerm.factors {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {f q : AddMonoidAlgebra K G} {c : G}
    (h : IsUniqueGaussTerm v w (f * q) c) :
    ∃ a b, IsUniqueGaussTerm v w f a ∧ IsUniqueGaussTerm v w q b ∧ a + b = c := by
  have hp : f * q ≠ 0 := by
    intro hz
    exact h.coeff_ne_zero (by simp [hz])
  have hf : f ≠ 0 := fun hz => hp (by simp [hz])
  have hq : q ≠ 0 := fun hz => hp (by simp [hz])
  obtain ⟨a, ha⟩ := exists_gaussInitial v w f hf
  obtain ⟨b, hb⟩ := exists_gaussInitial v w q hq
  obtain ⟨a', ha'⟩ := exists_gaussFinal v w f hf
  obtain ⟨b', hb'⟩ := exists_gaussFinal v w q hq
  have hab : a + b = c := (ha.mul hb).eq_of_unique h
  have hab' : a' + b' = c := (ha'.mul hb').eq_of_unique h
  have haa : a = a' := by
    apply le_antisymm (ha.le_final ha')
    by_contra hh
    have hlt : a + b < a' + b' :=
      add_lt_add_of_lt_of_le (lt_of_not_ge hh) (hb.le_final hb')
    exact hlt.ne (hab.trans hab'.symm)
  have hbb : b = b' := by
    apply add_left_cancel (a := a)
    simpa only [← haa] using hab.trans hab'.symm
  refine ⟨a, b, uniqueGaussTerm_of_initial_final ha ?_,
    uniqueGaussTerm_of_initial_final hb ?_, hab⟩
  · simpa only [← haa] using ha'
  · simpa only [← hbb] using hb'

/-- Every subproduct inherits a unique maximal term from the full product. -/
theorem IsUniqueGaussTerm.subproduct {v : Valuation K ℝ≥0}
    {w : Multiplicative G →* ℝ≥0ˣ} {ι : Type*} (f : ι → AddMonoidAlgebra K G)
    {s t : Finset ι} (ht : t ⊆ s) {c : G}
    (h : IsUniqueGaussTerm v w (∏ i ∈ s, f i) c) :
    ∃ a, IsUniqueGaussTerm v w (∏ i ∈ t, f i) a := by
  classical
  rw [← Finset.prod_sdiff ht] at h
  obtain ⟨_, a, _, ha, _⟩ := h.factors
  exact ⟨a, ha⟩

end Ordered

/-- An additive real weight gives a positive multiplicative exponential weight. -/
def exponentialWeight (u : G →+ ℝ) : Multiplicative G →* ℝ≥0ˣ where
  toFun g := Units.mk0 ⟨Real.exp (-u g.toAdd), (Real.exp_pos _).le⟩
    (by intro h; exact (Real.exp_pos (-u g.toAdd)).ne' (congrArg Subtype.val h))
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    change Real.exp (-u 0) = 1
    simp
  map_mul' a b := by
    apply Units.ext
    apply Subtype.ext
    change Real.exp (-u (a.toAdd + b.toAdd)) = Real.exp (-u a.toAdd) * Real.exp (-u b.toAdd)
    simp [Real.exp_add, mul_comm]

@[simp] theorem exponentWeight_exponentialWeight (u : G →+ ℝ) (g : G) :
    (exponentWeight (exponentialWeight u) g : ℝ) = Real.exp (-u g) := rfl

/-- The dot product with the real variable weights, as an additive homomorphism. -/
def laurentWeightOrder {n : ℕ} (u : Fin n → ℝ) : (Fin n → ℤ) →+ ℝ where
  toFun β := ∑ i, (β i : ℝ) * u i
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

/-- The ordinary weighted Gauss value on the project's finite Laurent algebra. -/
def laurentGaussValue {n : ℕ} (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f : Laurent K n) : ℝ≥0 :=
  gaussValue v (exponentialWeight (laurentWeightOrder u)) f

theorem gaussTerm_eq_exp_neg_termOrder {n : ℕ} (v : Valuation K ℝ≥0)
    (u : Fin n → ℝ) (f : Laurent K n) {β : Fin n → ℤ} (hβ : f.coeff β ≠ 0) :
    (gaussTerm v (exponentialWeight (laurentWeightOrder u)) f β : ℝ) =
      Real.exp (-termOrder v u β (f.coeff β)) := by
  have hc : 0 < (v (f.coeff β) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hβ))
  simp only [gaussTerm, NNReal.coe_mul, exponentWeight_exponentialWeight,
    termOrder, realValuationOrder, laurentWeightOrder, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [neg_add, neg_neg, Real.exp_add, Real.exp_log hc]

/-- Literal single least additive-order term, with zero coefficients excluded. -/
def IsInitialTerm {n : ℕ} (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f : Laurent K n) (β : Fin n → ℤ) : Prop :=
  f.coeff β ≠ 0 ∧ ∀ γ, γ ≠ β → f.coeff γ ≠ 0 →
    termOrder v u β (f.coeff β) < termOrder v u γ (f.coeff γ)

theorem isInitialTerm_iff_uniqueGaussTerm {n : ℕ} (v : Valuation K ℝ≥0)
    (u : Fin n → ℝ) (f : Laurent K n) (β : Fin n → ℤ) :
    IsInitialTerm v u f β ↔
      IsUniqueGaussTerm v (exponentialWeight (laurentWeightOrder u)) f β := by
  constructor
  · rintro ⟨hβ, h⟩
    refine ⟨hβ, fun γ hγ => ?_⟩
    by_cases hc : f.coeff γ = 0
    · rw [(gaussTerm_eq_zero_iff _ _ _ _).mpr hc]
      exact gaussTerm_pos _ _ f hβ
    · apply NNReal.coe_lt_coe.mp
      rw [gaussTerm_eq_exp_neg_termOrder v u f hc,
        gaussTerm_eq_exp_neg_termOrder v u f hβ]
      exact Real.exp_lt_exp.mpr (neg_lt_neg (h γ hγ hc))
  · intro h
    refine ⟨h.coeff_ne_zero, fun γ hγ hc => ?_⟩
    have hh := NNReal.coe_lt_coe.mpr (h.term_lt γ hγ)
    rw [gaussTerm_eq_exp_neg_termOrder v u f hc,
      gaussTerm_eq_exp_neg_termOrder v u f h.coeff_ne_zero] at hh
    exact neg_lt_neg_iff.mp (Real.exp_lt_exp.mp hh)

/-- Weighted Gauss multiplicativity for arbitrary real weights on finite Laurent exponents. -/
theorem laurentGaussValue_mul {n : ℕ} (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f q : Laurent K n) :
    laurentGaussValue v u (f * q) = laurentGaussValue v u f * laurentGaussValue v u q := by
  exact gaussValue_mul (G := Lex (Fin n → ℤ)) _ _ _ _

/-- The literal weighted Gauss valuation on the finite Laurent polynomial ring. -/
def laurentGaussValuation {n : ℕ} (v : Valuation K ℝ≥0) (u : Fin n → ℝ) :
    Valuation (Laurent K n) ℝ≥0 where
  toFun := laurentGaussValue v u
  map_zero' := gaussValue_zero _ _
  map_one' := gaussValue_one _ _
  map_mul' := laurentGaussValue_mul v u
  map_add_le_max' := gaussValue_add_le _ _

theorem IsInitialTerm.mul {n : ℕ} {v : Valuation K ℝ≥0} {u : Fin n → ℝ}
    {f q : Laurent K n} {β γ : Fin n → ℤ}
    (hf : IsInitialTerm v u f β) (hq : IsInitialTerm v u q γ) :
    IsInitialTerm v u (f * q) (β + γ) := by
  apply (isInitialTerm_iff_uniqueGaussTerm v u _ _).mpr
  exact IsUniqueGaussTerm.mul (G := Lex (Fin n → ℤ))
    ((isInitialTerm_iff_uniqueGaussTerm v u _ _).mp hf)
    ((isInitialTerm_iff_uniqueGaussTerm v u _ _).mp hq)

/-- The single least-order term of a product forces one in each factor. -/
theorem IsInitialTerm.factors {n : ℕ} {v : Valuation K ℝ≥0} {u : Fin n → ℝ}
    {f q : Laurent K n} {δ : Fin n → ℤ} (h : IsInitialTerm v u (f * q) δ) :
    ∃ β γ, IsInitialTerm v u f β ∧ IsInitialTerm v u q γ ∧ β + γ = δ := by
  obtain ⟨β, γ, hf, hq, heq⟩ :=
    @IsUniqueGaussTerm.factors K (Lex (Fin n → ℤ)) _ _
      (inferInstanceAs (LinearOrder (Lex (Fin n → ℤ))))
      (inferInstanceAs (IsOrderedAddMonoid (Lex (Fin n → ℤ))))
      v (exponentialWeight (laurentWeightOrder u)) f q δ
      ((isInitialTerm_iff_uniqueGaussTerm v u _ _).mp h)
  exact ⟨β, γ, (isInitialTerm_iff_uniqueGaussTerm v u _ _).mpr hf,
    (isInitialTerm_iff_uniqueGaussTerm v u _ _).mpr hq, heq⟩

theorem IsInitialTerm.subproduct {n : ℕ} {v : Valuation K ℝ≥0} {u : Fin n → ℝ}
    {ι : Type*} (f : ι → Laurent K n) {s t : Finset ι} (ht : t ⊆ s)
    {δ : Fin n → ℤ} (h : IsInitialTerm v u (∏ i ∈ s, f i) δ) :
    ∃ β, IsInitialTerm v u (∏ i ∈ t, f i) β := by
  obtain ⟨β, hβ⟩ :=
    @IsUniqueGaussTerm.subproduct K (Lex (Fin n → ℤ)) _ _
      (inferInstanceAs (LinearOrder (Lex (Fin n → ℤ))))
      (inferInstanceAs (IsOrderedAddMonoid (Lex (Fin n → ℤ))))
      v (exponentialWeight (laurentWeightOrder u)) ι f s t ht δ
      ((isInitialTerm_iff_uniqueGaussTerm v u _ _).mp h)
  exact ⟨β, (isInitialTerm_iff_uniqueGaussTerm v u _ _).mpr hβ⟩

/-- The valuation of the initial coefficient adds, even when other coefficients cancel. -/
theorem IsInitialTerm.coefficientOrder_mul {n : ℕ} {v : Valuation K ℝ≥0}
    {u : Fin n → ℝ} {f q : Laurent K n} {β γ : Fin n → ℤ}
    (hf : IsInitialTerm v u f β) (hq : IsInitialTerm v u q γ) :
    realValuationOrder v ((f * q).coeff (β + γ)) =
      realValuationOrder v (f.coeff β) + realValuationOrder v (q.coeff γ) := by
  have hf' := IsUniqueGaussTerm.initial (G := Lex (Fin n → ℤ))
    ((isInitialTerm_iff_uniqueGaussTerm v u _ _).mp hf)
  have hq' := IsUniqueGaussTerm.initial (G := Lex (Fin n → ℤ))
    ((isInitialTerm_iff_uniqueGaussTerm v u _ _).mp hq)
  have h := congrArg (fun x : ℝ≥0 => -Real.log (x : ℝ)) (hf'.product_coefficient_value hq')
  change realValuationOrder v ((f * q).coeff (β + γ)) =
    realValuationOrder v (f.coeff β * q.coeff γ) at h
  rw [realValuationOrder_mul v hf.1 hq.1] at h
  exact h

theorem IsInitialTerm.order_mul {n : ℕ} {v : Valuation K ℝ≥0}
    {u : Fin n → ℝ} {f q : Laurent K n} {β γ : Fin n → ℤ}
    (hf : IsInitialTerm v u f β) (hq : IsInitialTerm v u q γ) :
    termOrder v u (β + γ) ((f * q).coeff (β + γ)) =
      termOrder v u β (f.coeff β) + termOrder v u γ (q.coeff γ) := by
  simp only [termOrder, hf.coefficientOrder_mul hq, Pi.add_apply,
    Int.cast_add, add_mul, Finset.sum_add_distrib]
  ring

theorem isInitialTerm_one {n : ℕ} (v : Valuation K ℝ≥0) (u : Fin n → ℝ) :
    IsInitialTerm v u (1 : Laurent K n) 0 := by
  classical
  refine ⟨by simp, fun γ hγ hc => ?_⟩
  exfalso
  apply hc
  change (AddMonoidAlgebra.single (0 : Fin n → ℤ) (1 : K)).coeff γ = 0
  simp [AddMonoidAlgebra.coeff_single, hγ]

theorem isInitialTerm_single {n : ℕ} (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (β : Fin n → ℤ) {c : K} (hc : c ≠ 0) :
    IsInitialTerm v u (AddMonoidAlgebra.single β c) β := by
  classical
  refine ⟨by simpa, fun γ hγ hcoeff => ?_⟩
  exact (hcoeff (by simp [hγ])).elim

theorem IsInitialTerm.finset_prod {n : ℕ} {v : Valuation K ℝ≥0}
    {u : Fin n → ℝ} {ι : Type*} (s : Finset ι) (f : ι → Laurent K n)
    (β : ι → Fin n → ℤ) (h : ∀ i ∈ s, IsInitialTerm v u (f i) (β i)) :
    IsInitialTerm v u (∏ i ∈ s, f i) (∑ i ∈ s, β i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isInitialTerm_one v u
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Finite additive Gauss order. Its zero-polynomial value is conventional;
all multiplicative order statements explicitly exclude zero. -/
def laurentOrder {n : ℕ} (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f : Laurent K n) : ℝ := -Real.log (laurentGaussValue v u f : ℝ)

theorem laurentOrder_mul {n : ℕ} (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    {f q : Laurent K n} (hf : f ≠ 0) (hq : q ≠ 0) :
    laurentOrder v u (f * q) = laurentOrder v u f + laurentOrder v u q := by
  have hfn : (laurentGaussValue v u f : ℝ) ≠ 0 := by
    exact_mod_cast (gaussValue_pos v (exponentialWeight (laurentWeightOrder u)) hf).ne'
  have hqn : (laurentGaussValue v u q : ℝ) ≠ 0 := by
    exact_mod_cast (gaussValue_pos v (exponentialWeight (laurentWeightOrder u)) hq).ne'
  simp only [laurentOrder, laurentGaussValue_mul, NNReal.coe_mul,
    Real.log_mul hfn hqn, neg_add]

theorem laurentOrder_le_termOrder {n : ℕ} (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f : Laurent K n) {β : Fin n → ℤ} (hβ : f.coeff β ≠ 0) :
    laurentOrder v u f ≤ termOrder v u β (f.coeff β) := by
  have hp : (0 : ℝ) < gaussTerm v (exponentialWeight (laurentWeightOrder u)) f β := by
    exact_mod_cast gaussTerm_pos v (exponentialWeight (laurentWeightOrder u)) f hβ
  have hle : (gaussTerm v (exponentialWeight (laurentWeightOrder u)) f β : ℝ) ≤
      laurentGaussValue v u f := by
    exact_mod_cast gaussTerm_le_gaussValue v (exponentialWeight (laurentWeightOrder u)) f β
  have h := Real.log_le_log hp hle
  rw [gaussTerm_eq_exp_neg_termOrder v u f hβ, Real.log_exp] at h
  exact neg_le_of_neg_le h

theorem IsInitialTerm.order_eq {n : ℕ} {v : Valuation K ℝ≥0} {u : Fin n → ℝ}
    {f : Laurent K n} {β : Fin n → ℤ} (h : IsInitialTerm v u f β) :
    laurentOrder v u f = termOrder v u β (f.coeff β) := by
  have hv := ((isInitialTerm_iff_uniqueGaussTerm v u _ _).mp h).value_eq
  unfold laurentOrder laurentGaussValue
  rw [hv, gaussTerm_eq_exp_neg_termOrder v u f h.1, Real.log_exp, neg_neg]

end HereditaryAtomicity.DVRBase
