import HereditaryAtomicity.DVRBase.Gauss
import HereditaryAtomicity.DVRBase.CoefficientMatching

/-!
# Exact Gauss support bounds and selection of collected terms

The zero polynomial is included in all support/value equivalences. Additive
order assertions about a selected coefficient explicitly exclude zero.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal

variable {K G : Type*} [Field K] [AddCommGroup G]

/-- A weak bound on the Gauss value is precisely a bound on every actual term. -/
theorem gaussValue_le_iff (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G) (a : ℝ≥0) :
    gaussValue v w f ≤ a ↔
      ∀ g, f.coeff g ≠ 0 → gaussTerm v w f g ≤ a := by
  constructor
  · exact fun h g _ => (gaussTerm_le_gaussValue v w f g).trans h
  · intro h
    apply gaussValue_le
    intro g
    by_cases hg : f.coeff g = 0
    · rw [(gaussTerm_eq_zero_iff v w f g).mpr hg]
      exact zero_le
    · exact h g hg

/-- Strict finite support bounds include the empty support when the cutoff is positive. -/
theorem gaussValue_lt_iff (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G)
    {a : ℝ≥0} (ha : 0 < a) :
    gaussValue v w f < a ↔
      ∀ g, f.coeff g ≠ 0 → gaussTerm v w f g < a := by
  classical
  unfold gaussValue
  rw [Finset.sup_lt_iff ha]
  simp only [Finsupp.mem_support_iff]

/-- A nonzero polynomial has an actual coefficient attaining its Gauss value;
no ordering of exponent vectors or tie-breaking choice is needed. -/
theorem exists_gaussTerm_eq_gaussValue (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (f : AddMonoidAlgebra K G) (hf : f ≠ 0) :
    ∃ g, f.coeff g ≠ 0 ∧ gaussTerm v w f g = gaussValue v w f := by
  classical
  have hs : f.coeff.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    exact AddMonoidAlgebra.coeff_eq_zero.not.mpr hf
  obtain ⟨g, hg, heq⟩ := Finset.exists_mem_eq_sup f.coeff.support hs (gaussTerm v w f)
  exact ⟨g, Finsupp.mem_support_iff.mp hg, heq.symm⟩

/-- Keep exactly the collected coefficients satisfying a prescribed term predicate. -/
def selectTerms (P : G → K → Prop) (f : AddMonoidAlgebra K G) : AddMonoidAlgebra K G := by
  classical
  exact AddMonoidAlgebra.ofCoeff (f.coeff.filter fun g => P g (f.coeff g))

omit [AddCommGroup G] in
open Classical in
@[simp] theorem coeff_selectTerms (P : G → K → Prop) (f : AddMonoidAlgebra K G) (g : G) :
    (selectTerms P f).coeff g = if P g (f.coeff g) then f.coeff g else 0 := rfl

omit [AddCommGroup G] in
@[simp] theorem coeff_selectTerms_ne_zero (P : G → K → Prop)
    (f : AddMonoidAlgebra K G) (g : G) :
    (selectTerms P f).coeff g ≠ 0 ↔ P g (f.coeff g) ∧ f.coeff g ≠ 0 := by
  classical
  by_cases hp : P g (f.coeff g) <;> simp [hp]

omit [AddCommGroup G] in
open Classical in
/-- The selected polynomial has exactly the filtered actual support. -/
theorem support_selectTerms (P : G → K → Prop) (f : AddMonoidAlgebra K G) :
    (selectTerms P f).coeff.support =
      {g ∈ f.coeff.support | P g (f.coeff g)} := by
  classical
  rfl

@[simp] theorem selectTerms_zero (P : G → K → Prop) :
    selectTerms P (0 : AddMonoidAlgebra K G) = 0 := by
  classical
  ext g
  by_cases hp : P g 0 <;> simp [hp]

/-- Selection and its complementary selection recover the original polynomial exactly. -/
theorem selectTerms_add_compl (P : G → K → Prop) (f : AddMonoidAlgebra K G) :
    selectTerms P f + selectTerms (fun g c => ¬ P g c) f = f := by
  classical
  ext g
  by_cases hp : P g (f.coeff g) <;> simp [hp]

theorem sub_selectTerms (P : G → K → Prop) (f : AddMonoidAlgebra K G) :
    f - selectTerms P f = selectTerms (fun g c => ¬ P g c) f := by
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using (selectTerms_add_compl P f).symm)

/-- Dropping collected terms cannot increase the Gauss value. -/
theorem gaussValue_selectTerms_le (v : Valuation K ℝ≥0)
    (w : Multiplicative G →* ℝ≥0ˣ) (P : G → K → Prop) (f : AddMonoidAlgebra K G) :
    gaussValue v w (selectTerms P f) ≤ gaussValue v w f := by
  classical
  apply (gaussValue_le_iff v w _ _).mpr
  intro g hg
  obtain ⟨hp, _⟩ := (coeff_selectTerms_ne_zero P f g).mp hg
  simpa only [gaussTerm, coeff_selectTerms, ite_eq_left hp] using
    gaussTerm_le_gaussValue v w f g

section Laurent

variable {n : ℕ}

/-- Nonstrict order support class. -/
def orderAtLeast (u : Fin n → ℝ) (ν : ℝ) : MonomialClass n where
  contains β e := ν ≤ e + ∑ i, (β i : ℝ) * u i
  upward := by
    intro β a b hab ha
    linarith

/-- Every nonzero collected coefficient has order at least ν exactly when
its finite Gauss value is at most exp(-ν), including the zero polynomial. -/
theorem laurentGaussValue_le_exp_iff (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f : Laurent K n) (ν : ℝ) :
    (laurentGaussValue v u f : ℝ) ≤ Real.exp (-ν) ↔
      ∀ β, f.coeff β ≠ 0 → ν ≤ termOrder v u β (f.coeff β) := by
  let a : ℝ≥0 := ⟨Real.exp (-ν), (Real.exp_pos _).le⟩
  change laurentGaussValue v u f ≤ a ↔ _
  rw [laurentGaussValue, gaussValue_le_iff]
  apply forall_congr'
  intro β
  apply imp_congr_right
  intro hβ
  change (gaussTerm v (exponentialWeight (laurentWeightOrder u)) f β : ℝ) ≤
    Real.exp (-ν) ↔ _
  rw [gaussTerm_eq_exp_neg_termOrder v u f hβ, Real.exp_le_exp, neg_le_neg_iff]

/-- Strict coefficient order bounds are exact strict Gauss value bounds;
positive exponential cutoffs automatically handle zero and empty support. -/
theorem laurentGaussValue_lt_exp_iff (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f : Laurent K n) (ν : ℝ) :
    (laurentGaussValue v u f : ℝ) < Real.exp (-ν) ↔
      ∀ β, f.coeff β ≠ 0 → ν < termOrder v u β (f.coeff β) := by
  let a : ℝ≥0 := ⟨Real.exp (-ν), (Real.exp_pos _).le⟩
  have ha : 0 < a := Real.exp_pos (-ν)
  change laurentGaussValue v u f < a ↔ _
  rw [laurentGaussValue, gaussValue_lt_iff v _ f ha]
  apply forall_congr'
  intro β
  apply imp_congr_right
  intro hβ
  change (gaussTerm v (exponentialWeight (laurentWeightOrder u)) f β : ℝ) <
    Real.exp (-ν) ↔ _
  rw [gaussTerm_eq_exp_neg_termOrder v u f hβ, Real.exp_lt_exp, neg_lt_neg_iff]

theorem mem_higherOrder_supported_iff (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f : Laurent K n) (ν : ℝ) :
    f ∈ (higherOrder u ν).supported v ↔
      (laurentGaussValue v u f : ℝ) < Real.exp (-ν) := by
  rw [laurentGaussValue_lt_exp_iff, MonomialClass.mem_supported]
  rfl

theorem mem_orderAtLeast_supported_iff (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f : Laurent K n) (ν : ℝ) :
    f ∈ (orderAtLeast u ν).supported v ↔
      (laurentGaussValue v u f : ℝ) ≤ Real.exp (-ν) := by
  rw [laurentGaussValue_le_exp_iff, MonomialClass.mem_supported]
  rfl

/-- An actual coefficient attains the finite Laurent order of a nonzero polynomial. -/
theorem exists_termOrder_eq_laurentOrder (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (f : Laurent K n) (hf : f ≠ 0) :
    ∃ β, f.coeff β ≠ 0 ∧ termOrder v u β (f.coeff β) = laurentOrder v u f := by
  obtain ⟨β, hβ, heq⟩ := exists_gaussTerm_eq_gaussValue v
    (exponentialWeight (laurentWeightOrder u)) f hf
  refine ⟨β, hβ, ?_⟩
  unfold laurentOrder laurentGaussValue
  rw [← heq, gaussTerm_eq_exp_neg_termOrder v u f hβ, Real.log_exp, neg_neg]

/-- Any coefficient predicate preserves every monomial support class. -/
theorem selectTerms_mem_supported (v : Valuation K ℝ≥0) (M : MonomialClass n)
    (P : (Fin n → ℤ) → K → Prop) {f : Laurent K n}
    (hf : f ∈ M.supported v) : selectTerms P f ∈ M.supported v := by
  classical
  apply (MonomialClass.mem_supported v M).mpr
  intro β hβ
  obtain ⟨hp, hc⟩ := (coeff_selectTerms_ne_zero P f β).mp hβ
  simpa only [coeff_selectTerms, ite_eq_left hp] using
    (MonomialClass.mem_supported v M).mp hf β hc

/-- The selected polynomial satisfies the selecting predicate at each nonzero coefficient. -/
theorem selectTerms_satisfies (P : (Fin n → ℤ) → K → Prop) (f : Laurent K n)
    (β : Fin n → ℤ) (hβ : (selectTerms P f).coeff β ≠ 0) :
    P β ((selectTerms P f).coeff β) := by
  classical
  obtain ⟨hp, _⟩ := (coeff_selectTerms_ne_zero P f β).mp hβ
  simpa only [coeff_selectTerms, ite_eq_left hp] using hp

theorem laurentGaussValue_selectTerms_le (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (P : (Fin n → ℤ) → K → Prop) (f : Laurent K n) :
    laurentGaussValue v u (selectTerms P f) ≤ laurentGaussValue v u f :=
  gaussValue_selectTerms_le v _ P f

/-- Whenever the retained part is nonzero, discarding terms can only raise order. -/
theorem laurentOrder_le_selectTerms (v : Valuation K ℝ≥0) (u : Fin n → ℝ)
    (P : (Fin n → ℤ) → K → Prop) (f : Laurent K n)
    (hsel : selectTerms P f ≠ 0) :
    laurentOrder v u f ≤ laurentOrder v u (selectTerms P f) := by
  obtain ⟨β, hβ, heq⟩ := exists_termOrder_eq_laurentOrder v u (selectTerms P f) hsel
  obtain ⟨hp, hc⟩ := (coeff_selectTerms_ne_zero P f β).mp hβ
  rw [← heq, coeff_selectTerms, ite_eq_left hp]
  exact laurentOrder_le_termOrder v u f hc

end Laurent
end HereditaryAtomicity.DVRBase
