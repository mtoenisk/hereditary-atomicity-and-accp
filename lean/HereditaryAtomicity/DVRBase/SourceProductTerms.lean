import HereditaryAtomicity.DVRBase.SourceLaurent
import Mathlib.Algebra.BigOperators.Ring.List

/-! # Actual finite products of source Laurent generators -/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}
theorem list_prod_laurent_single {ι k : Type*} [CommSemiring k]
    (l : List ι) (β : ι → Fin n → ℤ) (c : ι → k) :
    (l.map (fun i => (AddMonoidAlgebra.single (β i) (c i) : Laurent k n))).prod =
      AddMonoidAlgebra.single ((l.map β).sum) ((l.map c).prod) := by
  induction l with
  | nil => simp [← AddMonoidAlgebra.one_def]
  | cons i l ih => simp [ih, AddMonoidAlgebra.single_mul_single]

theorem list_sum_function_apply {ι A : Type*} [AddCommMonoid A]
    (l : List ι) (f : ι → Fin n → A) (i : Fin n) :
    (l.map f).sum i = (l.map (fun a => f a i)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem realValuationOrder_list_prod {ι k : Type*} [Field k]
    (v : Valuation k ℝ≥0) (l : List ι) (f : ι → k) (hf : ∀ a ∈ l, f a ≠ 0) :
    realValuationOrder v (l.map f).prod = (l.map (fun a => realValuationOrder v (f a))).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have htail : ∀ b ∈ l, f b ≠ 0 := fun b hb => hf b (List.mem_cons_of_mem _ hb)
      have hp : (l.map f).prod ≠ 0 := by
        apply List.prod_ne_zero
        rintro hz
        obtain ⟨b, hb, he⟩ := List.mem_map.mp hz
        exact htail b hb he
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [realValuationOrder_mul v (hf a List.mem_cons_self) hp, ih htail]

namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

/-- One literal product term in E_n, before collecting Laurent coefficients.
The endpoint count at i refers to Z_(i+1), matching the tail counts in Lemma X. -/
structure FormalProduct (O : Subring K) (n : ℕ) where
  coefficient : O
  variablePowers : Fin n → ℕ
  endpointPowers : Fin n → ℕ
  deadFactors : List {h : D.FirstDead // h.length ≤ n}

namespace FormalProduct
variable {D} {O : Subring K}

/-- The actual product expression retaining all source-generator counts. -/
def formal (π : O) (p : D.FormalProduct O n) : Laurent (FractionRing O) n :=
  AddMonoidAlgebra.single 0 (algebraMap O (FractionRing O) p.coefficient) *
    (∏ i, variableMonomial i ^ p.variablePowers i) *
    (∏ i, endpointMonomial (algebraMap O (FractionRing O) π) D.exponent (i.val + 1) ^
      p.endpointPowers i) *
    (p.deadFactors.map (fun h => h.val.formal O π h.property)).prod

/-- Combining products adds the literal variable/endpoint counts and appends
first-dead factors, without collecting away their provenance. -/
def mul (p q : D.FormalProduct O n) : D.FormalProduct O n where
  coefficient := p.coefficient * q.coefficient
  variablePowers := p.variablePowers + q.variablePowers
  endpointPowers := p.endpointPowers + q.endpointPowers
  deadFactors := p.deadFactors ++ q.deadFactors

def neg (p : D.FormalProduct O n) : D.FormalProduct O n where
  coefficient := -p.coefficient
  variablePowers := p.variablePowers
  endpointPowers := p.endpointPowers
  deadFactors := p.deadFactors

@[simp] theorem formal_mul (π : O) (p q : D.FormalProduct O n) :
    (p.mul q).formal π = p.formal π * q.formal π := by
  simp only [formal, mul, map_mul, Pi.add_apply, pow_add,
    Finset.prod_mul_distrib, List.map_append, List.prod_append]
  have he : (AddMonoidAlgebra.single 0 (algebraMap O (FractionRing O) p.coefficient) :
      Laurent (FractionRing O) n) *
      AddMonoidAlgebra.single 0 (algebraMap O (FractionRing O) q.coefficient) =
      AddMonoidAlgebra.single 0 (algebraMap O (FractionRing O) p.coefficient *
        algebraMap O (FractionRing O) q.coefficient) := by
    rw [AddMonoidAlgebra.single_mul_single, zero_add]
  rw [← he]
  ring

@[simp] theorem formal_neg (π : O) (p : D.FormalProduct O n) :
    p.neg.formal π = -p.formal π := by
  simp [formal, neg]
  ring

theorem formal_mem (π : O) (p : D.FormalProduct O n) :
    p.formal π ∈ D.formalRing O π n := by
  apply Subring.mul_mem
  · apply Subring.mul_mem
    · apply Subring.mul_mem
      · exact Subring.subset_closure (FormalGenerator.coefficient p.coefficient)
      · apply Subring.prod_mem
        intro i _
        exact Subring.pow_mem _ (Subring.subset_closure (FormalGenerator.coordinate i)) _
    · apply Subring.prod_mem
      intro i _
      exact Subring.pow_mem _
        (Subring.subset_closure (FormalGenerator.endpoint (i.val + 1) i.isLt)) _
  · apply Subring.list_prod_mem
    intro x hx
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hx
    exact Subring.subset_closure (FormalGenerator.firstDead h.val h.property)

/-- The exact exponent of the product, before any cancellation with other terms. -/
def formalExponent (p : D.FormalProduct O n) : Fin n → ℤ :=
  (∑ i, p.variablePowers i • Pi.single i 1) +
    (∑ i : Fin n, p.endpointPowers i • (fun j : Fin n => if j.val < i.val + 1 then -1 else 0)) +
    (p.deadFactors.map (fun h => h.val.formalExponent h.property)).sum

/-- The exact original coefficient of the product monomial. -/
def formalCoefficient (π : O) (p : D.FormalProduct O n) : FractionRing O :=
  algebraMap O (FractionRing O) p.coefficient *
    (∏ i, ((algebraMap O (FractionRing O) π) ^ D.exponent) ^ p.endpointPowers i) *
    (p.deadFactors.map (fun h => (algebraMap O (FractionRing O) π) ^ h.val.coefficientExponent /
      (algebraMap O (FractionRing O) π) ^ D.exponent)).prod

theorem formalCoefficient_ne_zero (π : O) (p : D.FormalProduct O n)
    (hπ : π ≠ 0) (hc : p.coefficient ≠ 0) : p.formalCoefficient π ≠ 0 := by
  have hi := IsFractionRing.injective O (FractionRing O)
  have hp : algebraMap O (FractionRing O) π ≠ 0 := (map_ne_zero_iff _ hi).mpr hπ
  apply mul_ne_zero
  · apply mul_ne_zero ((map_ne_zero_iff _ hi).mpr hc)
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (pow_ne_zero _ hp))
  · apply List.prod_ne_zero
    rintro hz
    obtain ⟨h, _, he⟩ := List.mem_map.mp hz
    exact div_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hp) he

/-- The exact coefficient order remembers the nonnegative original O
coefficient and all integer coefficient exponents of first-dead factors. -/
theorem formalCoefficient_order (π : O) (p : D.FormalProduct O n)
    (v : Valuation (FractionRing O) ℝ≥0) (hπ : π ≠ 0)
    (hvπ : realValuationOrder v (algebraMap O (FractionRing O) π) = 1)
    (hc : p.coefficient ≠ 0) :
    realValuationOrder v (p.formalCoefficient π) =
      realValuationOrder v (algebraMap O (FractionRing O) p.coefficient) +
      (D.exponent : ℝ) * ∑ i, (p.endpointPowers i : ℝ) +
      (p.deadFactors.map (fun h => (h.val.coefficientExponent : ℝ) - D.exponent)).sum := by
  have hi := IsFractionRing.injective O (FractionRing O)
  have hp : algebraMap O (FractionRing O) π ≠ 0 := (map_ne_zero_iff _ hi).mpr hπ
  have hb : (∏ i : Fin n, ((algebraMap O (FractionRing O) π) ^ D.exponent) ^ p.endpointPowers i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (pow_ne_zero _ hp))
  have hq : ∀ h : {h : D.FirstDead // h.length ≤ n},
      (algebraMap O (FractionRing O) π) ^ h.val.coefficientExponent /
        (algebraMap O (FractionRing O) π) ^ D.exponent ≠ 0 :=
    fun h => div_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hp)
  have hqs : (p.deadFactors.map (fun h =>
      (algebraMap O (FractionRing O) π) ^ h.val.coefficientExponent /
      (algebraMap O (FractionRing O) π) ^ D.exponent)).prod ≠ 0 := by
    apply List.prod_ne_zero
    rintro hz
    obtain ⟨h, _, he⟩ := List.mem_map.mp hz
    exact hq h he
  rw [formalCoefficient, realValuationOrder_mul v
    (mul_ne_zero ((map_ne_zero_iff _ hi).mpr hc) hb) hqs,
    realValuationOrder_mul v ((map_ne_zero_iff _ hi).mpr hc) hb,
    realValuationOrder_prod v _ _ (fun i _ => pow_ne_zero _ (pow_ne_zero _ hp)),
    realValuationOrder_list_prod v _ _ (fun h _ => hq h)]
  simp only [realValuationOrder_pow, hvπ, mul_one,
    realValuationOrder_div v (pow_ne_zero _ hp) (pow_ne_zero _ hp)]
  rw [← Finset.sum_mul]
  ring

/-- A literal product-count term is exactly its computed Laurent monomial. -/
theorem formal_eq_single (π : O) (p : D.FormalProduct O n) :
    p.formal π = AddMonoidAlgebra.single p.formalExponent (p.formalCoefficient π) := by
  simp only [formal, variableMonomial, endpointMonomial,
    AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.prod_single,
    Finset.prod_const_one, FirstDead.formal_eq_single]
  rw [list_prod_laurent_single]
  simp only [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  rfl

/-- The variable contribution at a coordinate is its original natural count. -/
theorem variable_exponent_apply (p : D.FormalProduct O n) (i : Fin n) :
    (∑ j : Fin n, p.variablePowers j • (Pi.single j 1 : Fin n → ℤ)) i = p.variablePowers i := by
  classical
  simp [Finset.sum_apply, Pi.single_apply]

/-- The endpoint contribution is minus the tail count of endpoint factors. -/
theorem endpoint_exponent_apply (p : D.FormalProduct O n) (i : Fin n) :
    (∑ j : Fin n, p.endpointPowers j • (fun a : Fin n => if a.val < j.val + 1 then (-1 : ℤ) else 0)) i =
      -((∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val), p.endpointPowers j : ℕ) : ℤ) := by
  classical
  simp only [Finset.sum_apply, nsmul_eq_mul, Finset.sum_filter,
    Nat.cast_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i.val ≤ j.val
  · change i ≤ j at hij
    simp [hij]
  · change ¬ i ≤ j at hij
    simp [hij]

/-- Coordinatewise formula with the exact variable, endpoint-tail, and
first-dead counts used by Lemma X. -/
theorem formalExponent_apply (p : D.FormalProduct O n) (i : Fin n) :
    p.formalExponent i = (p.variablePowers i : ℤ) -
      ((∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val), p.endpointPowers j : ℕ) : ℤ) +
      (p.deadFactors.map (fun h => h.val.formalExponent h.property i)).sum := by
  simp only [formalExponent, Pi.add_apply, p.variable_exponent_apply,
    p.endpoint_exponent_apply, list_sum_function_apply, sub_eq_add_neg]

end FormalProduct

/-- Every generator has one product-count presentation. Endpoint zero is
absorbed into its original coefficient π^κ. -/
theorem formalGenerator_exists_product (O : Subring K) (π : O)
    {f : Laurent (FractionRing O) n} (hf : D.FormalGenerator O π n f) :
    ∃ p : D.FormalProduct O n, p.formal π = f := by
  classical
  cases hf with
  | coefficient a =>
      exact ⟨⟨a, 0, 0, []⟩, by simp [FormalProduct.formal]⟩
  | coordinate i =>
      refine ⟨⟨1, Pi.single i 1, 0, []⟩, ?_⟩
      simp [FormalProduct.formal, Pi.single_apply, ← AddMonoidAlgebra.one_def]
  | endpoint j hj =>
      cases j with
      | zero =>
          refine ⟨⟨π ^ D.exponent, 0, 0, []⟩, ?_⟩
          simp [FormalProduct.formal, endpointMonomial]
          rfl
      | succ j =>
          refine ⟨⟨1, 0, Pi.single (⟨j, hj⟩ : Fin n) 1, []⟩, ?_⟩
          simp [FormalProduct.formal, Pi.single_apply, ← AddMonoidAlgebra.one_def]
  | firstDead h hn =>
      exact ⟨⟨1, 0, 0, [⟨h, hn⟩]⟩, by simp [FormalProduct.formal, ← AddMonoidAlgebra.one_def]⟩

/-- Every element of E_n is a finite sum of literal source-generator products.
The coefficients remain elements of the original O, not of its completion. -/
theorem formalRing_exists_products (O : Subring K) (π : O)
    {f : Laurent (FractionRing O) n} (hf : f ∈ D.formalRing O π n) :
    ∃ ps : List (D.FormalProduct O n), (ps.map (fun p => p.formal π)).sum = f := by
  induction hf using Subring.closure_induction with
  | mem f hf =>
      obtain ⟨p, rfl⟩ := D.formalGenerator_exists_product O π hf
      exact ⟨[p], by simp⟩
  | zero => exact ⟨[], by simp⟩
  | one =>
      exact ⟨[⟨1, 0, 0, []⟩], by simp [FormalProduct.formal, ← AddMonoidAlgebra.one_def]⟩
  | add f g hf hg ihf ihg =>
      obtain ⟨ps, rfl⟩ := ihf
      obtain ⟨qs, rfl⟩ := ihg
      exact ⟨ps ++ qs, by simp⟩
  | neg f hf ih =>
      obtain ⟨ps, rfl⟩ := ih
      refine ⟨ps.map FormalProduct.neg, ?_⟩
      clear hf
      induction ps with
      | nil => simp
      | cons p ps ih =>
          simp only [List.map_cons, List.sum_cons, FormalProduct.formal_neg, neg_add_rev]
          rw [ih, add_comm]
  | mul f g hf hg ihf ihg =>
      obtain ⟨ps, rfl⟩ := ihf
      obtain ⟨qs, rfl⟩ := ihg
      refine ⟨ps.flatMap (fun p => qs.map (fun q => p.mul q)), ?_⟩
      clear hf hg
      induction ps with
      | nil => simp
      | cons p ps ih =>
          simp only [List.flatMap_cons, List.map_append, List.sum_append,
            List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
            FormalProduct.formal_mul]
          rw [List.sum_map_mul_left, ih, add_mul]

end SourceBlockData
end HereditaryAtomicity.DVRBase
