import Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Factorization bounds from additive measurements

The hypotheses describe measurements additive on nonzero products and zero on
units. Finite detector families bound occurrences of a specified predicate in
factorization multisets, including repeated factors. These are abstract counting
results: no existence of valuations, detector sets, or finite support is asserted.
-/

namespace Factorization

universe u v w

section AdditiveMeasurement

variable {M : Type u} [CommMonoidWithZero M]
  {A : Type v} [AddCommMonoid A]

/-- A measurement additive on nonzero products and zero on units is invariant
under association of nonzero elements. No law at zero is needed. -/
theorem degree_eq_of_associated (degree : M → A)
    (hunit : ∀ a : M, IsUnit a → degree a = 0)
    (hmul : ∀ a b : M, a ≠ 0 → b ≠ 0 → degree (a * b) = degree a + degree b)
    {x y : M} (hy : y ≠ 0) (hxy : Associated x y) : degree x = degree y := by
  obtain ⟨u, hu⟩ := hxy
  have hproduct : x * (u : M) ≠ 0 := by rwa [hu]
  rw [← hu, hmul x u (left_ne_zero_of_mul hproduct) (right_ne_zero_of_mul hproduct),
    hunit u u.isUnit, add_zero]

/-- Sum an additive measurement along a nonzero product. -/
theorem degree_prod_eq_sum (degree : M → A)
    (hunit : ∀ a : M, IsUnit a → degree a = 0)
    (hmul : ∀ a b : M, a ≠ 0 → b ≠ 0 → degree (a * b) = degree a + degree b)
    (factors : Multiset M) (hprod : factors.prod ≠ 0) :
    degree factors.prod = (factors.map degree).sum := by
  induction factors using Multiset.induction_on with
  | empty => simpa using hunit 1 isUnit_one
  | @cons a factors ih =>
      have hproduct : a * factors.prod ≠ 0 := by simpa using hprod
      simp only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      rw [hmul a factors.prod (left_ne_zero_of_mul hproduct)
        (right_ne_zero_of_mul hproduct), ih (right_ne_zero_of_mul hproduct)]

/-- The sum of the measurements of factors equals that of a nonzero associated
product; multiplication by a unit contributes zero. -/
theorem sum_degree_eq_of_associated (degree : M → A)
    (hunit : ∀ a : M, IsUnit a → degree a = 0)
    (hmul : ∀ a b : M, a ≠ 0 → b ≠ 0 → degree (a * b) = degree a + degree b)
    {x : M} (hx : x ≠ 0) (factors : Multiset M)
    (hfac : Associated factors.prod x) :
    (factors.map degree).sum = degree x := by
  rw [← degree_prod_eq_sum degree hunit hmul factors (hfac.ne_zero_iff.mpr hx)]
  exact degree_eq_of_associated degree hunit hmul hx hfac

end AdditiveMeasurement

section NaturalBounds

variable {M : Type u} [CommMonoidWithZero M]

omit [CommMonoidWithZero M] in
/-- Count selected occurrences, not distinct elements: each selected occurrence
contributes at least one to a natural-valued measurement. -/
theorem filter_card_le_sum_nat (degree : M → ℕ) (P : M → Prop) [DecidablePred P]
    (factors : Multiset M)
    (hdetect : ∀ a ∈ factors, P a → 1 ≤ degree a) :
    (factors.filter P).card ≤ (factors.map degree).sum := by
  induction factors using Multiset.induction_on with
  | empty => simp
  | @cons a factors ih =>
      have htail := ih (fun b hb => hdetect b (Multiset.mem_cons_of_mem hb))
      by_cases ha : P a
      · have hone := hdetect a (Multiset.mem_cons_self a factors) ha
        simp only [Multiset.filter_cons_of_pos _ ha, Multiset.card_cons,
          Multiset.map_cons, Multiset.sum_cons]
        omega
      · simp only [Multiset.filter_cons_of_neg _ ha, Multiset.map_cons, Multiset.sum_cons]
        omega

/-- A finite family of natural-valued additive detectors bounds the number of
selected factor occurrences by the sum of its values on the fixed product.
The family and its detection property are explicit inputs. -/
theorem filter_card_le_sum_nat_of_finite_detectors
    {ι : Type v} (indices : Finset ι) (weight : ι → M → ℕ)
    (hunit : ∀ i ∈ indices, ∀ a : M, IsUnit a → weight i a = 0)
    (hmul : ∀ i ∈ indices, ∀ a b : M, a ≠ 0 → b ≠ 0 →
      weight i (a * b) = weight i a + weight i b)
    {x : M} (hx : x ≠ 0) (factors : Multiset M)
    (hfac : Associated factors.prod x) (P : M → Prop) [DecidablePred P]
    (hdetect : ∀ a ∈ factors, P a → ∃ i ∈ indices, 0 < weight i a) :
    (factors.filter P).card ≤ ∑ i ∈ indices, weight i x := by
  let degree : M → ℕ := fun a => ∑ i ∈ indices, weight i a
  have hdegree_unit : ∀ a : M, IsUnit a → degree a = 0 := by
    intro a ha
    exact Finset.sum_eq_zero (fun i hi => hunit i hi a ha)
  have hdegree_mul : ∀ a b : M, a ≠ 0 → b ≠ 0 →
      degree (a * b) = degree a + degree b := by
    intro a b ha hb
    dsimp [degree]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => hmul i hi a b ha hb)
  have hcount := filter_card_le_sum_nat degree P factors (by
    intro a ha hPa
    obtain ⟨i, hi, hpos⟩ := hdetect a ha hPa
    have hle : weight i a ≤ degree a :=
      Finset.single_le_sum (fun j (_ : j ∈ indices) => Nat.zero_le (weight j a)) hi
    omega)
  rw [sum_degree_eq_of_associated degree hdegree_unit hdegree_mul hx factors hfac] at hcount
  exact hcount

/-- Natural-valued detectors for every nonunit divisor give an explicit bound
for every nonunit factorization of a nonzero element. -/
theorem factorization_card_le_of_finite_nat_detectors
    {ι : Type v} (indices : Finset ι) (weight : ι → M → ℕ)
    (hunit : ∀ i ∈ indices, ∀ a : M, IsUnit a → weight i a = 0)
    (hmul : ∀ i ∈ indices, ∀ a b : M, a ≠ 0 → b ≠ 0 →
      weight i (a * b) = weight i a + weight i b)
    {x : M} (hx : x ≠ 0)
    (hdetect : ∀ a : M, a ≠ 0 → a ∣ x → ¬ IsUnit a →
      ∃ i ∈ indices, 0 < weight i a)
    (factors : Multiset M) (hn : ∀ a ∈ factors, ¬ IsUnit a)
    (hfac : Associated factors.prod x) :
    factors.card ≤ ∑ i ∈ indices, weight i x := by
  have hcount := filter_card_le_sum_nat_of_finite_detectors indices weight hunit hmul
    hx factors hfac (fun _ => True) (by
      intro a ha _
      have hdvd : a ∣ x := (Multiset.dvd_prod ha).trans hfac.dvd
      exact hdetect a (ne_zero_of_dvd_ne_zero hx hdvd) hdvd (hn a ha))
  simpa using hcount

/-- A finite natural detector family proves bounded factorization without
assuming atomicity, ACCP, or uniqueness of factorization. -/
theorem hasBoundedFactorizations_of_finite_nat_detectors
    {ι : Type v} (indices : Finset ι) (weight : ι → M → ℕ)
    (hunit : ∀ i ∈ indices, ∀ a : M, IsUnit a → weight i a = 0)
    (hmul : ∀ i ∈ indices, ∀ a b : M, a ≠ 0 → b ≠ 0 →
      weight i (a * b) = weight i a + weight i b)
    {x : M} (hx : x ≠ 0)
    (hdetect : ∀ a : M, a ≠ 0 → a ∣ x → ¬ IsUnit a →
      ∃ i ∈ indices, 0 < weight i a) : HasBoundedFactorizations x :=
  ⟨∑ i ∈ indices, weight i x,
    factorization_card_le_of_finite_nat_detectors indices weight hunit hmul hx hdetect⟩

/-- A natural-valued additive degree positive on every nonunit divisor gives
an explicit linear bound on the length of each factorization. -/
theorem factorization_card_le_natDegree (degree : M → ℕ)
    (hunit : ∀ a : M, IsUnit a → degree a = 0)
    (hmul : ∀ a b : M, a ≠ 0 → b ≠ 0 → degree (a * b) = degree a + degree b)
    {x : M} (hx : x ≠ 0)
    (hpositive : ∀ a : M, a ≠ 0 → a ∣ x → ¬ IsUnit a → 0 < degree a)
    (factors : Multiset M) (hn : ∀ a ∈ factors, ¬ IsUnit a)
    (hfac : Associated factors.prod x) : factors.card ≤ degree x := by
  have hcount := filter_card_le_sum_nat degree (fun _ => True) factors (by
    intro a ha _
    have hdvd : a ∣ x := (Multiset.dvd_prod ha).trans hfac.dvd
    exact hpositive a (ne_zero_of_dvd_ne_zero hx hdvd) hdvd (hn a ha))
  rw [sum_degree_eq_of_associated degree hunit hmul hx factors hfac] at hcount
  simpa using hcount

/-- An additive natural degree proves bounded factorization of a nonzero
product when it is positive on every nonunit divisor of that product. -/
theorem hasBoundedFactorizations_of_natDegree (degree : M → ℕ)
    (hunit : ∀ a : M, IsUnit a → degree a = 0)
    (hmul : ∀ a b : M, a ≠ 0 → b ≠ 0 → degree (a * b) = degree a + degree b)
    {x : M} (hx : x ≠ 0)
    (hpositive : ∀ a : M, a ≠ 0 → a ∣ x → ¬ IsUnit a → 0 < degree a) :
    HasBoundedFactorizations x :=
  ⟨degree x, factorization_card_le_natDegree degree hunit hmul hx hpositive⟩

end NaturalBounds

section RealBounds

variable {M : Type u} [CommMonoidWithZero M]

omit [CommMonoidWithZero M] in
/-- Each selected occurrence contributes at least the chosen floor, while every
other occurrence contributes a nonnegative amount. -/
theorem filter_card_mul_le_sum_real (degree : M → ℝ) (P : M → Prop) [DecidablePred P]
    (floor : ℝ) (factors : Multiset M)
    (hnonnegative : ∀ a ∈ factors, 0 ≤ degree a)
    (hdetect : ∀ a ∈ factors, P a → floor ≤ degree a) :
    ((factors.filter P).card : ℝ) * floor ≤ (factors.map degree).sum := by
  induction factors using Multiset.induction_on with
  | empty => simp
  | @cons a factors ih =>
      have htail := ih (fun b hb => hnonnegative b (Multiset.mem_cons_of_mem hb))
        (fun b hb => hdetect b (Multiset.mem_cons_of_mem hb))
      by_cases ha : P a
      · have hfloor := hdetect a (Multiset.mem_cons_self a factors) ha
        simp only [Multiset.filter_cons_of_pos _ ha, Multiset.card_cons,
          Multiset.map_cons, Multiset.sum_cons, Nat.cast_add, Nat.cast_one]
        nlinarith
      · have hnonneg := hnonnegative a (Multiset.mem_cons_self a factors)
        simp only [Multiset.filter_cons_of_neg _ ha, Multiset.map_cons, Multiset.sum_cons]
        linarith

/-- Finite real-valued detectors give a linear estimate for the number of
selected factor occurrences. Every measurement is nonnegative on every factor,
and each selected factor reaches the specified floor at some detector. -/
theorem filter_card_mul_le_sum_real_of_finite_detectors
    {ι : Type v} (indices : Finset ι) (weight : ι → M → ℝ)
    (hunit : ∀ i ∈ indices, ∀ a : M, IsUnit a → weight i a = 0)
    (hmul : ∀ i ∈ indices, ∀ a b : M, a ≠ 0 → b ≠ 0 →
      weight i (a * b) = weight i a + weight i b)
    {x : M} (hx : x ≠ 0) (factors : Multiset M)
    (hfac : Associated factors.prod x) (P : M → Prop) [DecidablePred P]
    (floor : ℝ)
    (hnonnegative : ∀ i ∈ indices, ∀ a ∈ factors, 0 ≤ weight i a)
    (hdetect : ∀ a ∈ factors, P a → ∃ i ∈ indices, floor ≤ weight i a) :
    ((factors.filter P).card : ℝ) * floor ≤ ∑ i ∈ indices, weight i x := by
  let degree : M → ℝ := fun a => ∑ i ∈ indices, weight i a
  have hdegree_unit : ∀ a : M, IsUnit a → degree a = 0 := by
    intro a ha
    exact Finset.sum_eq_zero (fun i hi => hunit i hi a ha)
  have hdegree_mul : ∀ a b : M, a ≠ 0 → b ≠ 0 →
      degree (a * b) = degree a + degree b := by
    intro a b ha hb
    dsimp [degree]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => hmul i hi a b ha hb)
  have hcount := filter_card_mul_le_sum_real degree P floor factors
    (fun a ha => Finset.sum_nonneg (fun i hi => hnonnegative i hi a ha)) (by
      intro a ha hPa
      obtain ⟨i, hi, hfloor⟩ := hdetect a ha hPa
      exact hfloor.trans (Finset.single_le_sum (fun j hj => hnonnegative j hj a ha) hi))
  rw [sum_degree_eq_of_associated degree hdegree_unit hdegree_mul hx factors hfac] at hcount
  exact hcount

/-- A real additive degree with a common floor on nonunit divisors gives a
linear factorization-length estimate. Nonnegativity is required on all nonzero
divisors, including those not selected by the nonunit condition. -/
theorem factorization_card_mul_le_realDegree (degree : M → ℝ)
    (hunit : ∀ a : M, IsUnit a → degree a = 0)
    (hmul : ∀ a b : M, a ≠ 0 → b ≠ 0 → degree (a * b) = degree a + degree b)
    {x : M} (hx : x ≠ 0) (floor : ℝ)
    (hnonnegative : ∀ a : M, a ≠ 0 → a ∣ x → 0 ≤ degree a)
    (hfloor : ∀ a : M, a ≠ 0 → a ∣ x → ¬ IsUnit a → floor ≤ degree a)
    (factors : Multiset M) (hn : ∀ a ∈ factors, ¬ IsUnit a)
    (hfac : Associated factors.prod x) : (factors.card : ℝ) * floor ≤ degree x := by
  have hcount := filter_card_mul_le_sum_real degree (fun _ => True) floor factors
    (by
      intro a ha
      have hdvd : a ∣ x := (Multiset.dvd_prod ha).trans hfac.dvd
      exact hnonnegative a (ne_zero_of_dvd_ne_zero hx hdvd) hdvd) (by
      intro a ha _
      have hdvd : a ∣ x := (Multiset.dvd_prod ha).trans hfac.dvd
      exact hfloor a (ne_zero_of_dvd_ne_zero hx hdvd) hdvd (hn a ha))
  rw [sum_degree_eq_of_associated degree hunit hmul hx factors hfac] at hcount
  simpa using hcount

/-- A strictly positive floor for a real additive degree gives bounded
factorizations; a natural upper bound for `degree x / floor` suffices. -/
theorem hasBoundedFactorizations_of_realDegree (degree : M → ℝ)
    (hunit : ∀ a : M, IsUnit a → degree a = 0)
    (hmul : ∀ a b : M, a ≠ 0 → b ≠ 0 → degree (a * b) = degree a + degree b)
    {x : M} (hx : x ≠ 0) (floor : ℝ) (hpositive : 0 < floor)
    (hnonnegative : ∀ a : M, a ≠ 0 → a ∣ x → 0 ≤ degree a)
    (hfloor : ∀ a : M, a ≠ 0 → a ∣ x → ¬ IsUnit a → floor ≤ degree a) :
    HasBoundedFactorizations x := by
  obtain ⟨bound, hbound⟩ := exists_nat_ge (degree x / floor)
  refine ⟨bound, ?_⟩
  intro factors hn hfac
  have hlinear := factorization_card_mul_le_realDegree degree hunit hmul hx floor
    hnonnegative hfloor factors hn hfac
  have hreal : (factors.card : ℝ) ≤ bound :=
    ((le_div_iff₀ hpositive).mpr hlinear).trans hbound
  exact_mod_cast hreal

end RealBounds

end Factorization
