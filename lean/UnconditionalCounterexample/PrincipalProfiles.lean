import UnconditionalCounterexample.PoleAlgebra
import UnconditionalCounterexample.RawWords
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Group.Subgroup.Finsupp

/-!
# Actual signed principal-factor representations

Factoring canonical numerators and denominators gives finite signed orders at the
monic irreducibles. For a unit of the pole algebra, these factors all occur in the
selected denominators. Injectivity of the raw factor sequence therefore produces a
finite signed word.

The triangular raw-denominator normalization preserves the generated subgroup
of the nonzero rational functions. Hence every such B-unit is a nonzero
constant times a finite signed word in the actual normalized generators.
Guard-unit conditions, the conclusion that the constant is a sign, and the
realization of the primary valuation formulas are separate downstream steps.
No finite-generation assumption or abstract representation hypothesis is used.
-/

noncomputable section
namespace UnconditionalCounterexample.PrincipalProfiles
open Polynomial UniqueFactorizationMonoid
open scoped BigOperators

variable {k α : Type*} [Field k]

local instance : DecidableEq k := Classical.decEq k

/-- Monic irreducibles index finite affine principal orders. -/
abbrev MonicIrreducible (k : Type*) [Field k] := {p : k[X] // p.Monic ∧ Irreducible p}

/-- Canonical polynomial image associated with a monic irreducible. -/
def factor (p : MonicIrreducible k) : RatFunc k := algebraMap k[X] (RatFunc k) p.val

theorem factor_ne_zero (p : MonicIrreducible k) : factor p ≠ 0 :=
  RatFunc.algebraMap_ne_zero p.property.1.ne_zero

/-- A signed finite product in an arbitrary field. -/
def word {L : Type*} [Field L] (P : α → L) (e : α →₀ ℤ) : L :=
  e.prod fun a n => P a ^ n

theorem word_add {L : Type*} [Field L] (P : α → L) (hP : ∀ a, P a ≠ 0)
    (e d : α →₀ ℤ) : word P (e + d) = word P e * word P d :=
  Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun a _ _ => zpow_add₀ (hP a) _ _)

theorem word_neg {L : Type*} [Field L] (P : α → L) (e : α →₀ ℤ) :
    word P (-e) = (word P e)⁻¹ := by
  rw [word, Finsupp.prod_neg_index (fun _ => zpow_zero _)]
  simp only [zpow_neg, word, Finsupp.prod, Finset.prod_inv_distrib]

theorem word_sub {L : Type*} [Field L] (P : α → L) (hP : ∀ a, P a ≠ 0)
    (e d : α →₀ ℤ) : word P (e - d) = word P e / word P d := by
  rw [sub_eq_add_neg, word_add P hP, word_neg, div_eq_mul_inv]

/-- The signed multiplicity vector attached to a finite multiset. -/
def multiplicities (s : Multiset α) : α →₀ ℤ := by
  classical
  exact s.toFinsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp)

theorem word_multiplicities {L : Type*} [Field L] (P : α → L) (s : Multiset α) :
    word P (multiplicities s) = (s.map P).prod := by
  classical
  rw [word, multiplicities, Finsupp.prod_mapRange_index (fun _ => zpow_zero _)]
  simp only [zpow_natCast, Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  exact (Finset.prod_multiset_map_count s P).symm

/-- The normalized factors of a nonzero polynomial, with their monic/irreducible proofs. -/
def factors (f : k[X]) (hf : f ≠ 0) : Multiset (MonicIrreducible k) := by
  classical
  exact (normalizedFactors f).attach.map fun p =>
    ⟨p.val, ((Polynomial.mem_normalizedFactors_iff hf).mp p.property).2.1,
      ((Polynomial.mem_normalizedFactors_iff hf).mp p.property).1⟩

@[simp] theorem factors_map_val (f : k[X]) (hf : f ≠ 0) :
    (factors f hf).map Subtype.val = normalizedFactors f := by
  classical
  simp [factors, Multiset.map_map]

/-- Actual polynomial factorization after the canonical inclusion into k(t). -/
theorem polynomial_factorization (f : k[X]) (hf : f ≠ 0) :
    algebraMap k[X] (RatFunc k) f =
      RatFunc.C f.leadingCoeff * word factor (multiplicities (factors f hf)) := by
  classical
  rw [word_multiplicities]
  have hprod : ((factors f hf).map factor).prod =
      algebraMap k[X] (RatFunc k) (normalizedFactors f).prod := by
    calc
      ((factors f hf).map factor).prod =
          (((factors f hf).map Subtype.val).map (algebraMap k[X] (RatFunc k))).prod := by
        rw [Multiset.map_map]
        rfl
      _ = ((normalizedFactors f).map (algebraMap k[X] (RatFunc k))).prod := by
        rw [factors_map_val]
      _ = _ := (map_multiset_prod _ _).symm
  rw [hprod, ← RatFunc.algebraMap_C, ← map_mul, Polynomial.leadingCoeff_mul_prod_normalizedFactors]

/-- Canonical signed orders of a nonzero rational function at monic irreducibles. -/
def exponents (x : RatFunc k) (hx : x ≠ 0) : MonicIrreducible k →₀ ℤ :=
  multiplicities (factors x.num (RatFunc.num_ne_zero hx)) -
    multiplicities (factors x.denom x.denom_ne_zero)

/-- The actual signed factorization of the canonical numerator and denominator. -/
theorem signed_factorization (x : RatFunc k) (hx : x ≠ 0) :
    x = RatFunc.C (x.num.leadingCoeff / x.denom.leadingCoeff) * word factor (exponents x hx) := by
  conv_lhs => rw [← RatFunc.num_div_denom x]
  rw [polynomial_factorization x.num (RatFunc.num_ne_zero hx),
    polynomial_factorization x.denom x.denom_ne_zero]
  rw [exponents, word_sub factor factor_ne_zero, map_div₀]
  ring

/-- Every nonzero rational function is a constant times a finite signed product. -/
theorem exists_signed_factorization (x : RatFunc k) (hx : x ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ ∃ e : MonicIrreducible k →₀ ℤ,
      x = RatFunc.C c * word factor e :=
  ⟨x.num.leadingCoeff / x.denom.leadingCoeff,
    div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hx))
      (Polynomial.leadingCoeff_ne_zero.mpr x.denom_ne_zero), exponents x hx,
    signed_factorization x hx⟩

@[simp] theorem mem_multiplicities_support (s : Multiset α) (a : α) :
    a ∈ (multiplicities s).support ↔ a ∈ s := by
  classical
  simp [multiplicities, Finsupp.mem_support_iff]

theorem mem_factors_iff (f : k[X]) (hf : f ≠ 0) (p : MonicIrreducible k) :
    p ∈ factors f hf ↔ p.val ∣ f := by
  have heq : p.val ∈ (factors f hf).map Subtype.val ↔ p ∈ factors f hf := by
    rw [Multiset.mem_map]
    constructor
    · rintro ⟨q, hq, heq⟩
      exact (Subtype.ext heq : q = p) ▸ hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  rw [factors_map_val, Polynomial.mem_normalizedFactors_iff hf] at heq
  simpa only [p.property.1, p.property.2, true_and] using heq.symm

/-- A B-unit has signed affine support only among factors of selected denominators. -/
theorem exponent_support_of_unit (S : Set k[X]) (hS : ∀ q ∈ S, q ≠ 0)
    (x : RatFunc k) (hx0 : x ≠ 0) (hx : x ∈ PoleAlgebra.generated S)
    (hxi : x⁻¹ ∈ PoleAlgebra.generated S) (p : MonicIrreducible k)
    (hp : p ∈ (exponents x hx0).support) : ∃ q ∈ S, p.val ∣ q := by
  classical
  have hpprime : Prime p.val := irreducible_iff_prime.mp p.property.2
  by_cases hpn : p ∈ factors x.num (RatFunc.num_ne_zero hx0)
  · have hpdvd := (mem_factors_iff x.num (RatFunc.num_ne_zero hx0) p).mp hpn
    exact PoleAlgebra.denom_prime_support S hS hxi hpprime
      (hpdvd.trans (RatFunc.associated_denom_inv hx0).symm.dvd)
  · have hnum0 : multiplicities (factors x.num (RatFunc.num_ne_zero hx0)) p = 0 := by
      simpa only [← mem_multiplicities_support, Finsupp.notMem_support_iff] using hpn
    have hpden : p ∈ factors x.denom x.denom_ne_zero := by
      rw [← mem_multiplicities_support, Finsupp.mem_support_iff]
      rw [Finsupp.mem_support_iff, exponents, Finsupp.sub_apply, hnum0, zero_sub, neg_ne_zero] at hp
      exact hp
    exact PoleAlgebra.denom_prime_support S hS hx hpprime
      ((mem_factors_iff x.denom x.denom_ne_zero p).mp hpden)

/-- If the selected polynomials are monic irreducibles, every nonzero signed
exponent of a B-unit belongs to their actual range. -/
theorem exponent_support_in_raw_range (F : ℕ → k[X])
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i))
    (x : RatFunc k) (hx0 : x ≠ 0) (hx : x ∈ PoleAlgebra.generated (Set.range F))
    (hxi : x⁻¹ ∈ PoleAlgebra.generated (Set.range F)) (p : MonicIrreducible k)
    (hp : p ∈ (exponents x hx0).support) : ∃ i, F i = p.val := by
  obtain ⟨q, ⟨i, rfl⟩, hpF⟩ := exponent_support_of_unit (Set.range F)
    (by rintro q ⟨i, rfl⟩; exact (hF i).1.ne_zero) x hx0 hx hxi p hp
  refine ⟨i, ?_⟩
  exact (Polynomial.eq_of_monic_of_associated p.property.1 (hF i).1
    (p.property.2.associated_of_dvd (hF i).2 hpF)).symm

/-- A signed finite product reindexes along an injection covering its support. -/
theorem word_comapDomain {β L : Type*} [Field L] (P : β → L)
    (f : α → β) (hf : Function.Injective f) (e : β →₀ ℤ)
    (he : (e.support : Set β) ⊆ Set.range f) :
    word (P ∘ f) (e.comapDomain f hf.injOn) = word P e := by
  have hbij : Set.BijOn f (f ⁻¹' (e.support : Set β)) (e.support : Set β) := by
    refine ⟨fun _ h => h, hf.injOn, ?_⟩
    intro b hb
    obtain ⟨a, rfl⟩ := he hb
    exact ⟨a, hb, rfl⟩
  exact Finsupp.prod_comapDomain f e (fun b n => P b ^ n) hbij

/-- The actual raw-factor representation of a unit of the selected pole algebra. -/
theorem exists_raw_factorization (F : ℕ → k[X])
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (x : RatFunc k) (hx0 : x ≠ 0) (hx : x ∈ PoleAlgebra.generated (Set.range F))
    (hxi : x⁻¹ ∈ PoleAlgebra.generated (Set.range F)) :
    ∃ c : k, c ≠ 0 ∧ ∃ e : ℕ →₀ ℤ,
      x = RatFunc.C c * word (fun i => algebraMap k[X] (RatFunc k) (F i)) e := by
  let index : ℕ → MonicIrreducible k := fun i => ⟨F i, hF i⟩
  have hi : Function.Injective index := fun i j h => hinj (congrArg Subtype.val h)
  have hs : ((exponents x hx0).support : Set (MonicIrreducible k)) ⊆ Set.range index := by
    intro p hp
    obtain ⟨i, hi⟩ := exponent_support_in_raw_range F hF x hx0 hx hxi p hp
    exact ⟨i, Subtype.ext hi⟩
  refine ⟨x.num.leadingCoeff / x.denom.leadingCoeff,
    div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hx0))
      (Polynomial.leadingCoeff_ne_zero.mpr x.denom_ne_zero),
    (exponents x hx0).comapDomain index hi.injOn, ?_⟩
  conv_lhs => rw [signed_factorization x hx0]
  rw [← word_comapDomain factor index hi _ hs]
  rfl

/-- Triangular normalization preserves the subgroup generated by the raw factors. -/
theorem closure_normalized_eq {G : Type*} [CommGroup G] (P : ℕ → G) (E : ℕ → ℕ) :
    Subgroup.closure (Set.range (fun i => P i / ∏ j ∈ Finset.range i, P j ^ E i)) =
      Subgroup.closure (Set.range P) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    apply Subgroup.div_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
    exact Submonoid.prod_mem _ fun j _ =>
      Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self j)) _
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    induction i using Nat.strong_induction_on with
    | h i ih =>
      have hbase := Subgroup.subset_closure (Set.mem_range_self i :
        P i / (∏ j ∈ Finset.range i, P j ^ E i) ∈
          Set.range (fun n => P n / ∏ j ∈ Finset.range n, P j ^ E n))
      have hprod : (∏ j ∈ Finset.range i, P j ^ E i) ∈
          Subgroup.closure (Set.range (fun n => P n / ∏ j ∈ Finset.range n, P j ^ E n)) :=
        Submonoid.prod_mem _ fun j hj => Subgroup.pow_mem _ (ih j (Finset.mem_range.mp hj)) _
      simpa using Subgroup.mul_mem _ hbase hprod

/-- Every finite raw group word has a finite signed word in the normalized generators. -/
theorem exists_group_normalized_word {G : Type*} [CommGroup G]
    (P : ℕ → G) (E : ℕ → ℕ) (e : ℕ →₀ ℤ) :
    ∃ d : ℕ →₀ ℤ, e.prod (fun i z => P i ^ z) =
      d.prod (fun i z => (P i / ∏ j ∈ Finset.range i, P j ^ E i) ^ z) := by
  apply Subgroup.exists_finsupp_of_mem_closure_range
  rw [closure_normalized_eq]
  exact Submonoid.prod_mem _ fun i _ =>
    Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

/-- The same triangular inversion for actual nonzero elements of a field. -/
theorem exists_normalized_word {L : Type*} [Field L]
    (P : ℕ → L) (hP : ∀ i, P i ≠ 0) (E : ℕ → ℕ) (e : ℕ →₀ ℤ) :
    ∃ d : ℕ →₀ ℤ, word P e = word (RawWords.normalizedFactor P E) d := by
  let U : ℕ → Lˣ := fun i => Units.mk0 (P i) (hP i)
  obtain ⟨d, hd⟩ := exists_group_normalized_word U E e
  refine ⟨d, ?_⟩
  have h := congrArg (fun z : Lˣ => (z : L)) hd
  simpa only [word, Finsupp.prod, RawWords.normalizedFactor, Units.coe_prod,
    Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_mk0, U] using h

/-- Every B-unit is a constant times a finite signed normalized word. -/
theorem exists_normalized_factorization (F : ℕ → k[X])
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (E : ℕ → ℕ) (x : RatFunc k) (hx0 : x ≠ 0)
    (hx : x ∈ PoleAlgebra.generated (Set.range F))
    (hxi : x⁻¹ ∈ PoleAlgebra.generated (Set.range F)) :
    ∃ c : k, c ≠ 0 ∧ ∃ e : ℕ →₀ ℤ,
      x = RatFunc.C c * word
        (RawWords.normalizedFactor (fun i => algebraMap k[X] (RatFunc k) (F i)) E) e := by
  obtain ⟨c, hc, e, he⟩ := exists_raw_factorization F hF hinj x hx0 hx hxi
  obtain ⟨d, hd⟩ := exists_normalized_word (fun i => algebraMap k[X] (RatFunc k) (F i))
    (fun i => RatFunc.algebraMap_ne_zero (hF i).1.ne_zero) E e
  exact ⟨c, hc, d, he.trans (congrArg (RatFunc.C c * ·) hd)⟩

end UnconditionalCounterexample.PrincipalProfiles
