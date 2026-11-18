import UnconditionalCounterexample.EvaluationDVR
import UnconditionalCounterexample.PrincipalProfiles
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Guard units force the rational scalar to be a sign

A rational scalar is a sign precisely when it is a unit at every rational
prime. Apply the actual guard homomorphisms to a scalar-times-signed-word
equality: if the element and every normalized generator have guard value one,
the scalar has value one at every prime. The actual UFD representation from
PrincipalProfiles then gives the element as a signed normalized word.

The guard-unit conditions are explicit. No assertion that arbitrary rational
constants, or arbitrary elements of the pole algebra, are signs is made.
-/

/-!
# Rational scalars in actual normalized words are signs

A unit of the pole algebra with guard orders zero has a finite normalized
representation. Guard evaluation makes its rational scalar a unit at every rational
prime, hence a sign.

-/

noncomputable section
namespace UnconditionalCounterexample.RationalSigns
open WithZero
variable {α K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

local instance primeFact (p : {p : ℕ // p.Prime}) : Fact p.val.Prime := ⟨p.property⟩

/-- A rational integral at every rational prime is an integer. -/
theorem integer_of_padic_le_one (q : ℚ)
    (h : ∀ p : {p : ℕ // p.Prime}, @Rat.padicValuation p.val ⟨p.property⟩ q ≤ 1) :
    ∃ z : ℤ, (z : ℚ) = q := by
  refine ⟨q.num, (Rat.den_eq_one_iff q).mp ?_⟩
  by_contra hden
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hden
  let : Fact p.Prime := ⟨hp⟩
  exact (Rat.padicValuation_le_one_iff.mp (h ⟨p, hp⟩)) hdvd

/-- A rational which is a unit at every rational prime is a sign. -/
theorem eq_one_or_neg_one_of_padic_eq_one (q : ℚ)
    (h : ∀ p : {p : ℕ // p.Prime}, @Rat.padicValuation p.val ⟨p.property⟩ q = 1) :
    q = 1 ∨ q = -1 := by
  obtain ⟨z, hz⟩ := integer_of_padic_le_one q (fun p => (h p).le)
  have hzabs : z.natAbs = 1 := by
    by_contra hzabs
    obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hzabs
    let : Fact p.Prime := ⟨hp⟩
    have hv : Int.padicValuation p z = 1 := by
      rw [← Rat.padicValuation_cast, hz]
      exact h ⟨p, hp⟩
    exact (Int.padicValuation_eq_one_iff.mp hv) (Int.natCast_dvd.mpr hdvd)
  rcases Int.natAbs_eq z with heq | heq
  · left
    rw [← hz, heq, hzabs]
    norm_num
  · right
    rw [← hz, heq, hzabs]
    norm_num

/-- A finite signed product of valuation units remains a valuation unit. -/
theorem valuation_finsupp_prod_eq_one (v : Valuation K Γ₀) (P : α → K)
    (e : α →₀ ℤ) (hP : ∀ i, v (P i) = 1) :
    v (e.prod (fun i z => P i ^ z)) = 1 := by
  rw [map_finsuppProd]
  apply Finset.prod_eq_one
  intro i _
  change v (P i ^ e i) = 1
  rw [map_zpow₀, hP, one_zpow]

/-- If a signed-word expression and every generator are guard units, the
rational coefficient is exactly a sign. No assertion is made about other constants. -/
theorem constant_sign_of_guard_units
    (g : ∀ p : {p : ℕ // p.Prime}, RatFunc ℚ →+* ℚ_[p.val])
    (P : α → RatFunc ℚ) (e : α →₀ ℤ) (x : RatFunc ℚ) (c : ℚ)
    (heq : x = RatFunc.C c * e.prod (fun i z => P i ^ z))
    (hx : ∀ p, @Padic.mulValuation p.val ⟨p.property⟩ (g p x) = 1)
    (hP : ∀ p i, @Padic.mulValuation p.val ⟨p.property⟩ (g p (P i)) = 1) :
    c = 1 ∨ c = -1 := by
  apply eq_one_or_neg_one_of_padic_eq_one
  intro p
  let : Fact p.val.Prime := ⟨p.property⟩
  let v := EvaluationDVR.valuation p.val (g p)
  have hword : v (e.prod (fun i z => P i ^ z)) = 1 :=
    valuation_finsupp_prod_eq_one v P e (hP p)
  have hxc : v (RatFunc.C c) = 1 := by
    have h := hx p
    change v x = 1 at h
    rw [heq, map_mul, hword, mul_one] at h
    exact h
  change Padic.mulValuation (g p (RatFunc.C c)) = 1 at hxc
  have hC : RatFunc.C c = (c : RatFunc ℚ) := by
    exact map_ratCast RatFunc.C c
  rw [hC, map_ratCast] at hxc
  have hval := congrArg (fun w : Valuation ℚ ℤᵐ⁰ => w c)
    (Padic.comap_mulValuation_eq_padicValuation (p := p.val))
  exact hval ▸ hxc

/-- A pole-algebra unit whose guard values all vanish is an actual signed
normalized word when the normalized generators are guard units. -/
theorem exists_signed_normalized_factorization
    (F : ℕ → Polynomial ℚ)
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (E : ℕ → ℕ) (x : RatFunc ℚ) (hx0 : x ≠ 0)
    (hxB : x ∈ PoleAlgebra.generated (Set.range F))
    (hxiB : x⁻¹ ∈ PoleAlgebra.generated (Set.range F))
    (g : ∀ p : {p : ℕ // p.Prime}, RatFunc ℚ →+* ℚ_[p.val])
    (hxg : ∀ p, @Padic.mulValuation p.val ⟨p.property⟩ (g p x) = 1)
    (hPg : ∀ p i, @Padic.mulValuation p.val ⟨p.property⟩
      (g p (RawWords.normalizedFactor
        (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (F j)) E i)) = 1) :
    ∃ e : ℕ →₀ ℤ,
      x = PrincipalProfiles.word (RawWords.normalizedFactor
        (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (F j)) E) e ∨
      x = -PrincipalProfiles.word (RawWords.normalizedFactor
        (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (F j)) E) e := by
  obtain ⟨c, _, e, he⟩ := PrincipalProfiles.exists_normalized_factorization F hF hinj E x hx0 hxB hxiB
  have hc := constant_sign_of_guard_units g _ e x c he hxg hPg
  refine ⟨e, ?_⟩
  rcases hc with rfl | rfl
  · left
    simpa only [map_one, one_mul] using he
  · right
    simpa only [map_neg, map_one, neg_one_mul] using he

end UnconditionalCounterexample.RationalSigns
