import UnconditionalCounterexample.Variations.UnivariateExtraction
import UnconditionalCounterexample.Variations.TwoChainExtraction
import UnconditionalCounterexample.UnitSigns
import UnconditionalCounterexample.Variations.TwoCentreHorizontalPoints

/-!
# Horizontal orders and signed words for the two-centre domain

The retained horizontal primes, all guards, and the two primary tails detect
divisibility. Only the actual enumeration, its generator valuations and its
stabilization at the two rational points depend on the two-colour selection.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.TwoCentreHorizontal

open Polynomial WithZero DiscreteOrders GuardSupport PrincipalProfiles
open Univariate UnivariateExtraction TwoChainExtraction

variable (R : Requirements)

theorem retained_point (c : Bool) : HorizontalOrders.Retained (poles R) (point c) := by
  apply (HorizontalOrders.retained_range_iff (chain R).raw
    (fun j => ⟨(chain R).raw_monic j, (chain R).raw_irreducible j⟩) (point c)).mpr
  rintro ⟨i, hi⟩
  have h := (chain R).raw_degree_five i
  rw [hi] at h
  change 5 ≤ (X - C (c.toNat : ℚ)).natDegree at h
  rw [natDegree_X_sub_C] at h
  omega

abbrev OtherHorizontal := {q : MonicIrreducible ℚ //
  HorizontalOrders.Retained (poles R) q ∧ ∀ c, q ≠ point c}

abbrev Outside := PrimeIndex ⊕ OtherHorizontal R

/-- These data are properties of the specific two-colour schedule. -/
structure PrimaryData where
  primary : Bool → ℕ → Valuation (RatFunc ℚ) ℤᵐ⁰
  mem_domain : ∀ x : RatFunc ℚ, x ∈ domain R ↔
    x ∈ poleAlgebra R ∧ (∀ c j, primary c j x ≤ 1) ∧ ∀ p, guardVal R p x ≤ 1
  generator_primary : ∀ c j i, primary c j (generator R i) = exp (-TwoChainSchedule.weight i c j)
  generator_guard : ∀ p i, guardVal R p (generator R i) = 1
  stabilizes : ∀ x : RatFunc ℚ, x ≠ 0 → ∀ c, ∃ N, ∀ i, N ≤ i →
    primary c i x = HorizontalOrders.valuation (point c) x

variable {R} (P : PrimaryData R)

def outsideVal : Outside R → Valuation (RatFunc ℚ) ℤᵐ⁰
  | .inl p => guardVal R p
  | .inr q => HorizontalOrders.valuation q.val

def valuation : Place (Outside R) → Valuation (RatFunc ℚ) ℤᵐ⁰
  | .endpoint c => HorizontalOrders.valuation (point c)
  | .primary c j => P.primary c j
  | .outside i => outsideVal i

theorem all_horizontal {Φ : MonicIrreducible ℚ → Prop}
    (hc : ∀ c, Φ (point c)) (hq : ∀ q : OtherHorizontal R, Φ q.val) :
    ∀ q, HorizontalOrders.Retained (poles R) q → Φ q := by
  intro q h
  by_cases he : ∃ c, q = point c
  · obtain ⟨c, rfl⟩ := he
    exact hc c
  · exact hq ⟨q, h, fun c heq => he ⟨c, heq⟩⟩

theorem mem_iff (x : RatFunc ℚ) : x ∈ domain R ↔ ∀ i, valuation P i x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [P.mem_domain, HorizontalOrders.mem_iff_retained_valuations_le_one (poles R) (poles_nonzero R) x hx]
  constructor
  · rintro ⟨hh, hp, hg⟩ i
    rcases i with ⟨c⟩ | ⟨c, j⟩ | ⟨p | q⟩
    · exact hh _ (retained_point R c)
    · exact hp _ _
    · exact hg _
    · exact hh _ q.property.1
  · intro h
    exact ⟨all_horizontal (fun c => h (.endpoint c)) (fun q => h (.outside (.inr q))),
      fun c j => h (.primary c j), fun p => h (.outside (.inl p))⟩

theorem integral (x : domain R) (i : Place (Outside R)) : valuation P i x ≤ 1 :=
  (mem_iff P x).mp x.property i

theorem full_intersection : domain R = fullIntersection (valuation P) := by
  ext x
  rw [mem_iff P, fullIntersection, IntersectionDomain.mem_intersection]
  simp

theorem dvd_iff (x y : domain R) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∣ y ↔ ∀ i, natOrder (valuation P i) (x : RatFunc ℚ) ≤ natOrder (valuation P i) (y : RatFunc ℚ) := by
  have h {D : Subring (RatFunc ℚ)} (he : D = fullIntersection (valuation P))
      (a b : D) (ha : a ≠ 0) (hb : b ≠ 0) : a ∣ b ↔ ∀ i,
      natOrder (valuation P i) (a : RatFunc ℚ) ≤ natOrder (valuation P i) (b : RatFunc ℚ) := by
    subst D
    exact dvd_iff_natOrder_le _ ha hb
  exact h (full_intersection P) x y hx hy

theorem finite_outside (x : RatFunc ℚ) (hx : x ≠ 0) :
    {i : Outside R | outsideVal i x ≠ 1}.Finite := by
  have hg := guard_support R x hx
  have hh : {q : OtherHorizontal R | HorizontalOrders.valuation q.val x ≠ 1}.Finite :=
    (HorizontalOrders.finite_valuation_support x hx).preimage Subtype.val_injective.injOn
  exact ((hg.image (Sum.inl (β := OtherHorizontal R))).union
    (hh.image (Sum.inr (α := PrimeIndex)))).subset (by
      rintro (p | q) h
      · exact Or.inl ⟨p, h, rfl⟩
      · exact Or.inr ⟨q, h, rfl⟩)

include P in
theorem pure_word (x : RatFunc ℚ) (hx : x ≠ 0)
    (he : ∀ c, DiscreteOrders.order (HorizontalOrders.valuation (point c)) x = 0)
    (ho : ∀ i : Outside R, DiscreteOrders.order (outsideVal i) x = 0) :
    ∃ e : ℕ →₀ ℤ, x = word (generator R) e ∨ x = -word (generator R) e :=
  signed_word_of_horizontal_units R P.generator_guard x hx
    (all_horizontal (fun c => (order_eq_zero_iff _ hx).mp (he c))
      (fun q => (order_eq_zero_iff _ hx).mp (ho (.inr q))))
    (fun p => (order_eq_zero_iff _ hx).mp (ho (.inl p)))

include P in
theorem signed_units (x : domain R) (hu : IsUnit x) : x = 1 ∨ x = -1 := by
  have hx : (x : RatFunc ℚ) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
  have hz (i : Place (Outside R)) : DiscreteOrders.order (valuation P i) (x : RatFunc ℚ) = 0 :=
    order_eq_zero_of_isUnit _ _ (fun a ha => integral P ⟨a, ha⟩ _) hu
  obtain ⟨e, he⟩ := pure_word P x hx (fun c => hz (.endpoint c)) (fun i => hz (.outside i))
  have rep := TwoChainSchedule.represents_signed_word P.primary (generator R) P.generator_primary
    e x he (fun _ _ => 0) (fun c j => by
      simpa only [neg_zero, exp_zero, valuation] using (order_eq_zero_iff _ hx).mp (hz (.primary c j)))
  have hzero : e = 0 := by
    ext j
    obtain ⟨c, g, rfl⟩ := TwoChainSchedule.stage_surjective j
    have hb := NormalizedWords.exponent_bounds (rep c) (r := 0) (fun _ => ⟨le_rfl, le_rfl⟩)
    cases g with
    | b n => have h := (hb n).1; simp at h; exact h
    | q n => exact le_antisymm (hb n).2.2 (hb n).2.1
  rw [hzero] at he
  simpa only [word, Finsupp.prod_zero_index, Subtype.ext_iff, Subring.coe_one, Subring.coe_neg] using he

/-- The signed quotient may be outside the integral intersection. Equal
endpoint and supplementary orders still force the triple relations on both
primary difference sequences. -/
theorem difference_triple (z u : domain R) (hz : z ≠ 0) (hu : u ≠ 0)
    (he : ∀ c, natOrder (HorizontalOrders.valuation (point c)) z =
      natOrder (HorizontalOrders.valuation (point c)) u)
    (ho : ∀ i : Outside R, natOrder (outsideVal i) z = natOrder (outsideVal i) u) (c : Bool) :
    TripleCongruent (fun j => (natOrder (P.primary c j) z : ℤ) - natOrder (P.primary c j) u) := by
  have hz0 : (z : RatFunc ℚ) ≠ 0 := fun h => hz (Subtype.ext h)
  have hu0 : (u : RatFunc ℚ) ≠ 0 := fun h => hu (Subtype.ext h)
  have hquot (i : Place (Outside R)) : DiscreteOrders.order (valuation P i) ((z : RatFunc ℚ) / u) =
      (natOrder (valuation P i) z : ℤ) - natOrder (valuation P i) u := by
    rw [DiscreteOrders.order_div _ hz0 hu0, natOrder_cast _ hz0 (integral P z i),
      natOrder_cast _ hu0 (integral P u i)]
  obtain ⟨e, hw⟩ := pure_word P ((z : RatFunc ℚ) / u) (div_ne_zero hz0 hu0)
    (fun c => (hquot (.endpoint c)).trans (by rw [show
      natOrder (valuation P (.endpoint c)) z = natOrder (valuation P (.endpoint c)) u from he c]; simp))
    (fun i => (hquot (.outside i)).trans (by rw [show natOrder (valuation P (.outside i)) z =
      natOrder (valuation P (.outside i)) u from ho i]; simp))
  apply ValuationProfiles.tripleCongruent_of_represents
    (TwoChainSchedule.represents_signed_word P.primary (generator R) P.generator_primary e _ hw
      (fun c j => (natOrder (P.primary c j) z : ℤ) - natOrder (P.primary c j) u) _ c)
  intro d j
  exact (value_eq_exp_neg_order _ (div_ne_zero hz0 hu0)).trans
    (congrArg (fun z : ℤ => exp (-z)) (hquot (.primary d j)))

/-- The complete intrinsic natural orders used in the two-colour box and
descent theorems. -/
def orders : TwoChainBox.Orders (domain R) (Outside R) where
  endpoint x c := natOrder (HorizontalOrders.valuation (point c)) x
  primary x c j := natOrder (P.primary c j) x
  outside x i := natOrder (outsideVal i) x
  eventually_primary x hx c := by
    obtain ⟨N, h⟩ := P.stabilizes x (fun h => hx (Subtype.ext h)) c
    exact ⟨N, fun i hi => congrArg (fun v => (-WithZero.log v).toNat) (h i hi)⟩
  finite_outside x hx := (finite_outside (R := R) x (fun h => hx (Subtype.ext h))).subset (by
    intro i hi ho
    apply hi
    change (-WithZero.log (outsideVal i (x : RatFunc ℚ))).toNat = 0
    simp [ho])
  le_of_dvd {z x} hx hd := by
    have h := (dvd_iff P z x (ne_zero_of_dvd_ne_zero hx hd) hx).mp hd
    exact ⟨fun c => h (.endpoint c), fun c j => h (.primary c j), fun i => h (.outside i)⟩
  difference_triple z u hz hu he ho := difference_triple P z u hz hu (congrFun he) (congrFun ho)
  associated_of_eq z u hz hu he ho hp := by
    have h (i : Place (Outside R)) : natOrder (valuation P i) z = natOrder (valuation P i) u := by
      cases i with
      | endpoint c => exact congrFun he c
      | primary c j => exact congrFun (congrFun hp c) j
      | outside i => exact congrFun ho i
    exact associated_of_dvd_dvd ((dvd_iff P z u hz hu).mpr fun i => (h i).le)
      ((dvd_iff P u z hu hz).mpr fun i => (h i).ge)

theorem order_eq_natOrder (i : Place (Outside R)) (x : domain R) :
    TwoChainExtraction.order (orders P) i x = natOrder (valuation P i) x := by
  cases i <;> rfl

theorem detects_divisibility : (orders P).DetectsDivisibility := by
  intro x y hx hy he hp ho
  apply (dvd_iff P x y hx hy).mpr
  rintro (⟨c⟩ | ⟨c, j⟩ | ⟨i⟩)
  · exact he c
  · exact hp c j
  · exact ho i

include P in
theorem listed_of_unbounded (T : Subring (domain R)) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) : Nonempty (ListedSequence R T) := by
  have hunit (i : Place (Outside R)) (y : domain R) (hy : IsUnit y) :
      TwoChainExtraction.order (orders P) i y = 0 := by
    rw [order_eq_natOrder]
    exact natOrder_eq_zero_of_isUnit _ _ (fun a ha => integral P ⟨a, ha⟩ _) hy
  have hmul (i : Place (Outside R)) (a b : domain R) (ha : a ≠ 0) (hb : b ≠ 0) :
      TwoChainExtraction.order (orders P) i (a*b) = TwoChainExtraction.order (orders P) i a +
        TwoChainExtraction.order (orders P) i b := by
    simp only [order_eq_natOrder, Subring.coe_mul]
    exact natOrder_mul _ (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
      (integral P a i) (integral P b i)
  obtain ⟨r, hr, y, k, w, ht, h⟩ := TwoChainExtraction.exists_listed_sequence (orders P) hunit hmul
    (domain R).subtype (generator R) P.primary P.generator_primary
    (fun y hy c j => by
      have h := natOrder_cast (valuation P (.primary c j))
        (show (y : RatFunc ℚ) ≠ 0 from fun h => hy (Subtype.ext h)) (integral P y _)
      exact (value_eq_exp_neg_order _ (show (y : RatFunc ℚ) ≠ 0 from fun h => hy (Subtype.ext h))).trans
        (congrArg (fun z : ℤ => exp (-z)) h.symm))
    (fun y hy he ho => by
      have hy0 : (y : RatFunc ℚ) ≠ 0 := fun h => hy (Subtype.ext h)
      have eqzero (i : Place (Outside R)) (hn : TwoChainExtraction.order (orders P) i y = 0) :
          DiscreteOrders.order (valuation P i) y = 0 := by
        rw [← natOrder_cast _ hy0 (integral P y i), ← order_eq_natOrder, hn, Nat.cast_zero]
      exact pure_word P y hy0 (fun c => eqzero (.endpoint c) (he c)) (fun i => eqzero (.outside i) (ho i)))
    T (UnitSigns.subring_reflects_units (signed_units P) T) hx hunbounded
  exact ⟨{ element := fun i => ⟨inclusion R (y i : domain R), ⟨_, (y i).property, rfl⟩⟩
           stage := k
           word := w
           bound := 2*r
           bounded := fun i => (h i).2.1
           tends := ht
           expansion := fun i => (h i).2.2.2 }⟩

include P in
theorem integer_conductor (T : Subring (domain R)) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    (∃ n : ℕ, 0 < n ∧ (n : domain R) * coordinate R ∈ T) ∧
    ∀ n : ℕ, (n : domain R) * coordinate R ∈ T → ∀ z : domain R, (n : domain R) * z ∈ T := by
  obtain ⟨L⟩ := listed_of_unbounded P T x hx hunbounded
  exact L.integer_conductor

end UnconditionalCounterexample.Variations.TwoCentreHorizontal
