import UnconditionalCounterexample.Variations.MultiDomainLowCoordinates
import UnconditionalCounterexample.Variations.MultiDomainLowScalars
import UnconditionalCounterexample.Variations.MultiDomainLowMoving
import UnconditionalCounterexample.Variations.MultiDomainDescent
import UnconditionalCounterexample.UnitSigns

/-!
# Realizing the multivariate atomicity profiles

The input records the raw polynomial sequence and the local evaluation choices. The
actual valuations give the signed quotient congruences, unit signs,
coordinatewise divisibility, and the profiles of the moving divisors.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain
open WithZero DiscreteOrders PrincipalProfiles PrimaryWordProfiles NormalizedWords Filter

variable {r : ℕ} {A : Data (r+1)}

/-- Algebraic and valuation properties of the ordinary choices at each stage. -/
structure ProfileChoices (A : Data (r+1)) extends MovingData A where
  E : ℕ → ℕ
  irreducible_raw : ∀ i, Irreducible (A.raw i)
  retained_t : ∀ i, ¬ TPoly r ∣ A.raw i
  b_eq : ∀ n, RawWords.normalizedFactor (rawValue A) E (Generator.b n).stage =
    ((b n : poleAlgebra A) : FunctionField (r+1))
  q_eq : ∀ n, RawWords.normalizedFactor (rawValue A) E (Generator.q n).stage =
    ((qRatio n : poleAlgebra A) : FunctionField (r+1))
  guard_above : ∀ p, A.guard p (p.val : FunctionField (r+1)) < 1
  primary_late : ∀ x : FunctionField (r+1), x ≠ 0 → ∀ᶠ j in atTop, A.primary j x = coordinateVal A .limit x
  guard_finite : ∀ x : FunctionField (r+1), x ≠ 0 → {p | A.guard p x ≠ 1}.Finite

namespace ProfileChoices
variable (C : ProfileChoices A)

abbrev generator := RawWords.normalizedFactor (rawValue A) C.E

theorem generator_guard (p : GuardSupport.PrimeIndex) (i : ℕ) : A.guard p (C.generator i) = 1 := by
  obtain ⟨g, rfl⟩ := StageExponents.stage_surjective i
  cases g with
  | b n => exact (congrArg (A.guard p) (C.b_eq n)).trans (C.b_guard n p)
  | q n => exact (congrArg (A.guard p) (C.q_eq n)).trans (C.q_guard n p)

theorem signed_word {x : FunctionField (r+1)} (hx : x ≠ 0)
    (hl : order (coordinateVal A .limit) x = 0)
    (ho : ∀ i, order (coordinateVal A (.outside i)) x = 0) :
    ∃ e : ℕ →₀ ℤ, (x = word C.generator e ∨ x = -word C.generator e) ∧
      Represents (StageExponents.bExponents e) (StageExponents.qExponents e)
        (fun j ↦ order (A.primary j) x) := by
  obtain ⟨u,hu⟩ := pole_unit_of_horizontal_zero A hx hl (fun p ↦ ho (.inr p))
  obtain ⟨c, _, e, he⟩ := pole_unit_normalized_word A C.irreducible_raw C.E u
  rw [hu] at he
  have hs := sign_of_guard_units A.guard C.guard_above c (fun p ↦ by
    have h := (order_eq_zero_iff _ hx).mp (ho (.inl p))
    change A.guard p x = 1 at h
    have hw : A.guard p (word C.generator e) = 1 :=
      RationalSigns.valuation_finsupp_prod_eq_one _ _ _ (C.generator_guard p)
    rw [he, map_mul, hw, mul_one] at h
    exact h)
  have hw : x = word C.generator e ∨ x = -word C.generator e := by
    rcases hs with rfl | rfl
    · exact Or.inl (by simpa using he)
    · exact Or.inr (by simpa using he)
  exact ⟨e, hw, represents_actual_primary_orders A.primary C.generator
    (fun n j ↦ (congrArg (A.primary j) (C.b_eq n)).trans (C.b_primary n j))
    (fun n j ↦ (congrArg (A.primary j) (C.q_eq n)).trans (C.q_primary n j)) e x hx hw⟩

include C in
theorem pure_triple {x : FunctionField (r+1)} (hx : x ≠ 0)
    (hl : order (coordinateVal A .limit) x = 0)
    (ho : ∀ i, order (coordinateVal A (.outside i)) x = 0) :
    TripleCongruent (fun j ↦ order (A.primary j) x) := by
  obtain ⟨_, _, h⟩ := C.signed_word hx hl ho
  exact ValuationProfiles.tripleCongruent_of_represents h

include C in
theorem signs (x : ordinary A) (hx : IsUnit x) : x = 1 ∨ x = -1 := by
  have hzero (p) := order_eq_zero_of_isUnit (ordinary A) (coordinateVal A p)
    (fun z hz ↦ coordinate_integral A C.retained_t ⟨z, hz⟩ p) hx
  obtain ⟨e, he, hr⟩ := C.signed_word (x := (x : FunctionField (r+1)))
    (fun h ↦ hx.ne_zero (Subtype.ext h)) (hzero .limit) (fun i ↦ hzero (.outside i))
  have he0 := UnitSigns.exponents_eq_zero_of_represents_zero e _ hr (fun j ↦ hzero (.primary j))
  simp only [he0, word, Finsupp.prod_zero_index] at he
  exact he.imp Subtype.ext Subtype.ext

def profile : ValuationProfiles (ordinary A) (Outside A) where
  value p x := natOrder (coordinateVal A p) (x : FunctionField (r+1))
  value_unit p x hx := natOrder_eq_zero_of_isUnit _ _
    (fun z hz ↦ coordinate_integral A C.retained_t ⟨z,hz⟩ p) hx
  value_mul p x y hx hy := natOrder_mul _
    (fun h ↦ hx (Subtype.ext h)) (fun h ↦ hy (Subtype.ext h))
    (coordinate_integral A C.retained_t x p) (coordinate_integral A C.retained_t y p)
  unit_of_zero x hx hzero := by
    have ht : x ∣ 1 := (coordinate_dvd A C.retained_t x 1 hx one_ne_zero).mpr (fun p ↦ by
      rw [hzero]; exact Nat.zero_le _)
    exact isUnit_of_dvd_unit ht isUnit_one
  eventually_primary x hx := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp (C.primary_late x (fun h ↦ hx (Subtype.ext h)))
    exact ⟨N, fun j hj ↦ congrArg (fun z : ℤᵐ⁰ ↦ (-z.log).toNat) (hN j hj)⟩
  finite_outside x hx := by
    have hn : (x : FunctionField (r+1)) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    apply (finite_outside A hn (C.guard_finite x hn)).subset
    intro i hi hzero
    exact hi (congrArg Int.toNat hzero)
  pure_triple x hx hl ho := by
    have hn : (x : FunctionField (r+1)) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    have hc (p) := natOrder_cast (coordinateVal A p) hn (coordinate_integral A C.retained_t x p)
    have ht : order (coordinateVal A .limit) x = 0 := by rw [← hc, hl]; rfl
    have hout (i) : order (coordinateVal A (.outside i)) x = 0 := by rw [← hc, ho]; rfl
    convert C.pure_triple hn ht hout using 1
    funext j
    exact hc (.primary j)

theorem profile_cast (p) {x : ordinary A} (hx : x ≠ 0) :
    (C.profile.value p x : ℤ) = order (coordinateVal A p) (x : FunctionField (r+1)) :=
  natOrder_cast _ (fun h ↦ hx (Subtype.ext h)) (coordinate_integral A C.retained_t x p)

theorem signedDifferenceTriple : C.profile.SignedDifferenceTriple := by
  intro x y hx hy hlx hly hout
  have hxn : (x : FunctionField (r+1)) ≠ 0 := fun h ↦ hx (Subtype.ext h)
  have hyn : (y : FunctionField (r+1)) ≠ 0 := fun h ↦ hy (Subtype.ext h)
  have hc (p) : order (coordinateVal A p) ((x : FunctionField (r+1)) / y) =
      (C.profile.value p x : ℤ) - C.profile.value p y := by
    rw [order_div _ hxn hyn, C.profile_cast _ hx, C.profile_cast _ hy]
  have hl : order (coordinateVal A .limit) ((x : FunctionField (r+1)) / y) = 0 := by simp [hc, hlx, hly]
  have ho (i) : order (coordinateVal A (.outside i)) ((x : FunctionField (r+1)) / y) = 0 := by
    rw [hc, hout, sub_self]
  convert C.pure_triple (div_ne_zero hxn hyn) hl ho using 1
  funext j
  exact (hc (.primary j)).symm

/-- The actual ordinary coordinate system produced solely from the raw
polynomial, generator, and local-place hypotheses of the schedule. -/
def descent : DescentData A (Outside A) where
  profile := C.profile
  divides x y hx hy := (coordinate_dvd A C.retained_t x y hx hy).mpr
  signs := C.signs
  a := C.movingElement
  nonzero := C.movingElement_ne_zero
  order_one n := by
    apply Int.ofNat_inj.mp
    rw [C.profile_cast _ (C.movingElement_ne_zero n)]
    change -log (coordinateVal A .limit (C.movingPole n : FunctionField (r+1))) = _
    rw [C.horizontal_moving (coordinateVal A .limit) (fun _ h ↦ retained_integral A MvPolynomial.X_prime C.retained_t ⟨_,h⟩)]
    change -log (PrimeOrders.valuation (p := TPoly r) MvPolynomial.X_prime (algebraMap _ _ (TPoly r))) = _
    rw [PrimeOrders.valuation_self, log_exp]
    decide
  outside_zero n i := by
    apply Int.ofNat_inj.mp
    rw [C.profile_cast _ (C.movingElement_ne_zero n)]
    apply (order_eq_zero_iff _ (fun h ↦ C.movingElement_ne_zero n (Subtype.ext h))).mpr
    cases i with
    | inl p => exact C.guard_moving n p
    | inr p =>
      exact (C.horizontal_moving _ (fun _ h ↦ retained_integral A p.val.prime p.val.retained ⟨_,h⟩) n).trans
        (coordinate_other_first A p)
  moving_primary n j := by
    rw [C.profile_cast _ (C.movingElement_ne_zero n)]
    change -log (A.primary j (C.movingPole n : FunctionField (r+1))) = _
    rw [C.primary_moving, log_exp, neg_neg]

end ProfileChoices
end UnconditionalCounterexample.Variations.MultiDomain
