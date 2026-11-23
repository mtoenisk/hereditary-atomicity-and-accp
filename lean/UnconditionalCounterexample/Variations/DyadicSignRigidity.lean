import UnconditionalCounterexample.Variations.DyadicConcreteDomain
import UnconditionalCounterexample.Variations.DyadicSignedField
import UnconditionalCounterexample.Variations.DyadicGeneratorColumns

/-!
# Sign rigidity in the calibrated dyadic intersection

The minus coordinates isolate every balanced exponent, and the auxiliary
coordinates isolate each auxiliary exponent. The remaining adjacent map is
injective. Consequently a signed normalized word with zero profile has no
nonzero exponents.
-/

noncomputable section
namespace UnconditionalCounterexample.DyadicDeviations
variable {J : Bool → Type*} {G H : Type*}

theorem Profile.columns_zero_of_translate_eq (p : Profile J G H) (index : (k : Bool) → J k → ℕ)
    (sign : (k : Bool) → J k → ℤ) (e : Columns J) (h : p.translate index sign e = p) : e = 0 := by
  rcases e with ⟨r,q,s⟩
  have hr (k : Bool) : r k = 0 := by
    have := congrArg (fun t : Profile J G H => t.minusDeviation k) h
    simpa [Profile.translate,Profile.addColumns] using this
  have hs (k : Bool) : s k = 0 := by
    have := congrArg (fun t : Profile J G H => t.auxiliary k) h
    simpa [Profile.translate,Profile.addColumns] using this
  have hq (k : Bool) : q k = 0 := by
    apply DyadicColumns.adjacent_injective
    have := congrArg (fun t : Profile J G H => t.plusDeviation k) h
    simpa [Profile.translate,Profile.addColumns,hr k,hs k] using this
  exact Prod.ext (funext hr) (Prod.ext (funext hq) (funext hs))

end UnconditionalCounterexample.DyadicDeviations

namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open GuardSupport Univariate DiscreteOrders DyadicDeviations FieldGeneration PrincipalProfiles

variable (a : Policy)

private def stageColumns : (ℕ →₀ ℤ) →+ Columns (Aux a) :=
  (columnsOfRaw (auxiliaryPrime a) (auxIndex a) (auxPositive a)).comp
    (Finsupp.mapDomain.addMonoidHom (fun n => ((driver a).actualRequest n).column))

private theorem stageColumns_injective_zero (e : ℕ →₀ ℤ) (h : stageColumns a e = 0) : e = 0 := by
  ext n
  let lab (t : ℕ) := ((driver a).actualRequest t).column
  let d := e.mapDomain lab
  have hd : columnsOfRaw (auxiliaryPrime a) (auxIndex a) (auxPositive a) d = 0 := h
  have zeroAt : d (lab n) = 0 := by
    obtain ⟨g,hg⟩ := column_is_basis a n
    change basisLabel (auxiliaryPrime a) (auxIndex a) (auxPositive a) g = lab n at hg
    rw [← hg]
    rcases g with (⟨k,i⟩|⟨k,i⟩) | ⟨k,j⟩
    · exact congrArg (fun c : Columns (Aux a) => c.1 k i) hd
    · exact congrArg (fun c : Columns (Aux a) => c.2.1 k i) hd
    · exact congrArg (fun c : Columns (Aux a) => c.2.2 k j) hd
  exact (Finsupp.mapDomain_apply_of_injective (column_injective a) _ _).symm.trans zeroAt

/-- On a raw word the full zero profile already forces every written exponent
to be zero. This also applies after multiplication by either sign. -/
theorem zero_word (e : ℕ →₀ ℤ)
    (h : ∀ i, order (valuation a i) (word (UnivariateExtraction.generator (driver a).requirements) e) = 0) : e = 0 := by
  let W := generatorUnit (driver a)
  let w := e.prod (fun n z => W n ^ z)
  have hw : (w : RatFunc ℚ) = word (UnivariateExtraction.generator (driver a).requirements) e := by
    simp only [w,word,Finsupp.prod,Units.coe_prod,Units.val_zpow_eq_zpow_val]
    rfl
  have heq : signed a w = signed a 1 := by
    apply Profile.signedValues_injective
    funext i
    rw [signed_values,signed_values,Units.val_one,order_one,hw,h]
  have hsingle (n : ℕ) (_ : n ∈ e.support) (x : (RatFunc ℚ)ˣ) :
      signed a (x*W n) = (signed a x).translate (auxIndex a) (auxSign (auxPositive a))
        (stageColumns a (Finsupp.single n 1)) := by
    simpa [stageColumns,Finsupp.mapDomain.addMonoidHom] using
      generator_translates a (signed a) (signed_values a) n x
  have he := signed_word_translates (auxIndex a) (auxSign (auxPositive a)) W (stageColumns a)
    (signed a) e hsingle 1
  change signed a (1*w) = _ at he
  rw [one_mul,heq] at he
  exact stageColumns_injective_zero a e ((signed a 1).columns_zero_of_translate_eq _ _ _ he.symm)

/-- The only units of this concrete dyadic valuation intersection are the
two rational signs. -/
theorem sign_units (z : fullIntersection (valuation a)) (hz : IsUnit z) : z = 1 ∨ z = -1 := by
  let D := driver a
  let R := D.requirements
  have hzero : ∀ i, order (valuation a i) z.val = 0 :=
    (isUnit_iff_order_zero (valuation a) hz.ne_zero).mp hz
  have hhor (q : FreezingCalendar.Horizontal) (hq : HorizontalOrders.Retained (poles R) q) :
      HorizontalOrders.valuation q z.val = 1 := by
    obtain ⟨i,rfl⟩ := horizontal_covers a q hq
    apply (order_eq_zero_iff _ (show z.val ≠ 0 from fun h => hz.ne_zero (Subtype.ext h))).mp
    simpa [valuation_horizontal] using hzero (horizontalSite i)
  have hguard (p : PrimeIndex) : UnivariateExtraction.guardVal R p z.val = 1 := by
    let g := (guardPrime a).symm p
    have hv := hzero (guardSite g)
    rw [valuation_guard] at hv
    apply (order_eq_zero_iff _ (show z.val ≠ 0 from fun h => hz.ne_zero (Subtype.ext h))).mp
    simpa [guardVal,g] using hv
  have hG (p : PrimeIndex) (i : ℕ) : UnivariateExtraction.guardVal R p (UnivariateExtraction.generator R i) = 1 := by
    apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
    rw [← UnivariateExtraction.eval_permanent_guard]
    exact D.generator_guard_norm_one i p
  obtain ⟨e,he⟩ := UnivariateExtraction.signed_word_of_horizontal_units R hG z.val
    (fun h => hz.ne_zero (Subtype.ext h)) hhor hguard
  have hezero : e = 0 := by
    apply zero_word a
    intro i
    rcases he with h | h <;> simpa [h] using hzero i
  subst e
  simp [word] at he
  exact he.imp id Subtype.ext

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
