import UnconditionalCounterexample.Variations.DyadicReservedNorm
import UnconditionalCounterexample.Variations.DyadicDispatchReserve
import UnconditionalCounterexample.Variations.DyadicConcreteDomain
import UnconditionalCounterexample.Variations.DyadicSplitValuesGlobal

/-!
# Actual factors obtained from a calibrated split instruction

A verified finite instruction yields the two field factors in the actual
domain, with the two zero endpoint orders and the two coprime congruences
required for descent to the original conductor-containing subring.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open GuardSupport PrimaryChoices Univariate DyadicDeviations FieldGeneration DiscreteOrders MixedStageSelection

variable (a : Policy)

theorem coprime_factors_of_installed
    (signed : (RatFunc ℚ)ˣ → Profile (Aux a) (Lone a) (Horiz a))
    (hval : ∀ y i, (signed y).signedValues i = order (valuation a i) y.val)
    (r : ℕ) (I : SplitInstruction) (hi : (openingData (planner a) r).instruction = some I)
    (hchannel : I.channel = true)
    (x : domain (driver a).requirements) (hx : (x : RatFunc ℚ) ≠ 0) (helement : I.task.element = x)
    (u v : Profile (Aux a) (Lone a) (Horiz a))
    (split : SplitAt (auxIndex a) (auxSign (auxPositive a)) (signed (Units.mk0 _ hx)) u v I.index)
    (ht : (signed I.coarse).translate (auxIndex a) (auxSign (auxPositive a))
      (columnsOfRaw (auxiliaryPrime a) (auxIndex a) (auxPositive a) I.coefficients) = u)
    (hs : I.coefficients.support ⊆ (Finset.range ((driver a).opening (r+1)-1+1)).image
      (fun j => ((driver a).actualRequest j).column))
    (hfibre : ∀ p : PrimeIndex, p.val ∣ I.task.modulus →
      I.first p.val = ((driver a).permanentRole p).elim true (fun q => !q.channel) ∧
      ∀ c k j, (driver a).permanentRole p = some (.regular c k j) → j < I.index) :
    ∃ (U V : domain (driver a).requirements) (d e : ℕ), x = U*V ∧
      order (valuation a (.centre true)) (U : RatFunc ℚ) = 0 ∧
      order (valuation a (.centre false)) (V : RatFunc ℚ) = 0 ∧
      I.task.modulus = d*e ∧ d.Coprime e ∧ (d : domain (driver a).requirements) ∣ U-1 ∧
        (e : domain (driver a).requirements) ∣ V-1 := by
  let D := driver a
  let n := D.opening (r+1)-1
  let P := (chain D.requirements).approx n
  let X : (RatFunc ℚ)ˣ := Units.mk0 _ hx
  let U₀ := I.prefix (D.state n) P
  let W := U₀ * generatorUnit D n
  obtain ⟨_,hr,hh,hc⟩ := last_executes (planner a) r I hi
  have hlast : (D.actualRequest n).column = .balanced true I.index := hchannel ▸ hc
  have hw : signed W = u := by
    apply D.instruction_profile (auxiliaryPrime a) (auxIndex a) (auxPositive a) (auxSign (auxPositive a))
      signed I n u ht hs (column_injective a).injOn hc
    exact fun j _ _ => generator_translates a signed hval j
  obtain ⟨hv,hmU,hmV⟩ := split.field_factors _ _ (valuation a) signed hval X W rfl hw
  rw [← domain_eq_intersection] at hmU hmV
  let U : domain D.requirements := ⟨W.val,hmU⟩
  let V : domain D.requirements := ⟨(X/W).val,hmV⟩
  have huv : x = U*V := by
    apply Subtype.ext
    change X.val = W.val * (X/W).val
    rw [Units.val_div_eq_div_val]
    exact (mul_div_cancel₀ _ W.ne_zero).symm
  have hnorm (p : PrimeIndex) (hp : p.val ∣ I.task.modulus) (b : Bool)
      (hb : Active (permanentSite D.requirements p).paired b) :
      ‖(permanentSite D.requirements p).evaluate b hb U₀.val‖ =
        if I.first p.val then ‖(permanentSite D.requirements p).evaluate b hb (x : RatFunc ℚ)‖ else 1 :=
    prefix_target_norm a signed hval I n I.index X u v split ht hs hlast p b hb (hfibre p hp).2 (hfibre p hp).1
  have hn : I.task.element ≠ 0 := helement ▸ hx
  have hbranch (j : (selection D.requirements n).batch.indices) (hj : (primes j.val).val ∣ I.task.modulus)
      (b : Bool) : ‖DyadicSplit.branchValue (selectionSite D.requirements n j) b U₀.val‖ =
        if I.first (primes j.val).val then
          ‖DyadicSplit.branchValue (selectionSite D.requirements n j) b I.task.element‖ else 1 := by
    rw [selectionSite_eq,helement]
    by_cases hb : Active (permanentSite D.requirements (primes j.val)).paired b
    · simp only [DyadicSplit.branchValue,dite_eq_left hb]
      exact hnorm (primes j.val) hj b hb
    · cases I.first (primes j.val).val <;> simp [DyadicSplit.branchValue,hb]
  have htargets := last_targets (planner a) r I hi hn
    (fun j hj => reserved_primary_zero a n I.index hlast j (hfibre _ hj).2)
    hbranch
  simp only [helement] at htargets
  obtain ⟨d,e,hde,hcop,hU,hV⟩ := DyadicSplit.selected_coprime_returns D.requirements n I.task.modulus
    I.task.positive I.first x hx U₀.val U₀.ne_zero _ htargets
    (D.reserved_primes_processed n I.task hr hh) hnorm U V rfl (Units.val_div_eq_div_val X W)
  refine ⟨U,V,d,e,huv,?_,?_,hde,hcop,hU,hV⟩
  · change order (valuation a (.centre true)) W.val = 0
    rw [← hval,hw]
    exact split.heights.2.1
  · change order (valuation a (.centre false)) (X/W).val = 0
    rw [← hval,hv]
    exact split.heights.2.2.1

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
