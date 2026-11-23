import UnconditionalCounterexample.Hierarchy.UnivariateInclusions
import UnconditionalCounterexample.Hierarchy.EvaluationStalks
import UnconditionalCounterexample.Hierarchy.OverringStalks
import UnconditionalCounterexample.Hierarchy.StrictClasses

/-!
# The two-chain and dyadic witnesses among almost Dedekind overrings

Both constructions use their actual permanent evaluation sites and the
canonical inclusion of integer-valued polynomials into the rational function
field. Their named elements witness the failures intrinsically.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open Variations Factorization StrictHierarchy

theorem univariate_isAlmostDedekind (R : Univariate.Requirements) : IsAlmostDedekindDomain (Univariate.domain R) := by
  let E := evaluationSet R
  let := evaluationRing_fractionRing E
  exact almostDedekind_overring (evaluationRing E) (Univariate.domain R) (evaluationRing_le_univariate R)
    (evaluationRing_isAlmostDedekind E (fun p ↦ (evaluationSet_finite R p).isCompact)
      (evaluationSet_nonempty R) (evaluationSet_transcendental R)) (univariate_not_isField R)

/-- Strong atomicity without weak ACCP, witnessed by the comaximal square starts. -/
theorem twoChain_overring :
    Witness (fun S ↦ IsWeakACCP S) (fun S ↦ IsStronglyAtomicDomain S) TwoChains.domain ∧
    IsFractionRing TwoChains.domain (RatFunc ℚ) ∧
    (TwoChains.parameter : RatFunc ℚ) = RatFunc.X ∧
    HasStrictChainAt (TwoChains.parameter^2) ∧ HasStrictChainAt ((1-TwoChains.parameter)^2) ∧
    IsCoprime (TwoChains.parameter^2) ((1-TwoChains.parameter)^2) := by
  obtain ⟨hX,hK,h₀,h₁,hc,hw,_⟩ := TwoChains.conclusion
  exact ⟨⟨⟨twoChain_intZ,univariate_isAlmostDedekind _,twoChain_stronglyAtomic⟩,hw⟩,hK,hX,h₀,h₁,hc⟩

/-- Atomicity without strong atomicity, witnessed by the dyadic pair's strictly extendible common divisors. -/
theorem dyadic_overring :
    Witness (fun S ↦ IsStronglyAtomicDomain S) (fun S ↦ IsAtomicDomain S) DyadicCounterexample.ring ∧
    IsFractionRing DyadicCounterexample.ring (RatFunc ℚ) ∧
    DyadicCounterexample.x ≠ 0 ∧ DyadicCounterexample.y ≠ 0 ∧
    ∀ d : DyadicCounterexample.ring, d ∣ DyadicCounterexample.x → d ∣ DyadicCounterexample.y →
      ∃ u : DyadicCounterexample.ring, ¬ IsUnit u ∧ d*u ∣ DyadicCounterexample.x ∧ d*u ∣ DyadicCounterexample.y := by
  obtain ⟨_,hx,hy,he,hn,_⟩ := DyadicCounterexample.counterexample
  exact ⟨⟨⟨dyadic_intZ,univariate_isAlmostDedekind _,dyadic_atomic⟩,hn⟩,Univariate.fractionRing _,hx,hy,he⟩

end UnconditionalCounterexample.Hierarchy
