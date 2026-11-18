import UnconditionalCounterexample.HorizontalPrimes

/-!
# Horizontal valuation rings as actual stalks

For every retained monic irreducible, localization of the pole algebra at
its actual positive-valuation center is its horizontal valuation ring.
The map is the literal inclusion into the rational-function field. The
canonical reduced denominator is outside the center whenever the fraction
is integral, providing the exact localization witness.
-/

noncomputable section
namespace UnconditionalCounterexample.HorizontalStalks

open Polynomial PrincipalProfiles HorizontalOrders HorizontalPrimes
open scoped WithZero

variable {k : Type*} [Field k] (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (p : MonicIrreducible k) (hp : Retained S p)

/-- The actual inclusion determines the pole-algebra structure on the horizontal ring. -/
@[instance_reducible] def valuationAlgebra : Algebra (PoleAlgebra.generated S) (valuation p).valuationSubring :=
  (valuationInclusion S hS p hp).toAlgebra

omit S hS hp in
theorem reduced_denom_not_mem_point (x : RatFunc k) (hx : valuation p x ≤ 1) :
    x.denom ∉ (point p).asIdeal := by
  have hcop : x.denom ∈ (point p).asIdeal → x.num ∉ (point p).asIdeal := by
    intro hd hn
    exact p.property.2.not_isUnit (x.isCoprime_num_denom.isUnit_of_dvd'
      (Ideal.mem_span_singleton.mp hn) (Ideal.mem_span_singleton.mp hd))
  apply ((point p).valuation_div_le_one_iff (RatFunc k) x.num x.denom_ne_zero hcop).mp
  rw [RatFunc.num_div_denom]
  exact hx

/-- Localization at the actual horizontal center is the actual valuation ring. -/
theorem isLocalization_center :
    let _ := valuationAlgebra S hS p hp
    IsLocalization (center S hS p hp).primeCompl (valuation p).valuationSubring := by
  let := valuationAlgebra S hS p hp
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro d
    rw [← not_not (a := IsUnit _), ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    change valuationInclusion S hS p hp d.val ∉
      IsLocalRing.maximalIdeal (valuation p).valuationSubring
    exact d.property
  · intro z
    let a : PoleAlgebra.generated S := algebraMap k[X] (PoleAlgebra.generated S) (z : RatFunc k).num
    let b : PoleAlgebra.generated S := algebraMap k[X] (PoleAlgebra.generated S) (z : RatFunc k).denom
    have hb : b ∉ center S hS p hp := by
      intro hb
      have hmem : (z : RatFunc k).denom ∈
          (center S hS p hp).comap (algebraMap k[X] (PoleAlgebra.generated S)) := hb
      rw [center_comap] at hmem
      exact reduced_denom_not_mem_point p z z.property hmem
    refine ⟨(a, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    change (z : RatFunc k) * algebraMap k[X] (RatFunc k) (z : RatFunc k).denom =
      algebraMap k[X] (RatFunc k) (z : RatFunc k).num
    exact (eq_div_iff (RatFunc.algebraMap_ne_zero (z : RatFunc k).denom_ne_zero)).mp
      (RatFunc.num_div_denom (z : RatFunc k)).symm
  · intro x y hxy
    refine ⟨1, ?_⟩
    simpa only [Submonoid.coe_one, one_mul] using
      (Subtype.ext (congrArg (fun z : (valuation p).valuationSubring => (z : RatFunc k)) hxy) : x = y)

/-- The algebra map is literally the existing inclusion in the rational-function field. -/
@[simp] theorem coe_algebraMap (x : PoleAlgebra.generated S) :
    let _ := valuationAlgebra S hS p hp
    ((algebraMap (PoleAlgebra.generated S) (valuation p).valuationSubring x) : RatFunc k) = x := rfl

/-- The canonical stalk equivalence respects the original pole-algebra inclusion. -/
def stalkEquiv :
    let _ := valuationAlgebra S hS p hp
    Localization.AtPrime (center S hS p hp) ≃ₐ[PoleAlgebra.generated S]
      (valuation p).valuationSubring := by
  let := valuationAlgebra S hS p hp
  let := isLocalization_center S hS p hp
  exact IsLocalization.algEquiv (center S hS p hp).primeCompl
    (Localization.AtPrime (center S hS p hp)) (valuation p).valuationSubring

@[simp] theorem stalkEquiv_algebraMap (x : PoleAlgebra.generated S) :
    let _ := valuationAlgebra S hS p hp
    ((stalkEquiv S hS p hp (algebraMap (PoleAlgebra.generated S)
      (Localization.AtPrime (center S hS p hp)) x)) : RatFunc k) = x := by
  let := valuationAlgebra S hS p hp
  rw [AlgEquiv.commutes]
  rfl

end UnconditionalCounterexample.HorizontalStalks
