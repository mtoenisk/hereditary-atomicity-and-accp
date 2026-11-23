import UnconditionalCounterexample.Variations.UnivariateRecovery

/-!
# The finite evaluation fibres of the univariate construction

The permanent site over each rational prime contains its guard and possibly
one primary. Those exact integral p-adic arguments define the polynomial
evaluation subring contained in the selected domain.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open Polynomial GuardSupport Variations Univariate UnivariateConductor

variable (R : Univariate.Requirements)

def evaluationSet (p : PrimeIndex) : Set ℤ_[p.val] :=
  Point.value '' (permanentSite R p).fibre.points

theorem evaluationSet_finite (p : PrimeIndex) : (evaluationSet R p).Finite := by
  apply Set.Finite.image
  cases (permanentSite R p).fibre <;> simp [Fibre.points]

theorem evaluationSet_nonempty (p : PrimeIndex) : (evaluationSet R p).Nonempty := by
  apply Set.Nonempty.image
  cases (permanentSite R p).fibre <;> simp [Fibre.points]

theorem evaluationSet_transcendental (p : PrimeIndex) (a : ℤ_[p.val]) (ha : a ∈ evaluationSet R p) :
    Transcendental ℚ a.val := by
  obtain ⟨a,_,rfl⟩ := ha
  exact a.transcendental

theorem polynomial_mem_univariate (f : ℚ[X])
    (hf : ∀ p (a : ℤ_[p.val]), a ∈ evaluationSet R p → ‖f.eval₂ (Rat.castHom ℚ_[p.val]) a.val‖ ≤ 1) :
    algebraMap ℚ[X] (RatFunc ℚ) f ∈ Univariate.domain R := by
  apply (Univariate.mem_domain_iff _ _).mpr
  refine ⟨PoleAlgebra.polynomial_mem _ _,fun p a ha ↦ ?_⟩
  have h := hf p a.value ⟨a,ha,rfl⟩
  change ‖LocalEvaluation.evalAt a.value.val a.transcendental (algebraMap _ _ f)‖ ≤ 1
  rw [LocalEvaluation.evalAt_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, map_one, div_one]
  change ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) a.value.val‖ ≤ 1
  rwa [show algebraMap ℚ ℚ_[p.val] = Rat.castHom _ from Subsingleton.elim ..]

theorem inverse_prime_not_mem (p : PrimeIndex) : (p.val : RatFunc ℚ)⁻¹ ∉ Univariate.domain R := by
  intro h
  obtain ⟨a,ha⟩ : (permanentSite R p).fibre.points.Nonempty := by
    cases (permanentSite R p).fibre <;> simp [Fibre.points]
  have he := ((Univariate.mem_domain_iff R _).mp h).2 p a ha
  change ‖LocalEvaluation.evalAt a.value.val a.transcendental ((p.val : RatFunc ℚ)⁻¹)‖ ≤ 1 at he
  rw [map_inv₀,map_natCast,norm_inv,inv_le_one₀ (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr p.property.ne_zero))] at he
  exact Padic.norm_p_lt_one.not_ge he

theorem univariate_not_isField : ¬ IsField (Univariate.domain R) := by
  intro h
  let p : PrimeIndex := ⟨2,Nat.prime_two⟩
  have hp : (p.val : Univariate.domain R) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  obtain ⟨y,hy⟩ := h.mul_inv_cancel hp
  have he : (p.val : RatFunc ℚ) * y = 1 := congrArg (Univariate.domain R).subtype hy
  exact inverse_prime_not_mem R p ((eq_inv_of_mul_eq_one_right he) ▸ y.property)

end UnconditionalCounterexample.Hierarchy
