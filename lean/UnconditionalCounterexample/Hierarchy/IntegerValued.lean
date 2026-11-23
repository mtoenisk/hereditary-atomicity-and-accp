import UnconditionalCounterexample.PairedDomain

/-!
# Integer-valued polynomials in the rational function field

Integer values at the ordinary integers imply integral values at every
p-adic integer, by continuity and density. The subring in the function field
uses the canonical embedding of rational polynomials.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open Polynomial

/-- Rational polynomials taking integer values on every integer. -/
def intZPolynomials : Subring ℚ[X] :=
  ⨅ z : ℤ, (Int.castRingHom ℚ).range.comap (evalRingHom (z : ℚ))

theorem mem_intZPolynomials_iff (f : ℚ[X]) :
    f ∈ intZPolynomials ↔ ∀ z : ℤ, ∃ n : ℤ, (n : ℚ) = f.eval (z : ℚ) := by
  exact Subring.mem_iInf

/-- The canonical image of Int(ℤ) in ℚ(t). -/
def intZInK : Subring (RatFunc ℚ) :=
  intZPolynomials.map (algebraMap ℚ[X] (RatFunc ℚ))

theorem mem_intZInK_iff (x : RatFunc ℚ) :
    x ∈ intZInK ↔ ∃ f : ℚ[X], f ∈ intZPolynomials ∧ algebraMap ℚ[X] (RatFunc ℚ) f = x :=
  Iff.rfl

theorem norm_eval₂_le_one_of_integerValued (p : ℕ) [Fact p.Prime]
    (f : ℚ[X]) (hf : f ∈ intZPolynomials) (a : ℤ_[p]) :
    ‖f.eval₂ (Rat.castHom ℚ_[p]) (a : ℚ_[p])‖ ≤ 1 := by
  let F (x : ℤ_[p]) : ℚ_[p] := f.eval₂ (Rat.castHom ℚ_[p]) (x : ℚ_[p])
  have hcont : Continuous F := (f.continuous_eval₂ _).comp continuous_subtype_val
  change ‖F a‖ ≤ 1
  refine PadicInt.denseRange_intCast.induction_on (p := fun x : ℤ_[p] => ‖F x‖ ≤ 1) a
    (isClosed_le hcont.norm continuous_const) ?_
  intro z
  obtain ⟨n, hn⟩ := (mem_intZPolynomials_iff f).mp hf z
  have he : F (z : ℤ_[p]) = (n : ℚ_[p]) := by
    change f.eval₂ (Rat.castHom ℚ_[p]) _ = _
    rw [PadicInt.coe_intCast, ← map_intCast (Rat.castHom ℚ_[p]) z, eval₂_hom, ← hn, map_intCast]
  change ‖F (z : ℤ_[p])‖ ≤ 1
  rw [he]
  exact_mod_cast (PadicInt.norm_le_one (n : ℤ_[p]))

theorem integerValued_eval_integral (p : ℕ) [Fact p.Prime] (f : ℚ[X]) (hf : f ∈ intZPolynomials)
    (a : ℤ_[p]) (ha : Transcendental ℚ a.val) :
    EvaluationDVR.evaluationValuation p a.val ha (algebraMap ℚ[X] (RatFunc ℚ) f) ≤ 1 := by
  apply (EvaluationDVR.mem_valuationSubring p (EvaluationDVR.evaluationHom p a.val ha) _).mpr
  change ‖LocalEvaluation.evalAt a.val ha (algebraMap ℚ[X] (RatFunc ℚ) f)‖ ≤ 1
  rw [LocalEvaluation.evalAt_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, map_one, div_one]
  change ‖f.eval₂ (algebraMap ℚ ℚ_[p]) a.val‖ ≤ 1
  rw [show algebraMap ℚ ℚ_[p] = Rat.castHom _ from Subsingleton.elim ..]
  exact norm_eval₂_le_one_of_integerValued p f hf a

theorem intZInK_le_pairedDomain (S : Set ℚ[X]) (d : PairedDomain.Places) :
    intZInK ≤ PairedDomain.domain S d := by
  rintro x ⟨f,hf,rfl⟩
  apply (IntersectionDomain.mem_intersection _ _ _).mpr
  refine ⟨PoleAlgebra.polynomial_mem S f, ?_⟩
  rintro (j | p)
  · exact integerValued_eval_integral _ f hf _ (d.primary_trans j)
  · exact integerValued_eval_integral _ f hf _ (d.guard_trans p)

end UnconditionalCounterexample.Hierarchy
