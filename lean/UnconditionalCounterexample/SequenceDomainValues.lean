import UnconditionalCounterexample.SequenceLocalTransfer
import UnconditionalCounterexample.ReturnCongruences

/-!
# Original domain values inside the pole algebra

The actual intersection domain has integral canonical rational evaluations at
both permanent branches of its own sequence. This follows from the defining
valuation inequalities, with the evaluation embedding identified with the
ordinary numerator/denominator formula. Viewing the domain inside its pole
algebra preserves those exact bounds; every actual unital subring maps into it
under the canonical inclusion.
-/

noncomputable section
namespace UnconditionalCounterexample.SequenceDomainValues

open Polynomial StageRecursion PrimaryChoices SequenceLocalTransfer

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable {R : Requirements}

/-- The actual intersection ring attached to the selected sequence. -/
abbrev actualDomain (seq : Sequence R) : Subring (RatFunc ℚ) :=
  PairedDomain.domain (Set.range seq.chain.raw) seq.chain.guardChain.places

/-- The same actual intersection, viewed inside its pole algebra. -/
def domainInPole (seq : Sequence R) :
    Subring (PoleAlgebra.generated (Set.range seq.chain.raw)) :=
  (actualDomain seq).comap (PoleAlgebra.generated (Set.range seq.chain.raw)).val.toRingHom

theorem evaluationHom_eq_eval (p : ℕ) [Fact p.Prime] (a : ℚ_[p])
    (ha : Transcendental ℚ a) (x : RatFunc ℚ) :
    EvaluationDVR.evaluationHom p a ha x = RatFunc.eval (algebraMap ℚ ℚ_[p]) a x :=
  LocalEvaluation.evalAt_apply a ha x

theorem evaluationBranch_eq_eval (seq : Sequence R) (j : ℕ) (b : Bool) (x : RatFunc ℚ) :
    PairedDomain.evaluationBranch seq.chain.guardChain.places j b x =
      RatFunc.eval (algebraMap ℚ ℚ_[(primes j).val]) (branch seq j b) x := by
  cases b
  · exact evaluationHom_eq_eval _ _ _ x
  · exact evaluationHom_eq_eval _ _ _ x

theorem norm_eval_le_one (seq : Sequence R) (j : ℕ) (b : Bool)
    (x : RatFunc ℚ) (hx : x ∈ actualDomain seq) :
    ‖RatFunc.eval (algebraMap ℚ ℚ_[(primes j).val]) (branch seq j b) x‖ ≤ 1 := by
  have h := ((PairedDomain.mem_domain_iff_branches seq.chain.guardChain.places
    (Set.range seq.chain.raw) x).mp hx).2 j b
  rw [evaluationBranch_eq_eval] at h
  exact (PadicInt.mem_subring_iff _).mp h

/-- Original-domain values are bounded at the exact permanent arguments used
by the actual tensor-conductor application. -/
theorem norm_eval_le_one_inPole (seq : Sequence R) (j : ℕ) (b : Bool)
    (d : domainInPole seq) :
    ‖RatFunc.eval (algebraMap ℚ ℚ_[(primes j).val]) (branch seq j b)
      ((d : PoleAlgebra.generated (Set.range seq.chain.raw)) : RatFunc ℚ)‖ ≤ 1 :=
  norm_eval_le_one seq j b _ d.property

/-- Every unital subring of the actual domain has this literal image in B. -/
def subringInPole (seq : Sequence R) (T : Subring (actualDomain seq)) :
    Subring (PoleAlgebra.generated (Set.range seq.chain.raw)) :=
  T.map (algebraMap (actualDomain seq) (PoleAlgebra.generated (Set.range seq.chain.raw)))

@[simp] theorem coe_algebraMap (seq : Sequence R) (d : actualDomain seq) :
    ((algebraMap (actualDomain seq) (PoleAlgebra.generated (Set.range seq.chain.raw)) d :
      PoleAlgebra.generated (Set.range seq.chain.raw)) : RatFunc ℚ) = d := rfl

theorem algebraMap_injective (seq : Sequence R) :
    Function.Injective (algebraMap (actualDomain seq) (PoleAlgebra.generated (Set.range seq.chain.raw))) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : PoleAlgebra.generated (Set.range seq.chain.raw) => (z : RatFunc ℚ)) h

theorem subringInPole_le (seq : Sequence R) (T : Subring (actualDomain seq)) :
    subringInPole seq T ≤ domainInPole seq := by
  rintro _ ⟨x, _, rfl⟩
  change ((algebraMap (actualDomain seq) (PoleAlgebra.generated (Set.range seq.chain.raw)) x :
    PoleAlgebra.generated (Set.range seq.chain.raw)) : RatFunc ℚ) ∈ actualDomain seq
  exact x.property

end UnconditionalCounterexample.SequenceDomainValues
