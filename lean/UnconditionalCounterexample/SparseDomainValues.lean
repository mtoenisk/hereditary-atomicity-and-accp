import UnconditionalCounterexample.SparsePrimaryDomain
import UnconditionalCounterexample.ConstructionRecovery

/-!
# Canonical original-domain values for a sparse primary family

The primary map is only injective, while every rational prime retains its
guard. Integral bounds follow directly from the actual defining intersection
valuations and are stated for the literal rational evaluation maps used by the
tensor conductors. All subring images use the canonical pole-algebra inclusion.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseDomainValues

open Polynomial SparsePrimaryDomain GuardSupport

noncomputable local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (S : Set ℚ[X]) (d : Places)

abbrev poleAlgebra := PoleAlgebra.generated S

def inclusion : domain S d →+* poleAlgebra S :=
  IntersectionDomain.inclusion (poleAlgebra S).toSubring (vertical d)

@[simp] theorem coe_inclusion (x : domain S d) :
    ((inclusion S d x : poleAlgebra S) : RatFunc ℚ) = (x : RatFunc ℚ) := rfl

theorem inclusion_injective : Function.Injective (inclusion S d) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : poleAlgebra S => (z : RatFunc ℚ)) h)

def coordinate : domain S d := ⟨RatFunc.X, SparsePrimaryDomain.X_mem S d⟩

@[simp] theorem coe_coordinate : (coordinate S d : RatFunc ℚ) = RatFunc.X := rfl

@[simp] theorem inclusion_coordinate :
    inclusion S d (coordinate S d) = algebraMap ℚ[X] (poleAlgebra S) X := rfl

def domainInPole : Subring (poleAlgebra S) :=
  (domain S d).comap (poleAlgebra S).val.toRingHom

theorem range_eq_domainInPole : (inclusion S d).range = domainInPole S d := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact z.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mapped_subring_le (T : Subring (domain S d)) :
    T.map (inclusion S d) ≤ domainInPole S d := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem primary_norm_eval_le_one (j : ℕ) (x : RatFunc ℚ) (hx : x ∈ domain S d) :
    ‖RatFunc.eval (algebraMap ℚ ℚ_[(d.primes j).val]) (d.primary j).val x‖ ≤ 1 := by
  have h := ((IntersectionDomain.mem_intersection _ _ _).mp hx).2 (.inl j)
  have hn := (EvaluationDVR.mem_valuationSubring (d.primes j).val
    (EvaluationDVR.evaluationHom (d.primes j).val (d.primary j).val (d.primary_trans j)) x).mp h
  have he : EvaluationDVR.evaluationHom (d.primes j).val (d.primary j).val
      (d.primary_trans j) x = RatFunc.eval (algebraMap ℚ ℚ_[(d.primes j).val]) (d.primary j).val x :=
    LocalEvaluation.evalAt_apply _ _ x
  rwa [he] at hn

theorem guard_norm_eval_le_one (p : PrimeIndex) (x : RatFunc ℚ) (hx : x ∈ domain S d) :
    ‖RatFunc.eval (algebraMap ℚ ℚ_[p.val]) (d.guard p).val x‖ ≤ 1 := by
  have h := ((IntersectionDomain.mem_intersection _ _ _).mp hx).2 (.inr p)
  have hn := (EvaluationDVR.mem_valuationSubring p.val (guardEvaluation d.guard d.guard_trans p) x).mp h
  have he : guardEvaluation d.guard d.guard_trans p x =
      RatFunc.eval (algebraMap ℚ ℚ_[p.val]) (d.guard p).val x := LocalEvaluation.evalAt_apply _ _ x
  rwa [he] at hn

theorem primary_norm_eval_le_one_inPole (j : ℕ) (x : domainInPole S d) :
    ‖RatFunc.eval (algebraMap ℚ ℚ_[(d.primes j).val]) (d.primary j).val
      ((x : poleAlgebra S) : RatFunc ℚ)‖ ≤ 1 :=
  primary_norm_eval_le_one S d j _ x.property

theorem guard_norm_eval_le_one_inPole (p : PrimeIndex) (x : domainInPole S d) :
    ‖RatFunc.eval (algebraMap ℚ ℚ_[p.val]) (d.guard p).val
      ((x : poleAlgebra S) : RatFunc ℚ)‖ ≤ 1 :=
  guard_norm_eval_le_one S d p _ x.property

theorem exists_nat_mul_mem (T : Subring (domain S d))
    (hT : RationalHull.hull (T.map (inclusion S d)) = ⊤) (x : domain S d) :
    ∃ n : ℕ, 0 < n ∧ (n : domain S d) * x ∈ T :=
  ConstructionRecovery.exists_nat_mul_mem_of_mapped_hull_eq_top
    (inclusion S d) (inclusion_injective S d) T hT x

theorem exists_nat_coordinate_mem (T : Subring (domain S d))
    (hT : RationalHull.hull (T.map (inclusion S d)) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ (n : domain S d) * coordinate S d ∈ T :=
  exists_nat_mul_mem S d T hT (coordinate S d)

end UnconditionalCounterexample.SparseDomainValues
