import UnconditionalCounterexample.IntersectionDomain
import UnconditionalCounterexample.PoleAlgebra
import UnconditionalCounterexample.GuardSupport
import UnconditionalCounterexample.PrimaryStabilization

/-!
# The intersection attached to paired rational evaluations

The constructor supplies raw polynomials with nonzero constants, an ordered
family of primary arguments and a guard for each prime. A pole algebra element
has nonnegative order at zero, and hence is integral at all late primaries.
Together with finite guard support this proves the integer localization.
-/

noncomputable section
namespace UnconditionalCounterexample.PairedDomain
open Polynomial WithZero Filter GuardSupport

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Arguments used in the vertical intersection. The schedule imposes further
conditions at the first primary and on the residues of the guards. -/
structure Places where
  primes : ℕ ≃ PrimeIndex
  primary (i : ℕ) : ℤ_[(primes i).val]
  primary_trans (i : ℕ) : Transcendental ℚ (primary i).val
  primary_late (i : ℕ) : 0 < i → (primary i).val.valuation = 1
  guard (p : PrimeIndex) : ℤ_[p.val]
  guard_trans (p : PrimeIndex) : Transcendental ℚ (guard p).val

def vertical (d : Places) : ℕ ⊕ PrimeIndex → Valuation (RatFunc ℚ) ℤᵐ⁰
  | .inl i => EvaluationDVR.evaluationValuation (d.primes i).val (d.primary i).val (d.primary_trans i)
  | .inr p => EvaluationDVR.valuation p.val (guardEvaluation d.guard d.guard_trans p)

abbrev domain (S : Set ℚ[X]) (d : Places) : Subring (RatFunc ℚ) :=
  IntersectionDomain.intersection (PoleAlgebra.generated S).toSubring (vertical d)

theorem tOrder_nonneg_of_mem {S : Set ℚ[X]} (hS : ∀ q ∈ S, constantCoeff q ≠ 0)
    {f : RatFunc ℚ} (hf : f ∈ PoleAlgebra.generated S) : 0 ≤ PrimaryStabilization.tOrder f := by
  have hn : ∀ q ∈ S, q ≠ 0 := fun q hq hz => hS q hq (by simp [hz])
  obtain ⟨s, hs, r, hr⟩ := (PoleAlgebra.mem_generated_iff_denom_dvd S hn f).mp hf
  have hsc : constantCoeff s ≠ 0 := by
    clear hr
    induction hs using Submonoid.closure_induction with
    | mem q hq => exact hS q hq
    | one => simp
    | mul q r _ _ hq hr => simpa only [map_mul] using mul_ne_zero hq hr
  have hd : constantCoeff f.denom ≠ 0 := by
    intro h
    exact hsc (by rw [hr, map_mul, h, zero_mul])
  simp [PrimaryStabilization.tOrder, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hd]

private theorem integral_value_le_one {p : ℕ} [Fact p.Prime] (z : ℤ_[p]) :
    Padic.mulValuation (z : ℚ_[p]) ≤ 1 := by
  have hz : ‖(z : ℚ_[p])‖ ≤ 1 := z.property
  apply le_of_not_gt
  intro h
  apply (not_lt_of_ge hz)
  simpa only [norm_one] using (Padic.norm_lt_norm_iff_mulValuation_lt
    (x := (1 : ℚ_[p])) (y := (z : ℚ_[p]))).mpr (by simpa only [map_one] using h)

theorem X_mem (S : Set ℚ[X]) (d : Places) : RatFunc.X ∈ domain S d := by
  apply IntersectionDomain.rational_X_mem _ _ (PoleAlgebra.X_mem S)
  rintro (i | p)
  · change EvaluationDVR.evaluationValuation _ _ _ RatFunc.X ≤ 1
    rw [EvaluationDVR.evaluationValuation_X]
    exact integral_value_le_one _
  · change EvaluationDVR.evaluationValuation _ _ _ RatFunc.X ≤ 1
    rw [EvaluationDVR.evaluationValuation_X]
    exact integral_value_le_one _

theorem fractionRing (S : Set ℚ[X]) (d : Places) :
    IsFractionRing (domain S d) (RatFunc ℚ) :=
  RationalFunctionSubring.isFractionRing_of_X_mem _ (X_mem S d)

/-- One guard at every prime forces the rational constants in the intersection
to be precisely the integers. No schedule estimates enter this argument. -/
theorem rational_mem_iff_integer (S : Set ℚ[X]) (d : Places) (q : ℚ) :
    (q : RatFunc ℚ) ∈ domain S d ↔ ∃ z : ℤ, (z : ℚ) = q := by
  constructor
  · intro hq
    refine ⟨q.num, (Rat.den_eq_one_iff q).mp ?_⟩
    by_contra hden
    obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hden
    let j : PrimeIndex := ⟨p, hp⟩
    let : Fact p.Prime := ⟨hp⟩
    have h := ((IntersectionDomain.mem_intersection _ _ _).mp hq).2 (.inr j)
    change Padic.mulValuation (guardEvaluation d.guard d.guard_trans j (q : RatFunc ℚ)) ≤ 1 at h
    rw [map_ratCast] at h
    have heq := congrArg (fun v : Valuation ℚ ℤᵐ⁰ => v q)
      (Padic.comap_mulValuation_eq_padicValuation (p := j.val))
    exact (Rat.padicValuation_le_one_iff (p := j.val)).mp (heq ▸ h) hdvd
  · rintro ⟨z, rfl⟩
    simp

theorem finite_nonintegral_of_guard_support (d : Places) {S : Set ℚ[X]} (hS : ∀ q ∈ S, constantCoeff q ≠ 0)
    (guardSupport : ∀ x : RatFunc ℚ, x ≠ 0 →
      {p : PrimeIndex | vertical d (.inr p) x ≠ 1}.Finite)
    (f : RatFunc ℚ) (hf : f ∈ PoleAlgebra.generated S) : {v | 1 < vertical d v f}.Finite := by
  by_cases hz : f = 0
  · simp [hz]
  have hpri := PrimaryStabilization.eventually_evaluationValuation_eq_exp_neg_tOrder
    (fun n => (d.primes n).val) (Subtype.val_injective.comp d.primes.injective)
    (fun n => (d.primary n).val) d.primary_trans d.primary_late f hz
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpri
  have hp : Set.Finite {i : ℕ | 1 < vertical d (.inl i) f} := by
    apply (Finset.range N).finite_toSet.subset
    intro i hi
    by_contra hnot
    have hiN : N ≤ i := by simpa using hnot
    change 1 < EvaluationDVR.evaluationValuation _ _ _ f at hi
    rw [hN i hiN] at hi
    exact (not_lt_of_ge (exp_le_one_iff.mpr (neg_nonpos.mpr (tOrder_nonneg_of_mem hS hf)))) hi
  have hg := guardSupport f hz
  apply ((hp.image (Sum.inl (β := PrimeIndex))).union (hg.image (Sum.inr (α := ℕ)))).subset
  rintro (i | p) hi
  · exact Or.inl ⟨i, hi, rfl⟩
  · exact Or.inr ⟨p, ne_of_gt hi, rfl⟩

/-- Inverting the nonzero integers in the intersection gives the pole algebra. -/
theorem integerLocalization_of_guard_support (d : Places) {S : Set ℚ[X]}
    (hS : ∀ q ∈ S, constantCoeff q ≠ 0)
    (guardSupport : ∀ x : RatFunc ℚ, x ≠ 0 →
      {p : PrimeIndex | vertical d (.inr p) x ≠ 1}.Finite) :
    IsLocalization (IntersectionDomain.integerDenominators (domain S d)) (PoleAlgebra.generated S) := by
  apply IntersectionDomain.integer_isLocalization _ _ (Sum.elim (fun n => (d.primes n).val) Subtype.val)
  · rintro (i | p)
    · exact (d.primes i).property.pos
    · exact p.property.pos
  · rintro (i | p)
    · exact EvaluationDVR.valuation_prime _ _
    · exact EvaluationDVR.valuation_prime _ _
  · exact finite_nonintegral_of_guard_support d hS guardSupport

variable (d : Places) (stage : PrimeIndex → ℕ) (hstage : ∀ n, {p | stage p ≤ n}.Finite)
  (havoid : ∀ p j, j < stage p →
    (integerPolynomialEnumeration j).val.eval₂ (Int.castRingHom (ZMod p.val))
      (PadicInt.toZMod (d.guard p)) ≠ 0)

include hstage havoid in
/-- Specialization for guards avoiding the integer-polynomial enumeration. -/
theorem integerLocalization {S : Set ℚ[X]} (hS : ∀ q ∈ S, constantCoeff q ≠ 0) :
    IsLocalization (IntersectionDomain.integerDenominators (domain S d)) (PoleAlgebra.generated S) :=
  integerLocalization_of_guard_support d hS
    (ratFunc_guardSupport_finite integerPolynomialEnumeration integerPolynomialEnumeration_surjective
      stage hstage d.guard havoid d.guard_trans)

end UnconditionalCounterexample.PairedDomain
