import UnconditionalCounterexample.SparseUnitSigns
import UnconditionalCounterexample.SparseDomainValues
import UnconditionalCounterexample.UnboundedWords

/-!
# Actual word extraction for sparse primary intersections

The complete profile and sign-unit results supply all inputs to the common
unbounded-factorization extraction theorem. Only elementary raw-polynomial and
actual generator-valuation data remain as construction inputs. All guard primes
are retained; no enumeration surjectivity or signed-word representation is assumed.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseExtraction
open Polynomial Filter RawWords SparseProfiles DiscreteOrders GuardSupport
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (F : ℕ → ℚ[X]) (hF : ∀ i, (F i).Monic ∧ Irreducible (F i))
  (hinj : Function.Injective F) (hconst : ∀ i, (F i).coeff 0 ≠ 0)
  (E : ℕ → ℕ) (d : SparsePrimaryDomain.Places) (hG : GeneratorProfiles F E d)
  (hguard : ∀ x : RatFunc ℚ, x ≠ 0 →
    {p : PrimeIndex | SparsePrimaryDomain.vertical d (.inr p) x ≠ 1}.Finite)

/-- Literal inclusion of the sparse intersection into its rational pole algebra. -/
abbrev inclusion : SparsePrimaryDomain.domain (Set.range F) d →+*
    PoleAlgebra.generated (Set.range F) :=
  SparseDomainValues.inclusion (Set.range F) d

@[simp] theorem coe_inclusion (x : SparsePrimaryDomain.domain (Set.range F) d) :
    ((inclusion F d x : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) = x := rfl

theorem inclusion_injective : Function.Injective (inclusion F d) :=
  SparseDomainValues.inclusion_injective (Set.range F) d

local notation "D" => SparsePrimaryDomain.domain (Set.range F) d

theorem primary_value_eq_exp_profile (z : D) (hz : z ≠ 0) (j : ℕ) :
    SparsePrimaryDomain.vertical d (.inl j) (z : RatFunc ℚ) =
      WithZero.exp (-((profiles F hF hinj hconst E d hG hguard).value (.primary j) z : ℤ)) := by
  change valuations (Set.range F) d (.primary j) (z : RatFunc ℚ) = _
  rw [value_eq_exp_neg_order _ (fun h => hz (Subtype.ext h)),
    profiles_value_cast F hF hinj hconst E d hG hguard _ z hz]

theorem guard_value_eq_one_of_outside_zero (z : D) (hz : z ≠ 0)
    (ho : ∀ i, (profiles F hF hinj hconst E d hG hguard).value (.outside i) z = 0) (p : PrimeIndex) :
    @Padic.mulValuation p.val ⟨p.property⟩
      (guardEvaluation d.guard d.guard_trans p (z : RatFunc ℚ)) = 1 := by
  have hzero : order (valuations (Set.range F) d (.outside (.inl p))) (z : RatFunc ℚ) = 0 := by
    rw [← profiles_value_cast F hF hinj hconst E d hG hguard _ z hz, ho]
    rfl
  exact (order_eq_zero_iff _ (fun h => hz (Subtype.ext h))).mp hzero

theorem inverse_pole_mem_of_pure (z : D) (hz : z ≠ 0)
    (hl : (profiles F hF hinj hconst E d hG hguard).value .limit z = 0) (ho : ∀ i, (profiles F hF hinj hconst E d hG hguard).value (.outside i) z = 0) :
    (z : RatFunc ℚ)⁻¹ ∈ PoleAlgebra.generated (Set.range F) := by
  have hn : ∀ q ∈ Set.range F, q ≠ 0 := by
    rintro q ⟨i, rfl⟩
    exact (hF i).2.ne_zero
  have hli : order (valuations (Set.range F) d .limit) (z : RatFunc ℚ) = 0 := by
    rw [← profiles_value_cast F hF hinj hconst E d hG hguard _ z hz, hl]
    rfl
  have hoi : ∀ i, order (valuations (Set.range F) d (.outside i)) (z : RatFunc ℚ) = 0 := by
    intro i
    rw [← profiles_value_cast F hF hinj hconst E d hG hguard _ z hz, ho]
    rfl
  exact (pole_unit_of_zero_outside _ d hn z (fun h => hz (Subtype.ext h)) hli hoi).2

include hF hinj hconst hG hguard in
/-- Uniformly bounded concrete words escaping every finite stage, obtained from
intrinsically unbounded factorizations inside the original subring. -/
theorem exists_listed_sequence_of_unbounded
    (T : Subring D) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ r : ℕ, 0 < r ∧ ∃ y : ℕ → T.map (inclusion F d), ∃ stage : ℕ → ℕ,
      ∃ w : ∀ i, StageWord (stage i) (stage i + 1),
      (∀ i, i < stage i) ∧ Tendsto stage atTop atTop ∧
      (∀ i, (w i).latestExponent ≤ 2 * r) ∧
      (∀ i j, |(w i).oldExponent j| ≤ (2 * r : ℕ)) ∧ ∀ i,
        ((y i : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) =
          generators F E (stage i) ^ (w i).latestExponent *
          (∏ j ∈ Finset.range (stage i), generators F E j ^ (w i).oldExponent j) := by
  apply UnboundedWords.exists_listed_sequence_of_unbounded_map F hF hinj E
    (fun j => SparsePrimaryDomain.vertical d (.inl j))
    (guardEvaluation d.guard d.guard_trans) hG.b hG.q hG.guard
    (inclusion F d) (inclusion_injective F d) (profiles F hF hinj hconst E d hG hguard)
    (primary_value_eq_exp_profile F hF hinj hconst E d hG hguard)
    (guard_value_eq_one_of_outside_zero F hF hinj hconst E d hG hguard)
    (inverse_pole_mem_of_pure F hF hinj hconst E d hG hguard)
    T (SparseUnitSigns.actual_subring_reflects_units F hF hinj hconst E d hG T)
    x hx hunbounded

end UnconditionalCounterexample.SparseExtraction
