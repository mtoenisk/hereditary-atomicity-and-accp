import UnconditionalCounterexample.PairedDomain
import UnconditionalCounterexample.SelectedPrimes
import UnconditionalCounterexample.PairedSpectrum
import UnconditionalCounterexample.IntersectionDomain
import UnconditionalCounterexample.PoleAlgebra
import UnconditionalCounterexample.GuardSupport
import UnconditionalCounterexample.PrimaryStabilization

/-!
# The intersection with primaries over an arbitrary infinite prime set

This is the domain interface for manuscript §8.2. The primary-prime map is
only injective; guards are retained over every rational prime. `ofSelected`
uses the increasing enumeration of an actual infinite set and the proved
transcendental primary choices, with first value two and later value one.

The actual intersection contains X, has fraction field ℚ(t), and has exactly
the integers as rational constants. Finite guard support gives its actual
integer localization. At an omitted primary prime, the rational prime itself
is a value-one singleton isolator. The actual guard residue map is surjective
and has kernel exactly pD (`guardResidue_ker_unpaired`), not just its radical.

No compatible raw-polynomial/guard schedule, varying-prime family existence,
or hereditary atomicity conclusion is asserted here. Those require the
separate mixed one-point/paired construction and downstream assembly.
-/

noncomputable section
namespace UnconditionalCounterexample.SparsePrimaryDomain
open Polynomial WithZero Filter GuardSupport

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Arguments used in the vertical intersection. The schedule imposes further
conditions at the first primary and on the residues of the guards. -/
structure Places where
  primes : ℕ ↪ PrimeIndex
  primary (i : ℕ) : ℤ_[(primes i).val]
  primary_trans (i : ℕ) : Transcendental ℚ (primary i).val
  primary_late (i : ℕ) : 0 < i → (primary i).val.valuation = 1
  guard (p : PrimeIndex) : ℤ_[p.val]
  guard_trans (p : PrimeIndex) : Transcendental ℚ (guard p).val

/-- The increasing enumeration of an infinite selected set supplies precisely
its retained primaries; every rational prime still receives the given guard. -/
def ofSelected (S : Set PrimeIndex) (hS : S.Infinite)
    (guard : ∀ p : PrimeIndex, ℤ_[p.val])
    (hguard : ∀ p, Transcendental ℚ (guard p).val) : Places where
  primes := ⟨SelectedPrimes.primes S hS, SelectedPrimes.primes_injective S hS⟩
  primary := SelectedPrimes.primary (SelectedPrimes.primes S hS)
  primary_trans := SelectedPrimes.primary_transcendental (SelectedPrimes.primes S hS)
  primary_late := SelectedPrimes.primary_late (SelectedPrimes.primes S hS)
  guard := guard
  guard_trans := hguard

@[simp] theorem ofSelected_range (S : Set PrimeIndex) (hS : S.Infinite)
    (guard : ∀ p : PrimeIndex, ℤ_[p.val])
    (hguard : ∀ p, Transcendental ℚ (guard p).val) :
    Set.range (ofSelected S hS guard hguard).primes = S := SelectedPrimes.range_primes S hS

@[simp] theorem ofSelected_primary_zero (S : Set PrimeIndex) (hS : S.Infinite)
    (guard : ∀ p : PrimeIndex, ℤ_[p.val])
    (hguard : ∀ p, Transcendental ℚ (guard p).val) :
    ((ofSelected S hS guard hguard).primary 0).val.valuation = 2 :=
  SelectedPrimes.primary_zero _

def vertical (d : Places) : ℕ ⊕ PrimeIndex → Valuation (RatFunc ℚ) ℤᵐ⁰
  | .inl i => EvaluationDVR.evaluationValuation (d.primes i).val (d.primary i).val (d.primary_trans i)
  | .inr p => EvaluationDVR.valuation p.val (guardEvaluation d.guard d.guard_trans p)

abbrev domain (S : Set ℚ[X]) (d : Places) : Subring (RatFunc ℚ) :=
  IntersectionDomain.intersection (PoleAlgebra.generated S).toSubring (vertical d)

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
    exact (not_lt_of_ge (exp_le_one_iff.mpr (neg_nonpos.mpr (PairedDomain.tOrder_nonneg_of_mem hS hf)))) hi
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

/-- At a prime omitted from the primary sequence, the rational prime itself
has positive value only at its sole guard, with value exactly one. -/
theorem unpaired_prime_profile (d : Places) (p : PrimeIndex)
    (hp : p ∉ Set.range d.primes) :
    vertical d (.inr p) (p.val : RatFunc ℚ) = exp (-1) ∧
      ∀ i, i ≠ .inr p → vertical d i (p.val : RatFunc ℚ) = 1 := by
  constructor
  · exact EvaluationDVR.valuation_prime _ _
  · rintro (j | q) hi
    · apply PairedSpectrum.valuation_other_prime
      intro h
      exact hp ⟨j, h⟩
    · apply PairedSpectrum.valuation_other_prime
      intro h
      exact hi (congrArg Sum.inr h)

/-- The actual one-guard residue map of the sparse-primary intersection. -/
def guardResidue (S : Set ℚ[X]) (d : Places) (p : PrimeIndex) :
    domain S d →+* ZMod p.val :=
  (EvaluationDVR.residueMap p.val (guardEvaluation d.guard d.guard_trans p)).comp
    (IntersectionStalks.valuationInclusion (PoleAlgebra.generated S).toSubring (vertical d) (.inr p))

theorem guardResidue_surjective (S : Set ℚ[X]) (d : Places) (p : PrimeIndex) :
    Function.Surjective (guardResidue S d p) := ZMod.ringHom_surjective _

theorem guardResidue_ker_center (S : Set ℚ[X]) (d : Places) (p : PrimeIndex) :
    RingHom.ker (guardResidue S d p) =
      IntersectionStalks.center (PoleAlgebra.generated S).toSubring (vertical d) (.inr p) := by
  change Ideal.comap
    (IntersectionStalks.valuationInclusion (PoleAlgebra.generated S).toSubring (vertical d) (.inr p))
    (RingHom.ker (EvaluationDVR.residueMap p.val (guardEvaluation d.guard d.guard_trans p))) = _
  rw [EvaluationDVR.residueMap_ker]
  rfl

/-- A value-one singleton isolator has exactly its principal ideal as center. -/
theorem center_eq_span_of_value_one {K ι : Type*} [Field K]
    (B : Subring K) (v : ι → Valuation K ℤᵐ⁰) (i : ι)
    (f : IntersectionDomain.intersection B v) (hfinv : (f : K)⁻¹ ∈ B)
    (hfi : v i f = exp (-1)) (hother : ∀ j, j ≠ i → v j f = 1) :
    IntersectionStalks.center B v i = Ideal.span {f} := by
  have hf0 : f ≠ 0 := by
    intro hf
    exact exp_ne_zero (hfi.symm.trans (by simp [hf]))
  apply le_antisymm
  · intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxK : (x : K) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hxv := (IntersectionStalks.mem_center B v i x).mp hx
    obtain ⟨m, hm⟩ := IntersectionStalks.exists_nat_value (v i) x hxK hxv.le
    have hmpos : 0 < m := by
      rw [hm, exp_lt_one_iff] at hxv
      omega
    have hbound : v i ((x : K) / (f : K) ^ (1 : ℕ)) ≤ 1 := by
      rw [pow_one, map_div₀, hm, hfi, ← exp_sub, exp_le_one_iff]
      omega
    have hquot := IntersectionStalks.div_pow_mem_of_bound B v i (x : K) f
      x.property hfinv hother 1 hbound
    rw [Ideal.mem_span_singleton, IntersectionDomain.subring_dvd_iff_div_mem _ f x hf0]
    simpa only [pow_one] using hquot
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [IntersectionStalks.mem_center, hfi, exp_lt_one_iff]
    norm_num

/-- At an unpaired prime, the actual residue kernel is pD, not merely its radical. -/
theorem guardResidue_ker_unpaired (S : Set ℚ[X]) (d : Places) (p : PrimeIndex)
    (hp : p ∉ Set.range d.primes) :
    RingHom.ker (guardResidue S d p) = Ideal.span {(p.val : domain S d)} := by
  rw [guardResidue_ker_center]
  obtain ⟨hmain, hother⟩ := unpaired_prime_profile d p hp
  apply center_eq_span_of_value_one _ _ _ (p.val : domain S d) _ hmain hother
  change ((p.val : RatFunc ℚ)⁻¹) ∈ PoleAlgebra.generated S
  simpa only [map_inv₀, map_natCast] using
    (PoleAlgebra.generated S).algebraMap_mem ((p.val : ℚ)⁻¹)

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

end UnconditionalCounterexample.SparsePrimaryDomain
