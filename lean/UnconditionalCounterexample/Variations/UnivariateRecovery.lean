import UnconditionalCounterexample.Variations.UnivariateTransfer
import UnconditionalCounterexample.Variations.UnivariateConductor

/-!
# The conductor on the ring of the selected univariate sequence

An escaping sequence of listed words in an intrinsic subring suffices for
generic recovery and the integer conductor. The poles, permanent arguments,
word denominators, derivative bounds and transfer identities are all taken
from the same adaptive construction.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.Univariate

open Polynomial Filter GuardSupport PrimaryChoices ConstructionWords
open UnivariateConductor
open scoped TensorProduct

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

namespace Site

variable {p : PrimeIndex}

def fibre (s : Site p) : Fibre p :=
  match s.primary with
  | none => .single ⟨s.guard, s.guard_trans⟩
  | some a => .pair ⟨a.val, a.property.1⟩ ⟨s.guard, s.guard_trans⟩ a.property.2.symm

theorem branch_of_point (s : Site p) {a : Point p} (ha : a ∈ s.fibre.points) :
    ∃ b, MixedStageSelection.Active s.paired b ∧ s.branch b = a.value.val := by
  cases hp : s.primary with
  | none =>
    simp [fibre, hp, Fibre.points] at ha
    exact ⟨true, Or.inl rfl, by rw [ha]; rfl⟩
  | some z =>
    simp [fibre, hp, Fibre.points] at ha
    rcases ha with rfl | rfl
    · exact ⟨false, Or.inr (by simp [paired, hp]), by simp [branch, hp]⟩
    · exact ⟨true, Or.inl rfl, rfl⟩

theorem fibre_polynomial (s : Site p) :
    algebraMap ℚ_[p.val][X] (RatFunc ℚ_[p.val]) s.fibre.polynomial =
      MixedWordTransfer.vanishing s.paired s.branch := by
  cases hp : s.primary <;>
    simp [fibre, hp, Fibre.polynomial, MixedWordTransfer.vanishing, paired, branch,
      RatFunc.algebraMap_X, RatFunc.algebraMap_C]

end Site

variable (R : Requirements)

abbrev poles := Set.range (chain R).raw

theorem poles_nonzero : ∀ f ∈ poles R, f ≠ 0 := by
  rintro _ ⟨i, rfl⟩
  exact ((chain R).raw_monic i).ne_zero

abbrev poleAlgebra := PoleAlgebra.generated (poles R)

def domainInPole : Subring (poleAlgebra R) :=
  UnivariateConductor.domain (poles R) (fun p => (permanentSite R p).fibre)

/-- The intersection in the actual rational function field. -/
def domain : Subring (RatFunc ℚ) :=
  (domainInPole R).map (poleAlgebra R).val.toRingHom

theorem mem_domain_iff (x : RatFunc ℚ) : x ∈ domain R ↔
    x ∈ poleAlgebra R ∧ ∀ p (a : Point p), a ∈ (permanentSite R p).fibre.points →
      LocalEvaluation.evalAt a.value.val a.transcendental x ∈ PadicInt.subring p.val := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.property, fun p a ha => ?_⟩
    exact Subring.mem_iInf.mp (Subring.mem_iInf.mp hz p) ⟨a, ha⟩
  · rintro ⟨hx, he⟩
    exact ⟨⟨x, hx⟩, Subring.mem_iInf.mpr (fun p => Subring.mem_iInf.mpr fun a => he p a a.property), rfl⟩

def inclusion : domain R →+* poleAlgebra R :=
  (domain R).subtype.codRestrict (poleAlgebra R).toSubring fun x =>
    ((mem_domain_iff R _).mp x.property).1

theorem inclusion_injective : Function.Injective (inclusion R) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : poleAlgebra R => z.val) h)

theorem mem_domainInPole (x : domain R) : inclusion R x ∈ domainInPole R := by
  obtain ⟨z, hz, he⟩ := x.property
  exact (show z = inclusion R x from Subtype.ext he) ▸ hz

def coordinate : domain R :=
  ⟨RatFunc.X, ⟨algebraMap ℚ[X] (poleAlgebra R) X,
    coordinate_mem (poles R) (fun p => (permanentSite R p).fibre), rfl⟩⟩

theorem fractionRing : IsFractionRing (domain R) (RatFunc ℚ) :=
  RationalFunctionSubring.isFractionRing_of_X_mem _ (coordinate R).property

/-- A sequence of normalized words in the actual subring, with one common
latest-exponent bound. -/
structure ListedWords (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (T : Subring (PoleAlgebra.generated (Set.range F))) where
  element : ℕ → T
  stage : ℕ → ℕ
  word : ∀ i, Word (stage i)
  bound : ℕ
  bounded : ∀ i, (word i).latestExponent ≤ bound
  tends : Tendsto stage atTop atTop
  expansion : ∀ i, (((element i).val : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) =
    ScheduledRecovery.generators F E (stage i) ^ (word i).latestExponent *
      (∏ j ∈ Finset.range (stage i),
        ScheduledRecovery.generators F E j ^ (word i).oldExponent j)

abbrev ListedSequence (T : Subring (domain R)) :=
  ListedWords (chain R).raw (chain R).exponent (T.map (inclusion R))

variable {R} {T : Subring (domain R)} (L : ListedSequence R T)

def ListedSequence.words : Words (T.map (inclusion R)) where
  element := L.element
  F i := (chain R).raw (L.stage i)
  H i := (globalPlan R (L.stage i)).wordDen (L.word i)
  exponent i := (L.word i).latestExponent
  stage i := L.stage i + 1
  bound := L.bound
  denominator_ne_zero i := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact pow_ne_zero _ (((chain R).raw_monic k.val).ne_zero)
  fraction i := by
    rw [L.expansion i]
    have h := ConstructionRecovery.global_word_eq_fraction (chain R).raw (chain R).exponent
      (L.stage i) (globalPlan R (L.stage i)) ((chain R).exponent_eq_selected (L.stage i)).symm (L.word i)
    rwa [ConstructionRecovery.oldDenominator_eq_wordDen] at h
  stage_tends := tendsto_atTop_mono (fun i => Nat.le_succ (L.stage i)) L.tends
  bounded := Eventually.of_forall L.bounded

theorem ListedSequence.estimates (p : PrimeIndex) :
    Estimates L.words (permanentSite R p).fibre := by
  obtain ⟨j, rfl⟩ := primes.surjective p
  constructor
  · intro a ha
    obtain ⟨b, hb, he⟩ := (permanentSite R _).branch_of_point ha
    filter_upwards [L.tends.eventually (eventually_all_word_estimates R j 0)] with i hi
    rw [← he]
    exact (hi (L.word i)).1 b hb
  · intro s
    filter_upwards [L.tends.eventually (eventually_all_word_estimates R j s)] with i hi
    rw [Site.fibre_polynomial]
    exact (hi (L.word i)).2

include L in
theorem ListedSequence.hull : RationalHull.hull (T.map (inclusion R)) = ⊤ :=
  hull_eq_top_of_sequence R _ L.element L.stage L.tends L.word L.expansion

include L in
/-- The same words give the radical conductor in the actual transported tensor
image, generated by one or two transverse linear factors. -/
theorem ListedSequence.local_conductor (p : PrimeIndex) :
    RadicalConductor.conductorIdeal (PoleTensorConductor.image p.val (poles R) (poles_nonzero R)
      (T.map (inclusion R))) = Ideal.span {algebraMap ℚ_[p.val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p.val] (poles R)))
        (permanentSite R p).fibre.polynomial} := by
  exact conductor_eq (poles_nonzero R) (domainInPole R) (by
      rintro _ ⟨x, _, rfl⟩
      exact mem_domainInPole R x) L.hull (permanentSite R p).fibre L.words (L.estimates p)
    (fun a ha => norm_eval_le_one (poles R) (fun q => (permanentSite R q).fibre) (p := p) (a := a) ha)

include L in
theorem ListedSequence.local_tensor_inclusion (p : PrimeIndex) (n : ℕ)
    (hnt : (n : domain R) * coordinate R ∈ T) :
    ∀ z ∈ LocalAlgebra.IntegralTensorImage.image p.val (poleAlgebra R) (domainInPole R),
      (n : ℚ_[p.val] ⊗[ℚ] poleAlgebra R) * z ∈
        LocalAlgebra.IntegralTensorImage.image p.val (poleAlgebra R) (T.map (inclusion R)) := by
  let f := fun p => (permanentSite R p).fibre
  have hval := fun a ha => norm_eval_le_one (poles R) f (p := p) (a := a) ha
  have hnt' : ((n : ℤ) : poleAlgebra R) * algebraMap ℚ[X] (poleAlgebra R) X ∈ T.map (inclusion R) :=
    ⟨_, hnt, by rw [map_mul, map_natCast, Int.cast_natCast]; rfl⟩
  simpa only [Int.cast_natCast] using same_integer_in_image (poles_nonzero R) (domainInPole R)
    (f p) hval (L.local_conductor p) (n : ℤ) hnt'

include L in
/-- INDEX for the same permanent sites and selected polynomials, assuming only
the intrinsic listed sequence from WORDS. -/
theorem ListedSequence.integer_conductor :
    (∃ n : ℕ, 0 < n ∧ (n : domain R) * coordinate R ∈ T) ∧
      ∀ n : ℕ, (n : domain R) * coordinate R ∈ T → ∀ z : domain R, (n : domain R) * z ∈ T := by
  refine ⟨ConstructionRecovery.exists_nat_mul_mem_of_mapped_hull_eq_top (inclusion R)
    (inclusion_injective R) T L.hull (coordinate R), fun n hnt z => ?_⟩
  have hall := LocalAlgebra.TorsionDescent.integer_conductor_of_all_images _ (domainInPole R) L.hull
    (n : ℤ) (fun p hp => by simpa only [Int.cast_natCast] using
      L.local_tensor_inclusion ⟨p, hp.out⟩ n hnt)
  obtain ⟨y, hy, he⟩ := hall (inclusion R z) (mem_domainInPole R z)
  have h : y = (n : domain R) * z := inclusion_injective R (by
    simpa only [map_mul, map_natCast, Int.cast_natCast] using he)
  exact h ▸ hy

end UnconditionalCounterexample.Variations.Univariate
