import UnconditionalCounterexample.SingleTensorConductor
import UnconditionalCounterexample.SingleTensorLifting
import UnconditionalCounterexample.GuardSupport
import UnconditionalCounterexample.PaperGenericRecovery
import UnconditionalCounterexample.SequenceDomainValues

/-!
# The integer conductor for mixed one- and two-point fibres

A primary can reduce to either endpoint. The local lattice
argument only uses distinct residues at paired primes. For one sequence of
extracted words in the original subring, the transfer and derivative estimates
give the exact conductor of its integral tensor image at every prime. Descent
gives the original coordinate-clearing integer for the full intersection.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.UnivariateConductor

open Polynomial Filter GuardSupport LocalAlgebra RadicalConductor
open scoped TensorProduct

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- A transcendental integral evaluation point of the rational curve. -/
structure Point (p : PrimeIndex) where
  value : ℤ_[p.val]
  transcendental : Transcendental ℚ value.val

theorem Point.retained {p : PrimeIndex} (a : Point p) {f : ℚ[X]} (hf : f ≠ 0) :
    f.eval₂ (algebraMap ℚ ℚ_[p.val]) a.value.val ≠ 0 :=
  mt ((transcendental_iff.mp a.transcendental) f) hf

/-- A guard alone, or a primary and a guard with distinct reductions. -/
inductive Fibre (p : PrimeIndex) where
  | single (guard : Point p)
  | pair (primary guard : Point p)
      (separated : PadicInt.toZMod guard.value ≠ PadicInt.toZMod primary.value)

variable {p : PrimeIndex}

def Fibre.points : Fibre p → Set (Point p)
  | .single b => {b}
  | .pair a b _ => {a, b}

def Fibre.polynomial : Fibre p → ℚ_[p.val][X]
  | .single b => X - C b.value.val
  | .pair a b _ => (X - C a.value.val) * (X - C b.value.val)

theorem unit_difference (a b : Point p)
    (h : PadicInt.toZMod b.value ≠ PadicInt.toZMod a.value) :
    IsUnit (b.value - a.value) := by
  apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
  rw [map_sub]
  exact sub_ne_zero.mpr h

variable (S : Set ℚ[X])
local notation "B" => PoleAlgebra.generated S

/-- Inside the pole algebra take the intersection of the integral evaluation
rings for precisely the listed points. -/
def domain (fibres : (p : PrimeIndex) → Fibre p) : Subring B :=
  ⨅ (p : PrimeIndex) (a : (fibres p).points),
    (PadicInt.subring p.val).comap
      ((LocalEvaluation.evalAt a.val.value.val a.val.transcendental).toRingHom.comp
        (PoleAlgebra.generated S).val.toRingHom)

theorem norm_eval_le_one (fibres : (p : PrimeIndex) → Fibre p) {p : PrimeIndex}
    {a : Point p} (ha : a ∈ (fibres p).points) (x : domain S fibres) :
    ‖RatFunc.eval (algebraMap ℚ ℚ_[p.val]) a.value.val ((x : B) : RatFunc ℚ)‖ ≤ 1 := by
  have hx := Subring.mem_iInf.mp (Subring.mem_iInf.mp x.property p) (⟨a, ha⟩ : (fibres p).points)
  change ‖LocalEvaluation.evalAt a.value.val a.transcendental ((x : B) : RatFunc ℚ)‖ ≤ 1 at hx
  have he : LocalEvaluation.evalAt a.value.val a.transcendental ((x : B) : RatFunc ℚ) =
      RatFunc.eval (algebraMap ℚ ℚ_[p.val]) a.value.val ((x : B) : RatFunc ℚ) :=
    LocalEvaluation.evalAt_apply _ _ _
  rwa [he] at hx

theorem coordinate_mem (fibres : (p : PrimeIndex) → Fibre p) :
    algebraMap ℚ[X] B X ∈ domain S fibres := by
  refine Subring.mem_iInf.mpr fun p => Subring.mem_iInf.mpr fun a => ?_
  change LocalEvaluation.evalAt a.val.value.val a.val.transcendental RatFunc.X ∈ PadicInt.subring p.val
  rw [LocalEvaluation.evalAt_X]
  exact a.val.value.property

variable {S}

/-- The word sequence is chosen once in the original subring, before passing to
any completion. -/
structure Words (T : Subring (PoleAlgebra.generated S)) where
  element : ℕ → T
  F : ℕ → ℚ[X]
  H : ℕ → ℚ[X]
  exponent : ℕ → ℕ
  stage : ℕ → ℕ
  bound : ℕ
  denominator_ne_zero : ∀ i, H i ≠ 0
  fraction : ∀ i, ((element i : PoleAlgebra.generated S) : RatFunc ℚ) =
    algebraMap ℚ[X] (RatFunc ℚ) (F i) ^ exponent i / algebraMap ℚ[X] (RatFunc ℚ) (H i)
  stage_tends : Tendsto stage atTop atTop
  bounded : ∀ᶠ i in atTop, exponent i ≤ bound

variable {T : Subring (PoleAlgebra.generated S)}

/-- The estimates for the same words at a particular fibre. The two-term
identity lies in the scaled polynomial ring at every fixed scale. -/
structure Estimates (w : Words T) (fibre : Fibre p) : Prop where
  derivative : ∀ a ∈ fibre.points, ∀ᶠ i in atTop,
    (LocalInterpolation.wordDerivative ((w.F i).map (algebraMap ℚ ℚ_[p.val]))
      ((w.H i).map (algebraMap ℚ ℚ_[p.val])) (w.exponent i) a.value.val).valuation < -(w.stage i : ℤ)
  transfer : ∀ s : ℕ, ∀ᶠ i in atTop, ∃ u v : padicScaledPolynomialRing p.val s,
    (RatFunc.C (p.val : ℚ_[p.val]) ^ (2 * s) *
      (algebraMap ℚ_[p.val][X] (RatFunc ℚ_[p.val]) fibre.polynomial)) ^ w.exponent i =
      RatFunc.C (p.val : ℚ_[p.val]) ^ w.stage i * ((u : RatFunc ℚ_[p.val]) +
        (v : RatFunc ℚ_[p.val]) * (((w.F i).map (algebraMap ℚ ℚ_[p.val]) : RatFunc ℚ_[p.val]) ^
          w.exponent i / ((w.H i).map (algebraMap ℚ ℚ_[p.val]) : RatFunc ℚ_[p.val])))

variable (hS : ∀ f ∈ S, f ≠ 0) (D : Subring (PoleAlgebra.generated S))

theorem conductor_eq (hTD : T ≤ D) (hhull : RationalHull.hull T = ⊤)
    (fibre : Fibre p) (w : Words T) (hw : Estimates w fibre)
    (hval : ∀ a ∈ fibre.points, ∀ x : D,
      ‖RatFunc.eval (algebraMap ℚ ℚ_[p.val]) a.value.val ((x : PoleAlgebra.generated S) : RatFunc ℚ)‖ ≤ 1) :
    conductorIdeal (PoleTensorConductor.image p.val S hS T) =
      Ideal.span {algebraMap ℚ_[p.val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p.val] S)) fibre.polynomial} := by
  cases fibre with
  | single b =>
    have hb : b ∈ (Fibre.single b).points := rfl
    apply SingleTensorConductor.conductor_eq_single_of_extracted_words p.val S hS T D hTD hhull
      b.value.val b.value.property (fun f hf => b.retained (hS f hf)) (hval b hb)
      w.element w.F w.H w.exponent w.stage w.bound
      (fun i => b.retained (w.denominator_ne_zero i)) w.fraction w.stage_tends w.bounded
      (hw.derivative b hb)
    simpa only [Fibre.polynomial, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using hw.transfer
  | pair a b hab =>
    have ha : a ∈ (Fibre.pair a b hab).points := Set.mem_insert a {b}
    have hb : b ∈ (Fibre.pair a b hab).points := Set.mem_insert_of_mem a rfl
    have hne : a.value.val ≠ b.value.val := fun he =>
      hab (congrArg PadicInt.toZMod (Subtype.ext he.symm))
    apply PoleTensorConductor.conductor_eq_pair_of_extracted_words p.val S hS T D hTD hhull
      a.value.val b.value.val hne a.value.property b.value.property
      (fun f hf => a.retained (hS f hf)) (fun f hf => b.retained (hS f hf))
      (hval a ha) (hval b hb) w.element w.F w.H w.exponent w.stage w.bound
      (fun i => a.retained (w.denominator_ne_zero i)) (fun i => b.retained (w.denominator_ne_zero i))
      w.fraction w.stage_tends w.bounded (hw.derivative a ha) (hw.derivative b hb)
    simpa only [Fibre.polynomial, map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
      using hw.transfer

theorem same_integer_in_image (fibre : Fibre p)
    (hval : ∀ a ∈ fibre.points, ∀ x : D,
      ‖RatFunc.eval (algebraMap ℚ ℚ_[p.val]) a.value.val ((x : PoleAlgebra.generated S) : RatFunc ℚ)‖ ≤ 1)
    (hcond : conductorIdeal (PoleTensorConductor.image p.val S hS T) =
      Ideal.span {algebraMap ℚ_[p.val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p.val] S)) fibre.polynomial})
    (n : ℤ) (hnt : (n : PoleAlgebra.generated S) *
      algebraMap ℚ[X] (PoleAlgebra.generated S) X ∈ T) :
    ∀ z ∈ IntegralTensorImage.image p.val (PoleAlgebra.generated S) D,
      (n : ℚ_[p.val] ⊗[ℚ] PoleAlgebra.generated S) * z ∈
        IntegralTensorImage.image p.val (PoleAlgebra.generated S) T := by
  cases fibre with
  | single b =>
    exact SingleTensorLifting.same_integer_in_image p.val S hS T D b.value.val
      (fun f hf => b.retained (hS f hf)) (hval b rfl) hcond n
  | pair a b hab =>
    exact TensorPairLifting.same_integer_in_image p.val S hS T D a.value b.value
      (unit_difference a b hab) (fun f hf => a.retained (hS f hf)) (fun f hf => b.retained (hS f hf))
      (hval a (Set.mem_insert a {b})) (hval b (Set.mem_insert_of_mem a rfl)) hcond n hnt

include hS in
/-- The original coordinate-clearing integer works throughout the intersection,
including when some primaries themselves are units. -/
theorem same_integer (fibres : (p : PrimeIndex) → Fibre p) (hTD : T ≤ domain S fibres)
    (hhull : RationalHull.hull T = ⊤) (w : Words T) (hw : ∀ p, Estimates w (fibres p))
    (n : ℤ) (hnt : (n : PoleAlgebra.generated S) *
      algebraMap ℚ[X] (PoleAlgebra.generated S) X ∈ T) :
    ∀ x ∈ domain S fibres, (n : PoleAlgebra.generated S) * x ∈ T := by
  apply TorsionDescent.integer_conductor_of_all_images T (domain S fibres) hhull n
  intro p hp
  let q : PrimeIndex := ⟨p, hp.out⟩
  have hval := fun a ha => norm_eval_le_one S fibres (p := q) (a := a) ha
  exact same_integer_in_image hS (domain S fibres) (fibres q) hval
    (conductor_eq hS (domain S fibres) hTD hhull (fibres q) w (hw q) hval) n hnt

namespace OneCentre

open PrimaryChoices PaperConstruction PaperInclusion

def primaryPoint (j : ℕ) : Point (primes j) :=
  ⟨primary j, primary_transcendental j⟩

def guardPoint (j : ℕ) : Point (primes j) :=
  ⟨construction.chain.guardChain.value (primes j),
    construction.chain.guardChain.value_transcendental (primes j)⟩

theorem separated (j : ℕ) :
    PadicInt.toZMod (guardPoint j).value ≠ PadicInt.toZMod (primaryPoint j).value := by
  intro h
  apply CombinedGuardStep.primary_not_unit j
  apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
  rw [← show PadicInt.toZMod (guardPoint j).value = PadicInt.toZMod (primary j) from h]
  exact (padicInt_isUnit_iff_toZMod_ne_zero _).mp (construction.chain.guardChain.value_unit _)

def fibres : (p : PrimeIndex) → Fibre p :=
  Equiv.piCongrLeft Fibre primes.toEquiv fun j =>
    .pair (primaryPoint j) (guardPoint j) (separated j)

@[simp] theorem fibres_prime (j : ℕ) :
    fibres (primes j) = .pair (primaryPoint j) (guardPoint j) (separated j) :=
  Equiv.piCongrLeft_apply_apply Fibre primes.toEquiv _ _

/-- The new intersection on the original sequence is literally the old ring
viewed in its pole algebra. -/
theorem domain_eq :
    UnivariateConductor.domain poles fibres = SequenceDomainValues.domainInPole construction := by
  ext x
  change x ∈ UnivariateConductor.domain poles fibres ↔ (x : RatFunc ℚ) ∈ PaperConstruction.domain
  rw [PairedDomain.mem_domain_iff_branches]
  constructor
  · intro hx
    refine ⟨x.property, fun j b => ?_⟩
    have ha : primaryPoint j ∈ (fibres (primes j)).points := by
      rw [fibres_prime]
      exact Set.mem_insert _ _
    have hb : guardPoint j ∈ (fibres (primes j)).points := by
      rw [fibres_prime]
      exact Set.mem_insert_of_mem _ rfl
    cases b
    · exact Subring.mem_iInf.mp (Subring.mem_iInf.mp hx _) ⟨_, ha⟩
    · exact Subring.mem_iInf.mp (Subring.mem_iInf.mp hx _) ⟨_, hb⟩
  · rintro ⟨_, hx⟩
    apply Subring.mem_iInf.mpr
    intro p
    obtain ⟨j, rfl⟩ := primes.surjective p
    apply Subring.mem_iInf.mpr
    rintro ⟨a, ha⟩
    rw [fibres_prime] at ha
    rcases (show a = primaryPoint j ∨ a = guardPoint j from ha) with rfl | rfl
    · exact hx j false
    · exact hx j true

/-- An unbounded element in an original subring produces a single word family
with the estimates required by the mixed-fibre conductor interface. -/
theorem words_of_unbounded (T : Subring PaperConstruction.domain) (x : T) (hx : x ≠ 0)
    (hu : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ w : Words (T.map inclusion), ∀ p, Estimates w (fibres p) := by
  obtain ⟨r, _, y, stage, word, _, hstage, hbound, _, hword⟩ :=
    PaperGenericRecovery.exists_listed_sequence_of_unbounded T x hx hu
  let den i := (GlobalPlans.globalPlan construction (stage i)).wordDen (word i)
  let w : Words (T.map inclusion) :=
    { element := y
      F := fun i => raw (stage i)
      H := den
      exponent := fun i => (word i).latestExponent
      stage := fun i => stage i + 1
      bound := 2 * r
      denominator_ne_zero := fun i h => by
        have he := SequenceLocalTransfer.global_wordDen_eval_ne_zero construction (stage i) (word i) 0 false
        change (den i).eval₂ _ _ ≠ 0 at he
        simp only [h, eval₂_zero, ne_eq, not_true_eq_false] at he
      fraction := fun i => by
        rw [hword i]
        have h := ConstructionRecovery.global_word_eq_fraction raw exponent (stage i)
          (GlobalPlans.globalPlan construction (stage i)) (GlobalPlans.globalPlan_E construction (stage i)) (word i)
        rwa [ConstructionRecovery.oldDenominator_eq_wordDen] at h
      stage_tends := tendsto_atTop_mono (fun i => Nat.le_succ (stage i)) hstage
      bounded := Eventually.of_forall hbound }
  refine ⟨w, fun p => ?_⟩
  obtain ⟨j, rfl⟩ := primes.surjective p
  rw [fibres_prime]
  constructor
  · intro a ha
    filter_upwards [hstage.eventually (SequenceLocalTransfer.eventually_all_word_estimates construction j 0)]
      with i hi
    rcases (show a = primaryPoint j ∨ a = guardPoint j from ha) with rfl | rfl
    · exact (hi (word i)).1 false
    · exact (hi (word i)).1 true
  · intro s
    filter_upwards [hstage.eventually (SequenceLocalTransfer.eventually_all_word_estimates construction j s)]
      with i hi
    simpa only [Fibre.polynomial, map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      w, den, primaryPoint, guardPoint, SequenceLocalTransfer.branch, Bool.false_eq_true,
      ↓reduceIte] using (hi (word i)).2

end OneCentre

end UnconditionalCounterexample.Variations.UnivariateConductor
