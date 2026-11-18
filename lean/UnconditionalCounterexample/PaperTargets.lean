import UnconditionalCounterexample.Target
import UnconditionalCounterexample.RadicalConductor
import Mathlib.RingTheory.PicardGroup
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Acceptance contracts for manuscript Theorems A and B

Theorem A and Theorem B of *A hereditarily atomic domain without ACCP* concern the
same subring of RatFunc ℚ.

The coordinate RatFunc.X is irreducible in the domain. Its square starts a strictly
increasing chain with endpoints X² / ∏_{j<n} q_{2j}. The successive ratios q_{2j} are
multiplicatively independent modulo nonzero rational constants.

`CommRing.Pic D` is mathlib's actual Picard group. For a domain,
`ClassGroup.equivPic D` identifies it with invertible fractional ideals modulo
nonzero principal fractional ideals, precisely the manuscript's definition.
Neither contract assumes that D is Noetherian or Dedekind. The direct sum is
represented by finitely supported functions `ℕ →₀ ZMod 3`.

Every subring condition is intrinsic: units, irreducibles, bounded
factorizations and ACCP are computed in the subring itself. Additive indices
refer to the additive-group quotient, while the conductor is an actual ideal
of D. No quotient ring by an arbitrary subring is used.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperTargets

universe u

variable (R : Type u) [CommRing R]

/-- The actual unital subring ℤ + nR, with its literal integer-plus-multiple carrier. -/
def integerOrder (n : ℕ) : Subring R where
  carrier := {x | ∃ z : ℤ, ∃ y : R, x = (z : R) + (n : R) * y}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro a b ⟨z, x, rfl⟩ ⟨w, y, rfl⟩
    refine ⟨z + w, x + y, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro a ⟨z, x, rfl⟩
    refine ⟨-z, -x, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro a b ⟨z, x, rfl⟩ ⟨w, y, rfl⟩
    refine ⟨z * w, (z : R) * y + (w : R) * x + (n : R) * x * y, ?_⟩
    push_cast
    ring

/-- Membership in an integer order is exactly an integer plus an n-multiple. -/
@[simp] theorem mem_integerOrder (n : ℕ) (x : R) :
    x ∈ integerOrder R n ↔ ∃ z : ℤ, ∃ y : R, x = (z : R) + (n : R) * y := Iff.rfl

/-- Every nonzero proper ideal is a finite product of actual radical ideals. -/
def IsSPDomain : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → I ≠ ⊤ →
    ∃ L : List (Ideal R), (∀ J ∈ L, J.IsRadical) ∧ L.prod = I

variable (D : Subring (RatFunc ℚ))

/-- The same even-indexed nonzero ratios have no nontrivial integral relation modulo ℚˣ. -/
def EvenRatiosIndependentModuloRationals (q : ℕ → D) : Prop :=
  (∀ j, q (2 * j) ≠ 0) ∧
  ∀ (e : ℕ →₀ ℤ) (c : ℚ), c ≠ 0 →
    e.prod (fun j m => ((q (2 * j) : D) : RatFunc ℚ) ^ m) = RatFunc.C c → e = 0

/-- One explicit chain and its actual ratios: endpoints are t² divided by their prefixes, and those same ratios are independent modulo ℚˣ. -/
def SquareChainConclusion (t : D) : Prop :=
  ∃ q x : ℕ → D,
    (∀ n, q n ≠ 0 ∧ ¬ IsUnit (q n)) ∧
    (∀ n, x n ≠ 0) ∧
    x 0 = t ^ 2 ∧
    (∀ n, (x n : RatFunc ℚ) = (t : RatFunc ℚ) ^ 2 /
      ∏ j ∈ Finset.range n, (q (2 * j) : RatFunc ℚ)) ∧
    (∀ n, x n = q (2 * n) * x (n + 1)) ∧
    StrictMono (fun n => Ideal.span ({x n} : Set D)) ∧
    EvenRatiosIndependentModuloRationals D q

/-- The invertible-fractional-ideal class group is a countable direct sum of groups of order three. -/
def ClassGroupConclusion : Prop :=
  Nonempty (Additive (ClassGroup D) ≃+ (ℕ →₀ ZMod 3))

/-- The actual Picard group is a countable direct sum of groups of order three. -/
def PicardGroupConclusion : Prop :=
  Nonempty (Additive (CommRing.Pic D) ≃+ (ℕ →₀ ZMod 3))

/-- The Picard and fractional-ideal class-group formulations agree for this actual domain. -/
theorem picardGroupConclusion_iff_classGroupConclusion :
    PicardGroupConclusion D ↔ ClassGroupConclusion D := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(ClassGroup.equivPic D).toAdditive.trans e⟩
  · rintro ⟨e⟩
    exact ⟨(ClassGroup.equivPic D).symm.toAdditive.trans e⟩

/-- Manuscript Theorem A, including the literal atom t=X and the explicit independent-ratio chain at t². -/
def TheoremAConclusion : Prop :=
  Factorization.IsHereditarilyAtomic D ∧
  IsFractionRing D (RatFunc ℚ) ∧
  (∀ x : D, IsUnit x ↔ x = 1 ∨ x = -1) ∧
  (∃ t : D, (t : RatFunc ℚ) = RatFunc.X ∧ Irreducible t ∧ SquareChainConclusion D t) ∧
  ¬ WfDvdMonoid D ∧
  IsAlmostDedekindDomain D ∧
  IsSPDomain D ∧
  PicardGroupConclusion D

/-- Manuscript Theorem B for every actual unital subring, with additive index, exact integer order, exact conductor, and hereditary bounded factorization. -/
def TheoremBConclusion : Prop :=
  ∀ T : Subring D,
    (¬ WfDvdMonoid T ↔ ¬ Factorization.IsBFDomain T) ∧
    (¬ Factorization.IsBFDomain T ↔ Finite (D ⧸ T.toAddSubgroup)) ∧
    (Finite (D ⧸ T.toAddSubgroup) ↔ ∃ n : ℕ, 0 < n ∧ T = integerOrder D n) ∧
    (∀ n : ℕ, 0 < n → T = integerOrder D n →
      T.toAddSubgroup.index = n ∧
      RadicalConductor.conductorIdeal T = Ideal.span {(n : D)}) ∧
    (Infinite (D ⧸ T.toAddSubgroup) → Factorization.IsHereditarilyBF T)

/-- Both manuscript theorems on the same domain D. -/
def PaperConclusion : Prop := TheoremAConclusion D ∧ TheoremBConclusion D

/-- The paper-facing existence target; this definition does not assert an inhabitant. -/
def PaperCounterexampleExists : Prop := ∃ D : Subring (RatFunc ℚ), PaperConclusion D

end UnconditionalCounterexample.PaperTargets
