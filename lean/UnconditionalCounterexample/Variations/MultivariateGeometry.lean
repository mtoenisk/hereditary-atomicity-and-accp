import UnconditionalCounterexample.Variations.MultivariateSelectionFrozen
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Exhaustive geometry for the dimension constructions

The polynomial tests enumerate all affine points and all polynomial ideals
over the algebraic closure of the rationals. The origin and the rational
point (1,0,…,0) are retained at every stage.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial Variations GuardSupport MultivariateListedWords

abbrev GeometricField := AlgebraicClosure ℚ

private theorem countable_geometric_field : Countable GeometricField := by
  apply Set.countable_univ_iff.mp
  apply (IndependentTuples.countable_algebraic (A := ℚ) (L := GeometricField)).mono
  exact fun x _ => Algebra.IsAlgebraic.isAlgebraic x

/-- The rational point through which the full coordinate flag passes. -/
def flagPoint (r : ℕ) : Fin (r+1) → ℚ := Fin.cons 1 0

@[simp] theorem flagPoint_zero (r : ℕ) : flagPoint r 0 = 1 := rfl

/-- One enumeration for the main and point-pullback dimension schedules. -/
def standardGeometry (r : ℕ) : Geometry r GeometricField := by
  classical
  have : Countable GeometricField := countable_geometric_field
  exact ⟨(exists_surjective_nat _).choose, MultivariateReservations.exists_ideal_enumeration.choose,
    {0, algebraMap ℚ GeometricField ∘ flagPoint r}⟩

theorem all_points (r : ℕ) : Function.Surjective (standardGeometry r).point := by
  have : Countable GeometricField := countable_geometric_field
  exact (exists_surjective_nat _).choose_spec

theorem all_ideals (r : ℕ) : Function.Surjective (standardGeometry r).primeEnumeration := by
  have : Countable GeometricField := countable_geometric_field
  exact MultivariateReservations.exists_ideal_enumeration.choose_spec

variable {r : ℕ} {q : PrimeIndex} (L : LocalPrescription r q)

theorem raw_not_divisible_first (n : ℕ) : ¬ X (0 : Fin (r+1)) ∣ siteRaw L (standardGeometry r) n := by
  apply first_variable_not_dvd (requirements L (standardGeometry r)) _ n
  simp [requirements, standardGeometry]

theorem raw_at_flagPoint (n : ℕ) : eval (flagPoint r) (siteRaw L (standardGeometry r) n) ≠ 0 := by
  have hu : algebraMap ℚ GeometricField ∘ flagPoint r ∈ (standardGeometry r).fixed := by
    simp [standardGeometry]
  have h := fixed_survives (requirements L (standardGeometry r)) n _ hu
  intro hzero
  apply h
  change eval (algebraMap ℚ GeometricField ∘ flagPoint r)
    (MvPolynomial.map (algebraMap ℚ GeometricField) (siteRaw L (standardGeometry r) n)) = 0
  rw [← map_eval, hzero, map_zero]

theorem flagPoint_retained : MultivariateFibres.Retained
    (Submonoid.closure (Set.range (siteRaw L (standardGeometry r)))) (flagPoint r) := by
  rintro ⟨x,hx⟩
  change eval (flagPoint r) x ≠ 0
  induction hx using Submonoid.closure_induction with
  | mem z hz => obtain ⟨n, rfl⟩ := hz; exact raw_at_flagPoint L n
  | one => simp
  | mul a b _ _ ha hb => simpa only [map_mul] using mul_ne_zero ha hb

end UnconditionalCounterexample.MultivariateSelection
