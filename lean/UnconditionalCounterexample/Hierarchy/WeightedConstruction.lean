import UnconditionalCounterexample.Hierarchy.WeightedChoice
import UnconditionalCounterexample.Hierarchy.ProfilePolynomials
import UnconditionalCounterexample.Hierarchy.WeightedSchedule
import UnconditionalCounterexample.Hierarchy.WeightedFieldProfiles
import UnconditionalCounterexample.Hierarchy.PoleUnits

/-!
# The selected primes and polynomial poles of the weighted construction

The same sequence of Cantor fibers processes all ordinary irreducibles,
preserves earlier pole profiles, and realizes every admissible request.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted
open Polynomial GuardSupport DiscreteOrders
open Classical

/-- The actual finite-stage inputs: a residue choice, an exact prescribed
marked difference, and one irreducible realizing the assigned fiber values. -/
def choices : StageChoices FiberPlace where
  prime P := P.prime.val
  order P := P.polynomialOrder
  safe frozen N := by
    let S := frozen.image Subtype.val
    have hn : ∀ g ∈ S, g ≠ 0 := by
      rintro g hg
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
      exact i.property.2.ne_zero
    obtain ⟨P, hp, hs⟩ := exists_safe_place S hn N
    exact ⟨P, hp, fun g hg => hs g.val (Finset.mem_image_of_mem _ hg)⟩
  correct frozen f hnew k N := by
    let S := frozen.image Subtype.val
    have hs : ∀ g ∈ S, g.Monic ∧ Irreducible g := by
      intro g hg
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
      exact i.property
    have hf : f.val ∉ S := by
      intro hg
      obtain ⟨i, hmem, hi⟩ := Finset.mem_image.mp hg
      exact hnew (Subtype.ext hi ▸ hmem)
    obtain ⟨s, hp⟩ := exists_correctionBalls_of_monic f.val f.property.1 f.property.2 S hf hs k N
    refine ⟨s.place, hp, fun g hg x => s.frozen_order (Finset.mem_image_of_mem _ hg) x, ?_⟩
    rw [s.order, s.order]
    change max k 0 - max (-k) 0 = k
    omega
  approximate A hinj g m := by
    have hi : Function.Injective fun i => (A i).prime :=
      fun i j h => hinj (congrArg Subtype.val h)
    obtain ⟨f, hm, hi', hd, hvalues⟩ := exists_profile_polynomial A hi (fun i => g i.val) m
    exact ⟨⟨f, hm, hi'⟩, hd, hvalues⟩

/-- The infinite sequence of actual compact transcendental fibers. -/
def selectedPlaces : ℕ → FiberPlace := choices.places

/-- Polynomial poles selected by approximation on the same sequence. -/
def selectedPoles (j : ℕ) : ℚ[X] := (choices.raw j).val

/-- The overring with these poles and the selected and ordinary guard evaluations. -/
def selectedRing : Subring (RatFunc ℚ) := ring selectedPlaces (Set.range selectedPoles)

theorem selectedPrimes_strict : StrictMono (fun j => (selectedPlaces j).prime.val) :=
  choices.primes_strict

theorem selectedPrimes_injective : Function.Injective (fun j => (selectedPlaces j).prime) :=
  fun _ _ h => selectedPrimes_strict.injective (congrArg Subtype.val h)

theorem selectedDegrees_strict : StrictMono (fun j => (selectedPoles j).natDegree) :=
  choices.degrees_strict

theorem selectedPole_monic (j : ℕ) : (selectedPoles j).Monic := (choices.raw j).property.1
theorem selectedPole_irreducible (j : ℕ) : Irreducible (selectedPoles j) := (choices.raw j).property.2

theorem selectedOrdinary_certified (f : Ordinary) : Certified selectedPlaces f := by
  obtain ⟨N, d, hu, he, hi⟩ := choices.ordinary_profile f
  exact ⟨⟨N, hu⟩, d, he, hi⟩

theorem selectedField_hasIntegralProfile (x : RatFunc ℚ) (hx : x ≠ 0) :
    HasIntegralProfile selectedPlaces x :=
  field_hasIntegralProfile selectedPlaces selectedPrimes_injective selectedOrdinary_certified x hx

/-- Every admissible profile occurs as the orders of an actual selected pole. -/
theorem selectedPole_realizes (g : Profile) (hg : Admissible g) :
    ∃ j, ∀ n x, order (valuation selectedPlaces (.inl (n,x)))
      (algebraMap ℚ[X] (RatFunc ℚ) (selectedPoles j)) = g n x := by
  obtain ⟨j, hj⟩ := choices.realizes_profile g hg
  exact ⟨j, fun n x => (order_polynomial selectedPlaces n x _).trans (hj n x)⟩

theorem selectedPole_even (j n : ℕ) (x : Fiber) :
    Even (order (valuation selectedPlaces (.inl (n,x)))
      (algebraMap ℚ[X] (RatFunc ℚ) (selectedPoles j))) := by
  obtain ⟨g, hg, he⟩ := choices.raw_profile j
  rw [order_polynomial]
  change Even (choices.order (choices.places n) (choices.raw j).val x)
  rw [he n x]
  exact hg.1 n x

/-- Orders of a pole-algebra unit have constant parity along each whole fiber. -/
theorem selectedPoleUnit_parity (u : PoleAlgebra.generated (Set.range selectedPoles))
    (hu : IsUnit u) (n : ℕ) (x y : Fiber) :
    Int.ModEq 2 (order (valuation selectedPlaces (.inl (n,x))) (u : RatFunc ℚ))
      (order (valuation selectedPlaces (.inl (n,y))) (u : RatFunc ℚ)) := by
  apply PoleUnits.order_modEq selectedPoles selectedPole_irreducible u hu
  · intro c _
    rw [← RatFunc.algebraMap_C, order_polynomial, order_polynomial]
    simp [FiberPlace.polynomialOrder]
  · intro i
    obtain ⟨a, ha⟩ := selectedPole_even i n x
    obtain ⟨b, hb⟩ := selectedPole_even i n y
    change Int.ModEq 2 (order _ (algebraMap ℚ[X] (RatFunc ℚ) (selectedPoles i)))
      (order _ (algebraMap ℚ[X] (RatFunc ℚ) (selectedPoles i)))
    rw [ha, hb]
    exact Int.modEq_iff_dvd.mpr ⟨b-a, by ring⟩

end UnconditionalCounterexample.Hierarchy.Weighted
