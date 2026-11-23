import UnconditionalCounterexample.Hierarchy.WeightedConstruction
import UnconditionalCounterexample.Hierarchy.WeightedGuards
import UnconditionalCounterexample.Hierarchy.WeightedAtoms

/-!
# Realizing integral profiles by units of the polynomial pole algebra

The selected raw polynomial is itself a unit after the corresponding pole
is inverted. Multiplication by a rational scalar gives independent control
of all complementary guards. In particular one can remove the full doubled
vertical profile of a field element, or realize a single nonnegative clopen
patch as an actual element of the intersection.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open Polynomial DiscreteOrders TopologicalSpace WithZero
open Classical

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

private def rawUnit (F : ℕ → ℚ[X]) (hf : ∀ j, F j ≠ 0) (j : ℕ) :
    (PoleAlgebra.generated (Set.range F))ˣ := by
  let f := algebraMap ℚ[X] (RatFunc ℚ) (F j)
  let b : PoleAlgebra.generated (Set.range F) := ⟨f, PoleAlgebra.polynomial_mem _ _⟩
  let y : PoleAlgebra.generated (Set.range F) :=
    ⟨f⁻¹, PoleAlgebra.inverse_mem (Set.mem_range_self j)⟩
  exact Units.mkOfMulEqOne b y (Subtype.ext (mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero (hf j))))

variable (P : ℕ → FiberPlace) (F : ℕ → ℚ[X])

local notation "poleRing" F => PoleAlgebra.generated (Set.range F)

/-- Realization of all even finite compact profiles of integral weight, with
independently prescribed orders at every complementary guard. -/
theorem realizes_unit_profile (hf : ∀ j, F j ≠ 0)
    (hreal : ∀ g : Profile, Admissible g → ∃ j, ∀ n x,
      order (valuation P (.inl (n,x))) (algebraMap ℚ[X] (RatFunc ℚ) (F j)) = g n x)
    (g : Profile) (hg : Admissible g) (k : Guard P →₀ ℤ) :
    ∃ u : (poleRing F)ˣ, (∀ n x, order (valuation P (.inl (n,x))) (u.val : RatFunc ℚ) = g n x) ∧
      ∀ i : Guard P, order (valuation P (.inr i)) (u.val : RatFunc ℚ) = k i := by
  obtain ⟨j,hj⟩ := hreal g hg
  obtain ⟨u,hu,huG⟩ := adjust_guard_orders P (Set.range F) (rawUnit F hf j) k
  exact ⟨u, fun n x => (hu n x).trans (hj n x), huG⟩

/-- Every doubled integral-weight profile is an admissible request. -/
theorem admissible_double (g : Profile) (hg : ∃ z : ℤ, profileWeight g = z) :
    Admissible (g + g) := by
  obtain ⟨z,hz⟩ := hg
  exact ⟨fun n x => ⟨g n x, rfl⟩, 2*z, by rw [map_add, hz]; push_cast; ring⟩

/-- The unmarked height-two patches and the first marked height-eight
patch have even entries. Their respective weights are zero and one. -/
private theorem admissible_patch (n : ℕ) (C : Clopens Fiber) (s : ℤ) (he : Even s)
    (hW : ∃ z : ℤ, profileWeight (Finsupp.single n (patch C s)) = z) :
    Admissible (Finsupp.single n (patch C s)) := by
  refine ⟨fun k x => ?_, hW⟩
  by_cases hk : k = n
  · subst k
    rw [Finsupp.single_eq_same, patch_apply]
    split_ifs <;> first | exact he | exact ⟨0, rfl⟩
  · simp [Finsupp.single_eq_of_ne hk]

theorem admissible_unmarked_patch (n : ℕ) (C : Clopens Fiber)
    (ha : mark false ∉ C) (hb : mark true ∉ C) :
    Admissible (Finsupp.single n (patch C 2)) := by
  apply admissible_patch _ _ _ (by decide)
  exact ⟨0, by simp [profileWeight_single_patch, ha, hb]⟩

theorem admissible_first_patch : Admissible (Finsupp.single 0 (patch firstPatch 8)) := by
  apply admissible_patch _ _ _ (by decide)
  exact ⟨1, by norm_num [profileWeight_single_patch, weight]⟩



/-- Realize every requested profile and all guard values in the concrete
pole algebra of the selected sequence. -/
theorem selected_unit_profile (g : Profile) (hg : Admissible g) (k : Guard selectedPlaces →₀ ℤ) :
    ∃ u : (poleRing selectedPoles)ˣ,
      (∀ n x, order (valuation selectedPlaces (.inl (n,x))) (u.val : RatFunc ℚ) = g n x) ∧
      ∀ i : Guard selectedPlaces, order (valuation selectedPlaces (.inr i)) (u.val : RatFunc ℚ) = k i :=
  realizes_unit_profile selectedPlaces selectedPoles (fun j => (selectedPole_irreducible j).ne_zero)
    selectedPole_realizes g hg k

/-- The prescribed pole unit has the square's valuation on every selected
fiber and complementary guard, all on the same ring. -/
theorem selected_doubled_profiles (x : selectedRing) (hx : x ≠ 0) :
    ∃ u : (poleRing selectedPoles)ˣ, ∀ i,
      valuation selectedPlaces i (u.val : RatFunc ℚ) = valuation selectedPlaces i (x : RatFunc ℚ)^2 := by
  have hxK : (x : RatFunc ℚ) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨g,hg,hW⟩ := selectedField_hasIntegralProfile x hxK
  let k := guardProfile selectedPlaces (x : RatFunc ℚ)
  obtain ⟨u,hu,huG⟩ := selected_unit_profile (g+g) (admissible_double g hW) (k+k)
  have hu0 : (u.val : RatFunc ℚ) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  refine ⟨u, fun i => ?_⟩
  have he : order (valuation selectedPlaces i) (u.val : RatFunc ℚ) =
      order (valuation selectedPlaces i) (x : RatFunc ℚ) + order (valuation selectedPlaces i) (x : RatFunc ℚ) := by
    rcases i with ⟨n,y⟩ | q
    · simpa only [Finsupp.add_apply, LocallyConstant.add_apply, hg] using hu n y
    · exact huG q
  rw [value_eq_exp_neg_order _ hu0, value_eq_exp_neg_order _ hxK, he, neg_add, exp_add, pow_two]

private theorem selected_patch (n : ℕ) (C : Clopens Fiber) (s : ℤ) (hs : 0 ≤ s)
    (ha : Admissible (Finsupp.single n (patch C s))) :
    RealizesPatch (poleRing selectedPoles).toSubring (valuation selectedPlaces) n C s := by
  obtain ⟨u,hu,hg⟩ := selected_unit_profile _ ha 0
  refine realizesPatch_of_unit (poleRing selectedPoles).toSubring (valuation selectedPlaces) n C s hs u ?_ hg
  intro k y
  by_cases hk : k = n
  · subst k
    simpa using hu n y
  · simpa [hk, Finsupp.single_eq_of_ne hk] using hu k y

/-- Each unmarked height-two patch is realized by a pole unit in the
intersection, with zero guard orders. -/
theorem selected_unmarked_patch (n : ℕ) (C : Clopens Fiber)
    (ha : mark false ∉ C) (hb : mark true ∉ C) :
    RealizesPatch (poleRing selectedPoles).toSubring (valuation selectedPlaces) n C 2 :=
  selected_patch n C 2 (by decide) (admissible_unmarked_patch n C ha hb)

/-- The first height-eight patch is realized by an actual element of the
domain. Its marked difference is eight, of weight one. -/
theorem selected_first_patch :
    RealizesPatch (poleRing selectedPoles).toSubring (valuation selectedPlaces) 0 firstPatch 8 :=
  selected_patch 0 firstPatch 8 (by decide) admissible_first_patch

end UnconditionalCounterexample.Hierarchy.Weighted
