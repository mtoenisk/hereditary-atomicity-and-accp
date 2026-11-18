import UnconditionalCounterexample.PaperConstruction
import UnconditionalCounterexample.ConstructionRecovery

/-!
# The canonical original-domain inclusion and coordinate

All actual subring images use the existing literal intersection inclusion into
the pole algebra. The original coordinate is RatFunc.X with its established
membership proof, and it maps to the same pole-algebra coordinate. Elementwise
integer clearing is pulled back to the original subring through this map.
-/

namespace UnconditionalCounterexample.PaperInclusion

noncomputable section
noncomputable local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

abbrev poleAlgebra := PoleAlgebra.generated PaperConstruction.poles

/-- The canonical map is the existing literal inclusion of the intersection. -/
def inclusion : PaperConstruction.domain →+* poleAlgebra :=
  IntersectionDomain.inclusion poleAlgebra.toSubring
    (PairedDomain.vertical PaperConstruction.places)

@[simp] theorem coe_inclusion (x : PaperConstruction.domain) :
    ((inclusion x : poleAlgebra) : RatFunc ℚ) = (x : RatFunc ℚ) := rfl

theorem inclusion_injective : Function.Injective inclusion := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : poleAlgebra => (z : RatFunc ℚ)) h)

/-- The coordinate in the original domain, with its actual membership proof. -/
def coordinate : PaperConstruction.domain :=
  ⟨RatFunc.X, PairedDomain.X_mem PaperConstruction.poles PaperConstruction.places⟩

@[simp] theorem coe_coordinate : (coordinate : RatFunc ℚ) = RatFunc.X := rfl

@[simp] theorem inclusion_coordinate :
    inclusion coordinate = CurveRecovery.coordinate PaperConstruction.poles := by
  apply Subtype.ext
  exact (CurveRecovery.coe_coordinate PaperConstruction.poles).symm

/-- The original domain inside B is equally its actual image and the preimage
of the original field subring along B's canonical inclusion. -/
theorem range_eq_comap : inclusion.range =
    PaperConstruction.domain.comap poleAlgebra.val.toRingHom := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact z.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem map_subring_le_range (T : Subring PaperConstruction.domain) :
    T.map inclusion ≤ inclusion.range := by
  rintro x ⟨z, _, rfl⟩
  exact ⟨z, rfl⟩

/-- Generic recovery clears elements in the original T, not just its image. -/
theorem exists_nat_mul_mem (T : Subring PaperConstruction.domain)
    (hT : RationalHull.hull (T.map inclusion) = ⊤) (x : PaperConstruction.domain) :
    ∃ n : ℕ, 0 < n ∧ (n : PaperConstruction.domain) * x ∈ T :=
  ConstructionRecovery.exists_nat_mul_mem_of_mapped_hull_eq_top
    inclusion inclusion_injective T hT x

theorem exists_nat_coordinate_mem (T : Subring PaperConstruction.domain)
    (hT : RationalHull.hull (T.map inclusion) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ (n : PaperConstruction.domain) * coordinate ∈ T :=
  exists_nat_mul_mem T hT coordinate

end
end UnconditionalCounterexample.PaperInclusion
