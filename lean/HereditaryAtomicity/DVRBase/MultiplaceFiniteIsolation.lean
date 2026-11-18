import HereditaryAtomicity.DVRBase.MultiplaceConsequencesPicard

/-! Finite source-top support isolates its centres in every containing
nonzero principal fibre. -/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R]

/-- A point of a finite source support is clopen in any nonzero principal
fibre containing it. The actual singleton component is therefore available
without a separately assumed isolation condition. -/
theorem isClopenInFiber_singleton_of_finite_support
    (π d : R) (hπ : π ≠ 0)
    (hfinite : Set.Finite {P : MaximalSpectrum R | d ∈ P.asIdeal})
    (P : MaximalSpectrum R) (hπP : π ∈ P.asIdeal) (hdP : d ∈ P.asIdeal) :
    IsClopenInFiber π {P} := by
  refine ⟨fun Q hQ => (Set.mem_singleton_iff.mp hQ).symm ▸ hπP, ?_⟩
  let Q : MaximalFiber π := ⟨P, hπP⟩
  have hV := isClopen_fiber_support π hπ d
  have hVfinite : Set.Finite {Q : MaximalFiber π | d ∈ Q.val.asIdeal} :=
    Set.Finite.preimage Subtype.val_injective.injOn hfinite
  have hQopen : IsOpen ({Q} : Set (MaximalFiber π)) :=
    isOpen_singleton_of_finite_mem_nhds Q (hV.2.mem_nhds hdP) hVfinite
  have heq : (Subtype.val : MaximalFiber π → MaximalSpectrum R) ⁻¹' {P} = {Q} := by
    ext T
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [heq]
  exact ⟨isClosed_singleton, hQopen⟩

/-- The ideal component depends only on its region, not on the principal
fibre used to exhibit that region as clopen. -/
theorem componentIdeal_eq_of_same_region {π ρ : R} {U : Set (MaximalSpectrum R)}
    (hπ : IsClopenInFiber π U) (hρ : IsClopenInFiber ρ U) (d : R) (hd : d ≠ 0) :
    componentIdeal hπ d hd = componentIdeal hρ d hd :=
  (componentIdeal_spec hπ d hd).unique (componentIdeal_spec hρ d hd)

/-- Changing the anchor of an actual region preserves its genuine source
class map exactly. -/
theorem componentClassHom_eq_of_same_region {π ρ : R} {U : Set (MaximalSpectrum R)}
    (hπ : IsClopenInFiber π U) (hρ : IsClopenInFiber ρ U) :
    componentClassHom hπ = componentClassHom hρ := by
  apply MonoidHom.ext
  intro d
  have hu : componentUnit hπ d (nonZeroDivisors.ne_zero d.property) =
      componentUnit hρ d (nonZeroDivisors.ne_zero d.property) := by
    apply Units.ext
    simp only [componentUnit_coe, componentIdeal_eq_of_same_region hπ hρ]
  change ClassGroup.mk (FractionRing R) (componentUnit hπ d _) =
    ClassGroup.mk (FractionRing R) (componentUnit hρ d _)
  rw [hu]

/-- The actual fraction-field class map is likewise independent of the anchor. -/
theorem componentFractionClassHom_eq_of_same_region
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {π ρ : R} {U : Set (MaximalSpectrum R)}
    (hπ : IsClopenInFiber π U) (hρ : IsClopenInFiber ρ U) :
    componentFractionClassHom (K := K) hπ = componentFractionClassHom (K := K) hρ := by
  simp only [componentFractionClassHom, componentClassHom_eq_of_same_region hπ hρ]

end HereditaryAtomicity.DVRBase
