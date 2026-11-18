import HereditaryAtomicity.DVRBase.ComponentClasses
import HereditaryAtomicity.DVRBase.MultiplaceConsequencesExtension

/-!
# Actual component class maps on the fraction field

These maps use the real ClassGroup of the source domain. The finite-singleton
product theorem is class cancellation for elements with the specified support.
-/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped nonZeroDivisors BigOperators
variable {R K : Type*} [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual component class map extends to all nonzero fractions. -/
def componentFractionClassHom {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) : Kˣ →* ClassGroup R :=
  extendSourceClassHom (componentClassHom hU)

@[simp] theorem componentFractionClassHom_source {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R⁰) :
    componentFractionClassHom (K := K) hU (sourceNonzeroToFractionUnits d) =
      componentClassHom hU d := extendSourceClassHom_source _ _

/-- A source element avoiding the selected region has trivial actual class. -/
theorem componentClassHom_eq_one_of_avoid {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R⁰) (hdU : ∀ P ∈ U, (d : R) ∉ P.asIdeal) :
    componentClassHom hU d = 1 := by
  have hu : componentUnit hU d (nonZeroDivisors.ne_zero d.property) = 1 := by
    apply Units.ext
    simp [componentIdeal_eq_top hU d (nonZeroDivisors.ne_zero d.property) hdU]
  change ClassGroup.mk (FractionRing R) (componentUnit hU d _) = 1
  rw [hu, map_one]

/-- Components at finitely many isolated centres multiply to the source
principal ideal whenever those centres contain the support of the element. -/
theorem prod_singleton_componentIdeal (S : Finset (MaximalSpectrum R))
    (π : S → R) (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (d : R) (hd : d ≠ 0) (hsupp : ∀ P : MaximalSpectrum R, d ∈ P.asIdeal → P ∈ S) :
    (∏ P : S, componentIdeal (hU P) d hd) = Ideal.span {d} := by
  classical
  apply Ideal.eq_of_localization_maximal
  intro Q hQ
  let Q' : MaximalSpectrum R := ⟨Q, hQ⟩
  change (Ideal.mapHom (algebraMap R (Localization.AtPrime Q)))
    (∏ P : S, componentIdeal (hU P) d hd) = _
  rw [map_prod]
  by_cases hQS : Q' ∈ S
  · let q : S := ⟨Q', hQS⟩
    rw [Finset.prod_eq_single q]
    · exact ((componentIdeal_spec (hU q) d hd).map_mem Q' (Set.mem_singleton Q')).trans
        (by simp only [Q', Ideal.map_span, Set.image_singleton])
    · intro P _ hne
      rw [Ideal.one_eq_top]
      change Ideal.map (algebraMap R (Localization.AtPrime Q))
        (componentIdeal (hU P) d hd) = ⊤
      simpa only [Q'] using
        (componentIdeal_spec (hU P) d hd).map_not_mem Q' (by
        intro h
        apply hne
        exact Subtype.ext (Set.mem_singleton_iff.mp h).symm)
    · simp
  · have hprod : (∏ P : S, (Ideal.mapHom (algebraMap R (Localization.AtPrime Q)))
        (componentIdeal (hU P) d hd)) = 1 := by
      apply Finset.prod_eq_one
      intro P _
      rw [Ideal.one_eq_top]
      change Ideal.map (algebraMap R (Localization.AtPrime Q))
        (componentIdeal (hU P) d hd) = ⊤
      simpa only [Q'] using
        (componentIdeal_spec (hU P) d hd).map_not_mem Q' (by
        intro h
        exact hQS ((Set.mem_singleton_iff.mp h).symm ▸ P.property))
    rw [hprod]
    have hdQ : d ∉ Q := fun h => hQS (hsupp Q' h)
    simpa [Ideal.map_span] using (Ideal.span_singleton_eq_top.mpr
      ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr hdQ)).symm

/-- The actual Picard component classes of a supported source element cancel.
In additive notation this is precisely the zero-sum identity for these supported elements. -/
theorem prod_singleton_componentClassHom (S : Finset (MaximalSpectrum R))
    (π : S → R) (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (d : R⁰) (hsupp : ∀ P : MaximalSpectrum R, (d : R) ∈ P.asIdeal → P ∈ S) :
    (∏ P : S, componentClassHom (hU P) d) = 1 := by
  classical
  let hd := nonZeroDivisors.ne_zero d.property
  let I : (FractionalIdeal R⁰ (FractionRing R))ˣ := ∏ P : S, componentUnit (hU P) d hd
  have hI : (I : FractionalIdeal R⁰ (FractionRing R)) = Ideal.span {(d : R)} := by
    change (Units.coeHom (FractionalIdeal R⁰ (FractionRing R)))
      (∏ P : S, componentUnit (hU P) d hd) = _
    rw [map_prod]
    change (∏ P : S, (componentUnit (hU P) d hd : FractionalIdeal R⁰ (FractionRing R))) = _
    simp only [componentUnit_coe]
    change (∏ P : S, (FractionalIdeal.coeIdealHom R⁰ (FractionRing R))
      (componentIdeal (hU P) d hd)) = _
    rw [← map_prod, prod_singleton_componentIdeal S π hU d hd hsupp]
    rfl
  have hclass : ClassGroup.mk (FractionRing R) I = 1 :=
    (ClassGroup.mk_eq_one_of_coe_ideal hI).mpr ⟨d, hd, rfl⟩
  simpa only [I, map_prod, componentClassHom, MonoidHom.coe_mk, OneHom.coe_mk] using hclass

/-- Local association on the chosen region identifies the actual source classes. -/
theorem componentClassHom_eq_of_local_associated {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (a b : R⁰)
    (hab : ∀ P ∈ U, Associated (algebraMap R (Localization.AtPrime P.asIdeal) (a : R))
      (algebraMap R (Localization.AtPrime P.asIdeal) (b : R))) :
    componentClassHom hU a = componentClassHom hU b := by
  have hu : componentUnit hU a (nonZeroDivisors.ne_zero a.property) =
      componentUnit hU b (nonZeroDivisors.ne_zero b.property) := by
    apply Units.ext
    simpa only [componentUnit_coe] using congrArg
      (fun I : Ideal R => (I : FractionalIdeal R⁰ (FractionRing R)))
      (componentIdeal_eq_of_local_associated hU a b
        (nonZeroDivisors.ne_zero a.property) (nonZeroDivisors.ne_zero b.property) hab)
  exact congrArg (ClassGroup.mk (FractionRing R)) hu

/-- A fraction represented by locally associated source numerator and denominator
has trivial actual component class. -/
theorem componentFractionClassHom_div_eq_one {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (a b : R⁰)
    (hab : ∀ P ∈ U, Associated (algebraMap R (Localization.AtPrime P.asIdeal) (a : R))
      (algebraMap R (Localization.AtPrime P.asIdeal) (b : R))) :
    componentFractionClassHom (K := K) hU
      (sourceNonzeroToFractionUnits a / sourceNonzeroToFractionUnits b) = 1 := by
  simp only [map_div, componentFractionClassHom_source,
    componentClassHom_eq_of_local_associated hU a b hab, div_self']

/-- The actual singleton component class kills every unit of its maximal
localization, after the canonical embedding into the fraction field. -/
theorem componentFractionClassHom_localUnit (P : MaximalSpectrum R) {π : R}
    (hU : IsClopenInFiber π {P})
    [Algebra (Localization.AtPrime P.asIdeal) K]
    [IsScalarTower R (Localization.AtPrime P.asIdeal) K]
    (u : (Localization.AtPrime P.asIdeal)ˣ) :
    componentFractionClassHom (K := K) hU
      (Units.map (algebraMap (Localization.AtPrime P.asIdeal) K).toMonoidHom u) = 1 := by
  let L := Localization.AtPrime P.asIdeal
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.asIdeal.primeCompl (u : L)
  have hbunit : IsUnit (algebraMap R L (b : R)) := IsLocalization.map_units L b
  have haunit : IsUnit (algebraMap R L a) := hab ▸ u.isUnit.mul hbunit
  have haP : a ∉ P.asIdeal := (IsLocalization.AtPrime.isUnit_to_map_iff L P.asIdeal a).mp haunit
  have hbP : (b : R) ∉ P.asIdeal := b.property
  have ha0 : a ≠ 0 := by intro h; exact haP (h ▸ P.asIdeal.zero_mem)
  have hb0 : (b : R) ≠ 0 := by intro h; exact hbP (h ▸ P.asIdeal.zero_mem)
  let a' : R⁰ := ⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩
  let b' : R⁰ := ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩
  have he : Units.map (algebraMap L K).toMonoidHom u =
      sourceNonzeroToFractionUnits a' / sourceNonzeroToFractionUnits b' := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val]
    change algebraMap L K (u : L) = algebraMap R K a / algebraMap R K (b : R)
    apply (eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0)).mpr
    have h := congrArg (algebraMap L K) hab
    rw [IsScalarTower.algebraMap_apply R L K, IsScalarTower.algebraMap_apply R L K]
    simpa only [map_mul] using h
  rw [he, map_div, componentFractionClassHom_source, componentFractionClassHom_source]
  rw [componentClassHom_eq_one_of_avoid hU a' (by
    intro Q hQ
    simpa only [Set.mem_singleton_iff.mp hQ] using haP),
    componentClassHom_eq_one_of_avoid hU b' (by
      intro Q hQ
      simpa only [Set.mem_singleton_iff.mp hQ] using hbP)]
  exact div_self' _

end HereditaryAtomicity.DVRBase
