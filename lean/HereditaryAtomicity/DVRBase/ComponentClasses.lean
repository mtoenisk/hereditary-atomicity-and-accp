import HereditaryAtomicity.DVRBase.ClopenComponents

/-!
# Actual ideal classes and principal powers of clopen components

`ClassGroup R` is used in its general-domain meaning: invertible fractional
ideals modulo principal fractional ideals. No Dedekind assumption is needed.
-/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDomain R]

/-- The genuine Picard ideal class of an invertible integral ideal. -/
def invertibleIdealClass (I : Ideal R)
    (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) : ClassGroup R :=
  ClassGroup.mk (FractionRing R) hI.unit

/-- A killed ideal class gives an actual nonzero source generator of its power. -/
theorem exists_generator_pow_of_class_eq_one (I : Ideal R)
    (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) (h : ℕ)
    (hclass : invertibleIdealClass I hI ^ h = 1) :
    ∃ c : R, c ≠ 0 ∧ I ^ h = Ideal.span {c} := by
  apply (ClassGroup.mk_eq_one_of_coe_ideal
    (I := hI.unit ^ h) (I' := I ^ h) ?_).mp
  · simpa only [invertibleIdealClass, map_pow] using hclass
  · simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, FractionalIdeal.coeIdeal_pow]

variable [Ring.KrullDimLE 1 R]

/-- Invertibility of the component is proved by its actual complementary ideal. -/
theorem componentIdeal_isUnit {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0) :
    IsUnit (componentIdeal hU d hd : FractionalIdeal R⁰ (FractionRing R)) :=
  (componentIdeal_spec hU d hd).comaximal.isUnit hd

/-- The invertible fractional ideal of a nonzero source component. -/
def componentUnit {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0) :
    (FractionalIdeal R⁰ (FractionRing R))ˣ :=
  (componentIdeal_isUnit hU d hd).unit

@[simp] theorem componentUnit_coe {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0) :
    (componentUnit hU d hd : FractionalIdeal R⁰ (FractionRing R)) = componentIdeal hU d hd :=
  IsUnit.unit_spec _

/-- Actual component ideal classes form a multiplicative map on nonzero source elements. -/
def componentClassHom {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) : R⁰ →* ClassGroup R where
  toFun d := ClassGroup.mk (FractionRing R) (componentUnit hU d (nonZeroDivisors.ne_zero d.property))
  map_one' := by
    have hu : componentUnit hU 1 one_ne_zero = 1 := by
      apply Units.ext
      simp [componentIdeal_one]
    change ClassGroup.mk (FractionRing R) (componentUnit hU 1 _) = 1
    rw [hu, map_one]
  map_mul' a b := by
    have hu : componentUnit hU (a * b) (mul_ne_zero (nonZeroDivisors.ne_zero a.property)
        (nonZeroDivisors.ne_zero b.property)) =
        componentUnit hU a (nonZeroDivisors.ne_zero a.property) *
          componentUnit hU b (nonZeroDivisors.ne_zero b.property) := by
      apply Units.ext
      simp only [componentUnit_coe, Units.val_mul]
      rw [componentIdeal_mul, FractionalIdeal.coeIdeal_mul]
    change ClassGroup.mk (FractionRing R) (componentUnit hU (a * b) _) = _
    rw [hu, map_mul]

/-- Torsion of the genuine component class gives a global nonzero element
with the specified local principal power, and a unit outside the region. -/
theorem exists_component_generator_pow {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0) (h : ℕ)
    (hclass : componentClassHom hU ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩ ^ h = 1) :
    ∃ c : R, c ≠ 0 ∧
      (∀ P : MaximalSpectrum R, P ∈ U →
        Associated (algebraMap R (Localization.AtPrime P.asIdeal) c)
          ((algebraMap R (Localization.AtPrime P.asIdeal) d) ^ h)) ∧
      (∀ P : MaximalSpectrum R, P ∉ U →
        IsUnit (algebraMap R (Localization.AtPrime P.asIdeal) c)) := by
  obtain ⟨c, hc, hIc⟩ := exists_generator_pow_of_class_eq_one
    (componentIdeal hU d hd) (componentIdeal_isUnit hU d hd) h hclass
  refine ⟨c, hc, ?_, ?_⟩
  · intro P hP
    apply Ideal.span_singleton_eq_span_singleton.mp
    have he := congrArg (Ideal.map (algebraMap R (Localization.AtPrime P.asIdeal))) hIc
    rw [Ideal.map_pow, (componentIdeal_spec hU d hd).map_mem P hP] at he
    simpa [Ideal.map_span, Ideal.span_singleton_pow] using he.symm
  · intro P hP
    apply Ideal.span_singleton_eq_top.mp
    have he := congrArg (Ideal.map (algebraMap R (Localization.AtPrime P.asIdeal))) hIc
    rw [Ideal.map_pow, (componentIdeal_spec hU d hd).map_not_mem P hP] at he
    have htop : (⊤ : Ideal (Localization.AtPrime P.asIdeal)) ^ h = ⊤ := by
      rw [← Ideal.one_eq_top, one_pow]
    rw [htop] at he
    simpa only [Ideal.map_span, Set.image_singleton] using he.symm


/-- Positive principal powers retain exactly the selected source support. -/
theorem exists_component_generator_pow_support {π : R} {U : Set (MaximalSpectrum R)}
    (hU : IsClopenInFiber π U) (d : R) (hd : d ≠ 0) (h : ℕ) (hh : 0 < h)
    (hclass : componentClassHom hU ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩ ^ h = 1) :
    ∃ c : R, c ≠ 0 ∧
      (∀ P : MaximalSpectrum R, P ∈ U →
        Associated (algebraMap R (Localization.AtPrime P.asIdeal) c)
          ((algebraMap R (Localization.AtPrime P.asIdeal) d) ^ h)) ∧
      (∀ P : MaximalSpectrum R, c ∈ P.asIdeal ↔ P ∈ U ∧ d ∈ P.asIdeal) := by
  obtain ⟨c, hc, hassoc, hunit⟩ := exists_component_generator_pow hU d hd h hclass
  refine ⟨c, hc, hassoc, ?_⟩
  intro P
  by_cases hP : P ∈ U
  · have hu := (hassoc P hP).isUnit_iff.trans (isUnit_pow_iff (Nat.ne_of_gt hh))
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P.asIdeal) P.asIdeal c,
      IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P.asIdeal) P.asIdeal d] at hu
    change (c ∉ P.asIdeal ↔ d ∉ P.asIdeal) at hu
    simpa only [hP, true_and, not_not] using not_congr hu
  · have hcP : c ∉ P.asIdeal := (IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime P.asIdeal) P.asIdeal c).mp (hunit P hP)
    simp only [hcP, hP, false_and]

omit [Ring.KrullDimLE 1 R] in
/-- The subgroup generated by actual comaximal factors of nonzero principal ideals. -/
def comaximalFactorClassGroup : Subgroup (ClassGroup R) :=
  Subgroup.closure {x | ∃ (d : R) (hd : d ≠ 0) (I : Ideal R)
    (hI : IsComaximalFactor d I), x = invertibleIdealClass I (hI.isUnit hd)}

/-- Every selected component class belongs to the source-defined Picard subgroup. -/
theorem componentClassHom_mem_comaximalFactorClassGroup {π : R}
    {U : Set (MaximalSpectrum R)} (hU : IsClopenInFiber π U) (d : R⁰) :
    componentClassHom hU d ∈ comaximalFactorClassGroup (R := R) := by
  apply Subgroup.subset_closure
  exact ⟨d, nonZeroDivisors.ne_zero d.property, componentIdeal hU d _,
    (componentIdeal_spec hU d _).comaximal, rfl⟩

/-- A common exponent on the actual comaximal-factor subgroup kills every component class. -/
theorem componentClassHom_pow_eq_one_of_subgroup_bound (h : ℕ)
    (hbound : ∀ x ∈ comaximalFactorClassGroup (R := R), x ^ h = 1)
    {π : R} {U : Set (MaximalSpectrum R)} (hU : IsClopenInFiber π U) (d : R⁰) :
    componentClassHom hU d ^ h = 1 :=
  hbound _ (componentClassHom_mem_comaximalFactorClassGroup hU d)

end HereditaryAtomicity.DVRBase
