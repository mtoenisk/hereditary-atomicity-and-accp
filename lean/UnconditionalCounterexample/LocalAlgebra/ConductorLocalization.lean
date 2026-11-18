import UnconditionalCounterexample.RadicalConductor
import Mathlib.RingTheory.Localization.Ideal

/-!
# Conductor transport through polynomial representatives

If localization denominators are already units after quotienting by an actual
ideal contained in a subring, conductor formation commutes with polynomial
pullback. Extending that pullback conductor recovers the localized conductor.
These statements use literal ideal containment and ordinary algebraic quotients.
-/

namespace UnconditionalCounterexample.LocalAlgebra

open RadicalConductor

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Conductor formation commutes with pullback when the target is covered by
image representatives modulo an actual ideal inside the target subring. -/
theorem conductorIdeal_comap_of_representatives
    (f : R →+* S) (T : Subring S) (J : Ideal S)
    (hJ : ∀ x ∈ J, x ∈ T)
    (hrep : ∀ s : S, ∃ r : R, s - f r ∈ J) :
    conductorIdeal (T.comap f) = (conductorIdeal T).comap f := by
  ext x
  constructor
  · intro hx
    change ∀ r : R, f (x * r) ∈ T at hx
    change ∀ s : S, f x * s ∈ T
    intro s
    obtain ⟨r, hr⟩ := hrep s
    have hprod : f x * f r ∈ T := by simpa only [map_mul] using hx r
    have herror : f x * (s - f r) ∈ T := hJ _ (J.mul_mem_left _ hr)
    have hsum := T.add_mem herror hprod
    simpa only [mul_sub, sub_add_cancel] using hsum
  · intro hx r
    change f (x * r) ∈ T
    rw [map_mul]
    exact hx (f r)

/-- Surjectivity after quotienting gives literal representatives modulo J. -/
theorem representatives_of_quotient_surjective
    (f : R →+* S) (J : Ideal S)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    ∀ s : S, ∃ r : R, s - f r ∈ J := by
  intro s
  obtain ⟨r, hr⟩ := hsurj (Ideal.Quotient.mk J s)
  refine ⟨r, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ?_⟩
  exact hr.symm

theorem conductorIdeal_comap_of_quotient_surjective
    (f : R →+* S) (T : Subring S) (J : Ideal S)
    (hJ : ∀ x ∈ J, x ∈ T)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    conductorIdeal (T.comap f) = (conductorIdeal T).comap f :=
  conductorIdeal_comap_of_representatives f T J hJ
    (representatives_of_quotient_surjective f J hsurj)

section Localization

variable [Algebra R S] (M : Submonoid R) [IsLocalization M S]

/-- If all localization denominators are units in R/I, localization leaves
the quotient unchanged, so every localized class has a polynomial representative. -/
theorem quotient_surjective_of_denominators_units (I : Ideal R)
    (hunit : ∀ m : M, IsUnit (Ideal.Quotient.mk I (m : R))) :
    Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap R S))).comp (algebraMap R S)) := by
  let e : (R ⧸ I) ≃ₐ[R ⧸ I] (S ⧸ I.map (algebraMap R S)) :=
    IsLocalization.atUnits (R ⧸ I) (Algebra.algebraMapSubmonoid (R ⧸ I) M)
      (by rintro y ⟨x, hx, rfl⟩; exact hunit ⟨x, hx⟩)
  intro z
  obtain ⟨q, hq⟩ := e.surjective z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨r, hq⟩

theorem conductorIdeal_comap_localization (T : Subring S) (I : Ideal R)
    (hI : ∀ x ∈ I.map (algebraMap R S), x ∈ T)
    (hunit : ∀ m : M, IsUnit (Ideal.Quotient.mk I (m : R))) :
    conductorIdeal (T.comap (algebraMap R S)) =
      (conductorIdeal T).comap (algebraMap R S) :=
  conductorIdeal_comap_of_quotient_surjective _ T _ hI
    (quotient_surjective_of_denominators_units M I hunit)

/-- The localized conductor is recovered from the polynomial pullback.
This uses actual ideal containment, not closure membership. -/
theorem conductorIdeal_eq_map_comap_localization (T : Subring S) (I : Ideal R)
    (hI : ∀ x ∈ I.map (algebraMap R S), x ∈ T)
    (hunit : ∀ m : M, IsUnit (Ideal.Quotient.mk I (m : R))) :
    conductorIdeal T = (conductorIdeal (T.comap (algebraMap R S))).map
      (algebraMap R S) := by
  rw [conductorIdeal_comap_localization M T I hI hunit]
  exact (IsLocalization.map_under M S (conductorIdeal T)).symm

end Localization

end UnconditionalCounterexample.LocalAlgebra
