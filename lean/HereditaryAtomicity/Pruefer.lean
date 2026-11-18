import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Ideal.Height

/-! # Prüfer domains through their actual prime localizations -/

namespace HereditaryAtomicity

/-- A domain is Prüfer when every prime localization is a valuation ring. -/
def IsPrueferDomain (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime], ValuationRing (Localization.AtPrime P)

/-- Transport valuation divisibility through a ring equivalence. -/
theorem valuationRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] (e : R ≃+* S) (hS : ValuationRing S) : ValuationRing R := by
  let := hS
  exact Function.Surjective.valuationRing e.symm.toRingHom e.symm.surjective

variable {K : Type*} [Field K]

/-- A prime localization lies in any embedded overring in which all elements
outside that prime have become units. -/
theorem ofPrime_le_of_isUnit (A U : Subring K) (P : Ideal A) [P.IsPrime]
    (hAU : A ≤ U)
    (hunits : ∀ s : A, s ∉ P → IsUnit (Subring.inclusion hAU s)) :
    (LocalSubring.ofPrime A P).toSubring ≤ U := by
  let f : Localization.AtPrime P →+* U :=
    IsLocalization.lift (M := P.primeCompl) (g := Subring.inclusion hAU)
      (fun s => hunits s s.property)
  let e := LocalSubring.ofPrimeEquiv A P
  have heq : U.subtype.comp f = (LocalSubring.ofPrime A P).toSubring.subtype.comp
      e.toRingHom := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext a
    simp [f, e]
    rfl
  intro x hx
  let a := e.symm ⟨x, hx⟩
  have ha : (f a : K) = x := by
    have h := congrArg (fun g : Localization.AtPrime P →+* K => g a) heq
    change (f a : K) = (e a : K) at h
    simpa only [a, AlgEquiv.apply_symm_apply] using h
  exact ha ▸ (f a).property

end HereditaryAtomicity
