import UnconditionalCounterexample.Target
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Maximal stalks of overrings of almost Dedekind domains

Given a maximal ideal of an embedded overring, place its contraction inside
a maximal ideal of the smaller ring. The resulting inclusion of local rings
exhibits the larger stalk as an overring of a DVR. Its nonzero maximal ideal
excludes the fraction field, so the two local rings coincide.

The localization-containment argument follows
`HereditaryAtomicity.Pruefer.ofPrime_le_of_isUnit`.
-/

namespace UnconditionalCounterexample.Hierarchy

variable {K : Type*} [Field K]

private theorem primeStalk_le (A U : Subring K) (P : Ideal A) [P.IsPrime]
    (hAU : A ≤ U) (hunits : ∀ s : A, s ∉ P → IsUnit (Subring.inclusion hAU s)) :
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

/-- A maximal stalk of a nonfield subring is a proper subring of the ambient field. -/
private theorem maximalStalk_ne_top (S : Subring K) (hS : ¬ IsField S)
    (Q : Ideal S) [hQ : Q.IsMaximal] : (LocalSubring.ofPrime S Q).toSubring ≠ ⊤ := by
  have hQ0 : Q ≠ ⊥ := fun h => hS (Ring.isField_iff_maximal_bot.mpr (h ▸ hQ))
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  let B := (LocalSubring.ofPrime S Q).toSubring
  intro htop
  have hqK : (q : K) ≠ 0 := fun h => hq0 (Subtype.ext h)
  have hu : IsUnit (algebraMap S B q) := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨⟨(q : K)⁻¹, by rw [show B = ⊤ from htop]; trivial⟩,
      Subtype.ext (mul_inv_cancel₀ hqK)⟩
  exact ((IsLocalization.AtPrime.isUnit_to_map_iff B Q q).mp hu) hq

/-- Every nonfield overring in the fraction field of an almost Dedekind domain
has discrete valuation rings at all its maximal ideals. -/
theorem almostDedekind_overring (R S : Subring K) [IsFractionRing R K]
    (hRS : R ≤ S) (hR : IsAlmostDedekindDomain R) (hS : ¬ IsField S) :
    IsAlmostDedekindDomain S := by
  intro Q hQ
  let P := Q.comap (Subring.inclusion hRS)
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime))
  let A := (LocalSubring.ofPrime R M).toSubring
  let B := (LocalSubring.ofPrime S Q).toSubring
  let : IsDiscreteValuationRing (Localization.AtPrime M) := hR M
  let : IsDiscreteValuationRing A :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (LocalSubring.ofPrimeEquiv R M)
  let : IsFractionRing A K := by
    apply IsFractionRing.of_field
    intro z
    obtain ⟨a,b,_,hz⟩ := IsFractionRing.div_surjective R z
    exact ⟨⟨a, LocalSubring.le_ofPrime R M a.property⟩,
      ⟨b, LocalSubring.le_ofPrime R M b.property⟩, hz.symm⟩
  have hRB : R ≤ B := hRS.trans (LocalSubring.le_ofPrime S Q)
  have hAB : A ≤ B := by
    apply primeStalk_le R B M hRB
    intro s hs
    change IsUnit (algebraMap S B (Subring.inclusion hRS s))
    exact IsLocalization.map_units B
      (⟨Subring.inclusion hRS s, fun h => hs (hPM h)⟩ : Q.primeCompl)
  let V := ValuationSubring.ofSubring A (fun x => by
    rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl (ha ▸ a.property)
    · exact Or.inr (ha ▸ a.property))
  let W := ValuationSubring.ofLE V B hAB
  let : Ring.KrullDimLE 1 V := inferInstanceAs (Ring.KrullDimLE 1 A)
  have hWV : V = W := ValuationSubring.eq_of_le_of_ne_top V (show V ≤ W from hAB)
    (fun h => maximalStalk_ne_top S hS Q (congrArg ValuationSubring.toSubring h))
  have hEq : A = B := congrArg ValuationSubring.toSubring hWV
  let : IsDiscreteValuationRing B := hEq ▸ inferInstanceAs (IsDiscreteValuationRing A)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (LocalSubring.ofPrimeEquiv S Q).symm

end UnconditionalCounterexample.Hierarchy
