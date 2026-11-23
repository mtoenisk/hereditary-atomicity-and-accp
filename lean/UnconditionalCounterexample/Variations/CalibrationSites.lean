import UnconditionalCounterexample.Variations.CalibrationLifts
import UnconditionalCounterexample.Variations.CalibrationPrimes
import UnconditionalCounterexample.Variations.UnivariateSelection

/-! # Paired auxiliary fibres calibrating a retained polynomial -/

namespace UnconditionalCounterexample.Calibration

open Polynomial GuardSupport
open Variations.Univariate

/-- The frozen polynomials are represented by their product `G`. Its
evaluation is a unit on both branches of this auxiliary fibre. Only the
primary has positive order on the polynomial being calibrated. -/
structure AuxiliarySite (f G : ℤ[X]) (l stage : ℕ) where
  prime : PrimeIndex
  guard : PaperGuardStages.Guard prime
  birth : guard.birth = stage
  primary : Primary prime guard.value
  value_ne_zero : aeval primary.val.val f ≠ 0
  value_order : (aeval primary.val.val f).valuation = l
  guard_unit : IsUnit (aeval guard.value f)
  frozen_primary : IsUnit (aeval primary.val G)
  frozen_guard : IsUnit (aeval guard.value G)

/-- Integral polynomial units contribute zero to the signed order. -/
theorem order_zero_of_unit {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) (g : ℤ[X])
    (hx : IsUnit (aeval x g)) : (aeval x.val g).valuation = 0 := by
  have he : aeval x.val g = ((aeval x g : ℤ_[p]) : ℚ_[p]) :=
    aeval_algebraMap_apply ℚ_[p] x g
  have hn : ‖aeval x.val g‖ = 1 := he ▸ PadicInt.isUnit_iff.mp hx
  have hz : aeval x.val g ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
  simpa using EvaluationChoices.valuation_eq_of_norm_eq p hz (one_ne_zero : (1 : ℚ_[p]) ≠ 0)
    (hn.trans norm_one.symm)

theorem AuxiliarySite.paired_order {f G : ℤ[X]} {l stage : ℕ} (s : AuxiliarySite f G l stage) :
    (aeval s.primary.val.val f).valuation - (aeval s.guard.value.val f).valuation = l ∧
      (aeval s.primary.val.val G).valuation - (aeval s.guard.value.val G).valuation = 0 := by
  simp [s.value_order, order_zero_of_unit _ _ s.guard_unit,
    order_zero_of_unit _ _ s.frozen_primary, order_zero_of_unit _ _ s.frozen_guard]

/-- A fresh auxiliary prime can be allocated after a finite prefix has been
fixed, for any positive target order. The resulting fibre has the same type
of primary and guard as the univariate selector. -/
theorem exists_auxiliary_site (f G : ℤ[X]) (hd : f.natDegree ≠ 0)
    (hprim : f.IsPrimitive) (hirr : Irreducible f) (hG : G ≠ 0)
    (hc : IsCoprime (f.map (Int.castRingHom ℚ)) (G.map (Int.castRingHom ℚ)))
    (cutoff stage l : ℕ) (hl : 0 < l) :
    ∃ s : AuxiliarySite f G l stage, cutoff < s.prime.val := by
  classical
  let H := f * G
  have hH : H ≠ 0 := mul_ne_zero hirr.ne_zero hG
  obtain ⟨p, a, hp, hbound, hroot, hsimple, hfrozen⟩ := exists_simple_root_prime f G hd hprim
    hirr hc (max cutoff (max H.leadingCoeff.natAbs (2 ^ (4 + H.natDegree))))
  have : Fact p.Prime := ⟨hp⟩
  have hcoeff : H.leadingCoeff.natAbs < p := by omega
  have hdegree : 2 ^ (4 + H.natDegree) < p := by omega
  obtain ⟨α, ht, hres, hnonzero, horder⟩ :=
    exists_transcendental_lift p f a l hl hroot hsimple
  let φ := Int.castRingHom (ZMod p)
  have hαunit : IsUnit (aeval α G) := by
    apply GuardSupport.intPolynomial_eval_unit_of_residue_nonzero
    rw [hres]
    have h := eval₂_at_apply (p := G) φ a
    exact h.trans_ne (fun hz => hfrozen ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
  have hred := GuardStages.map_ne_zero_of_leadingCoeff_natAbs_lt hH hcoeff
  obtain ⟨w, hwl, hwu, hw1, hwp, hw⟩ := GuardResidues.exists_guard_residue ({()} : Finset Unit)
    (fun _ => H.map φ) (fun _ _ => hred) (by
      simpa [φ, GuardStages.natDegree_map_eq_of_leadingCoeff_natAbs_lt hH hcoeff] using hdegree)
  have hwp0 : (w : ZMod p) ≠ 0 := by
    exact fun h => Nat.not_dvd_of_pos_of_lt (by omega) hwp ((ZMod.natCast_eq_zero_iff w p).mp h)
  obtain ⟨β, hβt, hβu, hβr⟩ := GuardStages.exists_transcendental_lift (w : ZMod p) hwp0
  have hβ : H.eval₂ φ (PadicInt.toZMod β) ≠ 0 := by
    simpa [hβr, eval_map] using hw () (by simp)
  have hFβ : f.eval₂ φ (PadicInt.toZMod β) ≠ 0 := (mul_ne_zero_iff.mp
    (show f.eval₂ φ (PadicInt.toZMod β) * G.eval₂ φ (PadicInt.toZMod β) ≠ 0 by
      simpa [H] using hβ)).1
  have hunit : IsUnit (aeval β f) ∧ IsUnit (aeval β G) := by
    have h := intPolynomial_eval_unit_of_residue_nonzero H β hβ
    change IsUnit (aeval β H) at h
    simpa [H] using h
  have hdiff : PadicInt.toZMod α ≠ PadicInt.toZMod β := by
    intro heq
    apply hFβ
    rw [← heq, hres]
    exact (eval₂_at_apply (p := f) φ a).trans
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hroot)
  let g : PaperGuardStages.Guard (⟨p, hp⟩ : PrimeIndex) :=
    ⟨β, hβt, hβu, w, hβr, stage, fun _ => ⟨hwl, hwu⟩⟩
  exact ⟨⟨⟨p, hp⟩, g, rfl, ⟨α, ht, hdiff⟩, hnonzero, horder, hunit.1, hαunit, hunit.2⟩,
    (le_max_left ..).trans_lt hbound⟩

end UnconditionalCounterexample.Calibration
