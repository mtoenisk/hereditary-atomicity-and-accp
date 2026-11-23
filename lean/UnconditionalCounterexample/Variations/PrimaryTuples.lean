import Mathlib.Algebra.MvPolynomial.Funext
import UnconditionalCounterexample.GuardStages
import UnconditionalCounterexample.Variations.IndependentTuples

/-!
# Fresh multivariate primary evaluations

A single integral tuple avoids the zeros of all finitely many nonzero
restrictions to the divisor t=0. A prime larger than their product value
preserves this avoidance. The independent p-adic lifts retain those unit
values and realize the specified positive valuation of t.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.IndependentTuples

open MvPolynomial GuardSupport

/-- A nonzero multivariate integer polynomial has an integer tuple on which
its value is nonzero. This also applies with no coordinates. -/
theorem exists_integer_value_ne_zero {n : ℕ} {f : MvPolynomial (Fin n) ℤ} (hf : f ≠ 0) :
    ∃ z : Fin n → ℤ, eval z f ≠ 0 := by
  by_contra! h
  exact hf (MvPolynomial.funext (fun z => by simp [h]))

/-- Unit evaluations on a new primary fibre and an exact valuation for its
first coordinate, with all coordinates algebraically independent. The
polynomials in `s` are the nonzero restrictions in the remaining variables. -/
theorem exists_fresh_primary_tuple (n k : ℕ) (hk : 0 < k)
    (s : Finset (MvPolynomial (Fin n) ℤ)) (hs : ∀ f ∈ s, f ≠ 0)
    (old : Finset PrimeIndex) (cutoff : ℕ) :
    ∃ (p : PrimeIndex) (a : Fin (n+1) → ℤ_[p.val]), cutoff < p.val ∧ p ∉ old ∧
      AlgebraicIndependent ℚ (fun i => (a i).val) ∧ ((a 0).val).valuation = k ∧ PadicInt.toZMod (a 0) = 0 ∧
      ∀ f ∈ s, IsUnit (eval₂Hom (Int.castRingHom ℤ_[p.val]) (fun i : Fin n => a i.succ) f) := by
  classical
  let F := ∏ f ∈ s, f
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
  obtain ⟨z, hz⟩ := exists_integer_value_ne_zero hF
  obtain ⟨p, hbig, hpold⟩ := GuardStages.exists_fresh_prime old (max cutoff (eval z F).natAbs)
  have hmod : ((eval z F : ℤ) : ZMod p.val) ≠ 0 := by
    intro h
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Int.natAbs_dvd_natAbs.mpr hd)
    simp only [Int.natAbs_natCast] at hle
    omega
  let c : Fin (n+1) → ℤ_[p.val] := Fin.cons ((p.val : ℤ_[p.val]) ^ k) (fun i => (z i : ℤ_[p.val]))
  have hp0 : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  let ε := ‖(p.val : ℚ_[p.val]) ^ k‖
  have hε : 0 < ε := norm_pos_iff.mpr (pow_ne_zero _ hp0)
  obtain ⟨a, hI, hclose⟩ := exists_padic_lifts p.val (n+1) c (fun _ => ε) (fun _ => hε)
  have hval : (a 0).val.valuation = k := by
    have hnear := (hclose 0).2
    change ‖(a 0).val - ((p.val : ℤ_[p.val]) ^ k).val‖ < ε at hnear
    rw [PadicInt.coe_pow, PadicInt.coe_natCast] at hnear
    have hn := Padic.norm_eq_of_norm_sub_lt_right hnear
    have hne : (a 0).val ≠ 0 := by
      exact norm_ne_zero_iff.mp (hn ▸ norm_ne_zero_iff.mpr (pow_ne_zero k hp0))
    rw [EvaluationChoices.valuation_eq_of_norm_eq p.val hne (pow_ne_zero k hp0) hn,
      Padic.valuation_pow, Padic.valuation_p, mul_one]
  have hzero : PadicInt.toZMod (a 0) = 0 := by
    rw [(hclose 0).1]
    simp [c, map_pow, Nat.ne_of_gt hk]
  let e : MvPolynomial (Fin n) ℤ →+* ℤ_[p.val] := eval₂Hom (Int.castRingHom ℤ_[p.val]) (fun i : Fin n => a i.succ)
  have hred : PadicInt.toZMod (e F) = (eval z F : ℤ) := by
    have he : PadicInt.toZMod.comp e = (Int.castRingHom (ZMod p.val)).comp (eval z) := by
      ext i
      · simp [e]
      · simpa [e] using ((hclose i.succ).1).trans (by simp [c] : PadicInt.toZMod (c i.succ) = (z i : ZMod p.val))
    exact DFunLike.congr_fun he F
  have hu : IsUnit (e F) := (padicInt_isUnit_iff_toZMod_ne_zero _).mpr (hred ▸ hmod)
  rw [show e F = ∏ f ∈ s, e f from map_prod e _ _] at hu
  exact ⟨p, a, (le_max_left _ _).trans_lt hbig, hpold, hI, hval, hzero, (fun f hf => isUnit_of_dvd_unit (Finset.dvd_prod_of_mem e hf) hu)⟩

/-- Restrict a polynomial to the first coordinate hyperplane. -/
def restrictToCentre (n : ℕ) : MvPolynomial (Fin (n+1)) ℤ →+* MvPolynomial (Fin n) ℤ :=
  eval₂Hom C (Fin.cons 0 X)

/-- A finite list of actual numerator polynomials stays invertible at the
fresh evaluation as soon as each restriction to the centre is nonzero. -/
theorem exists_screened_primary (n k : ℕ) (hk : 0 < k)
    (s : Finset (MvPolynomial (Fin (n+1)) ℤ)) (hs : ∀ f ∈ s, restrictToCentre n f ≠ 0)
    (old : Finset PrimeIndex) (cutoff : ℕ) :
    ∃ (p : PrimeIndex) (a : Fin (n+1) → ℤ_[p.val]), cutoff < p.val ∧ p ∉ old ∧
      AlgebraicIndependent ℚ (fun i => (a i).val) ∧ ((a 0).val).valuation = k ∧
      ∀ f ∈ s, IsUnit (eval₂Hom (Int.castRingHom ℤ_[p.val]) a f) := by
  classical
  let t := s.image (restrictToCentre n)
  have ht : ∀ g ∈ t, g ≠ 0 := by
    rintro _ hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    exact hs f hf
  obtain ⟨p, a, hcut, hfresh, hI, hval, hzero, hunit⟩ := exists_fresh_primary_tuple n k hk t ht old cutoff
  let ea := eval₂Hom (Int.castRingHom ℤ_[p.val]) a
  let ez := eval₂Hom (Int.castRingHom ℤ_[p.val]) (fun i : Fin n => a i.succ)
  have he : PadicInt.toZMod.comp ea = (PadicInt.toZMod.comp ez).comp (restrictToCentre n) := by
    ext i
    · simp [ea, ez, restrictToCentre]
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp [ea, ez, restrictToCentre, hzero]
      · simp [ea, ez, restrictToCentre]
  refine ⟨p, a, hcut, hfresh, hI, hval, fun f hf => ?_⟩
  apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
  exact (DFunLike.congr_fun he f) ▸ (padicInt_isUnit_iff_toZMod_ne_zero _).mp
    (hunit _ (Finset.mem_image.mpr ⟨f, hf, rfl⟩))

end UnconditionalCounterexample.Variations.IndependentTuples
