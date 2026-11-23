import UnconditionalCounterexample.Variations.MultivariateSelectionSites

/-! # Finite exceptional primes for mixed stage polynomials -/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport

variable {r : ℕ}

private def coefficientBound (f : Poly r) : ℕ :=
  f.support.sup fun m => max (f.coeff m).den ((f.coeff m)⁻¹).den

/-- All nonzero coefficients and their inverses are integral outside this
finite set. Thus any subsequently assigned guard can screen the polynomial. -/
def badPrimes (f : Poly r) : Finset PrimeIndex :=
  (Finset.range (coefficientBound f + 1)).subtype Nat.Prime

theorem good_model_of_not_mem_badPrimes (f : Poly r) (hf : f ≠ 0) (p : PrimeIndex)
    (hp : p ∉ badPrimes f) :
    ∃ g : MvPolynomial (Fin (r+1)) ℤ_[p.val],
      MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) g = MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) f ∧
      MvPolynomial.map PadicInt.toZMod g ≠ 0 := by
  classical
  have hlt : coefficientBound f < p.val := by
    simpa [badPrimes, Nat.lt_succ_iff] using hp
  have bound (m) (hm : m ∈ f.support) :
      max (f.coeff m).den ((f.coeff m)⁻¹).den < p.val := (Finset.le_sup (f := fun m =>
        max (f.coeff m).den ((f.coeff m)⁻¹).den) hm).trans_lt hlt
  have int (a : ℚ) (ha : a.den < p.val) : ‖(a : ℚ_[p.val])‖ ≤ 1 :=
    Padic.norm_rat_le_one fun h => ha.not_ge (Nat.le_of_dvd a.den_pos h)
  have hi (m) : ‖((f.coeff m : ℚ) : ℚ_[p.val])‖ ≤ 1 := by
    by_cases hm : m ∈ f.support
    · exact int _ ((le_max_left ..).trans_lt (bound m hm))
    · simp [notMem_support_iff.mp hm]
  let a (m) : ℤ_[p.val] := ⟨_,hi m⟩
  let g := ∑ m ∈ f.support, monomial m (a m)
  have hmodel : MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) g =
      MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) f := by
    conv_rhs => rw [f.as_sum]
    simp only [g,map_sum,map_monomial]
    rfl
  obtain ⟨m,hm⟩ := MvPolynomial.exists_coeff_ne_zero hf
  let ainv : ℤ_[p.val] := ⟨((f.coeff m)⁻¹ : ℚ),int _ ((le_max_right ..).trans_lt
    (bound m (mem_support_iff.mpr hm)))⟩
  have hv : (g.coeff m : ℚ_[p.val]) = ((f.coeff m : ℚ) : ℚ_[p.val]) := by
    simpa [coeff_map] using congrArg (fun h : MvPolynomial (Fin (r+1)) ℚ_[p.val] => h.coeff m) hmodel
  have hunit : IsUnit (g.coeff m) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨ainv,Subtype.ext ?_⟩
    change (g.coeff m : ℚ_[p.val]) * (((f.coeff m)⁻¹ : ℚ) : ℚ_[p.val]) = 1
    rw [hv,← Rat.cast_mul,mul_inv_cancel₀ hm,Rat.cast_one]
  refine ⟨g,hmodel,fun hzero => (hunit.map PadicInt.toZMod).ne_zero ?_⟩
  simpa [coeff_map] using congrArg (fun h : MvPolynomial (Fin (r+1)) (ZMod p.val) => h.coeff m) hzero

end UnconditionalCounterexample.MultivariateSelection
