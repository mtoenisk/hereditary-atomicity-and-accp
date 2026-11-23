import UnconditionalCounterexample.Variations.MultivariateSelectionModels
import UnconditionalCounterexample.Variations.MultivariateSelectionSites

/-! # Integral models for a single chronological polynomial entry -/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection.Entry

open MvPolynomial GuardSupport MultivariateInfinity

variable {r : ℕ} {M : Type*}

theorem good_model (u : Entry r M) (n : ℕ) (p : PrimeIndex) (S : Finset PrimeIndex)
    (hs : ∀ m v, v.Prime → v ∣ (u.lower.coeff m).den → ∃ i : S, v = i.val.val) (hp : p ∉ S) :
    ∃ Q : MvPolynomial (Fin (r+1)) ℤ_[p.val],
      MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) Q = MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (u.raw n) ∧
      MvPolynomial.map PadicInt.toZMod Q ≠ 0 := by
  classical
  obtain ⟨q',hq'⟩ := exists_integral_model (fun i : S => i.val.val) u.lower hs p.val
    (fun i hi => hp ((Subtype.ext hi : i.val = p) ▸ i.property))
  let l : MvPolynomial (Fin (r+1)) ℤ_[p.val] := ∑ j, C ((n : ℤ_[p.val]) ^ j.val) * X j
  let F := l ^ u.degree + q'
  have hF : MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) F =
      MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (u.raw n) := by
    simp only [F, Entry.raw, map_add, map_pow, map_vandermonde, hq']
    simp [l,vandermondeForm]
  refine ⟨F,hF,fun hz => ?_⟩
  let m := Finsupp.single (0 : Fin (r+1)) u.degree
  have ht : (u.raw n).coeff m = 1 := axis_top_coeff r n _ _ u.lower_lt
  have hc := congrArg (fun f : MvPolynomial (Fin (r+1)) ℚ_[p.val] => f.coeff m) hF
  simp only [coeff_map,ht,map_one] at hc
  have ht' : F.coeff m = 1 := Subtype.ext hc
  have hh := congrArg (fun f : MvPolynomial (Fin (r+1)) (ZMod p.val) => f.coeff m) hz
  change (MvPolynomial.map PadicInt.toZMod F).coeff m = 0 at hh
  rw [coeff_map,ht',map_one] at hh
  exact one_ne_zero hh

private theorem residue_one_zero (v : PrimeIndex) (a : ℤ_[v.val]) {m : (Fin (r+1)) →₀ ℕ}
    (hr : PadicInt.toZModPow 2 a = if m = 0 then (v.val : ZMod (v.val^2)) else 0) :
    PadicInt.toZModPow 1 a = 0 := by
  let φ := ZMod.castHom (pow_dvd_pow v.val (show 1 ≤ 2 by decide)) (ZMod (v.val^1))
  have hφ : φ.comp (PadicInt.toZModPow 2) = PadicInt.toZModPow 1 := PadicInt.zmod_cast_comp_toZModPow 1 2 (by decide)
  rw [← hφ, RingHom.comp_apply, hr]
  split_ifs
  · rw [map_natCast, ZMod.natCast_eq_zero_iff, pow_one]
  · exact map_zero _

theorem aux_model (u : Entry r M) (n : ℕ) (ell : PrimeIndex)
    (hm : ∀ m, HasAuxiliaryResidue ell.val (u.lower.coeff m) (if m = 0 then (ell.val : ZMod (ell.val^2)) else 0)) :
    ∃ Q : MvPolynomial (Fin (r+1)) ℤ_[ell.val],
      MvPolynomial.map (algebraMap ℤ_[ell.val] ℚ_[ell.val]) Q = MvPolynomial.map (algebraMap ℚ ℚ_[ell.val]) (u.raw n) ∧
      MvPolynomial.map (PadicInt.toZModPow 1) Q =
        (∑ j : Fin (r+1), C ((n : ZMod (ell.val^1)) ^ j.val) * X j) ^ u.degree := by
  classical
  let q := u.lower
  choose a ha hr using hm
  let q' : MvPolynomial (Fin (r+1)) ℤ_[ell.val] := ∑ m ∈ q.support, monomial m (a m)
  have hq' : MvPolynomial.map (algebraMap ℤ_[ell.val] ℚ_[ell.val]) q' = MvPolynomial.map (algebraMap ℚ ℚ_[ell.val]) q := by
    conv_rhs => rw [q.as_sum]
    simp only [q',map_sum,map_monomial]
    exact Finset.sum_congr rfl fun m _ => congrArg (monomial m) (ha m)
  have hred : MvPolynomial.map (PadicInt.toZModPow 1) q' = 0 := by
    have hzero (m) : PadicInt.toZModPow 1 (a m) = 0 := residue_one_zero ell _ (hr m)
    simp only [q',map_sum,map_monomial,hzero,monomial_zero,Finset.sum_const_zero]
  let l : MvPolynomial (Fin (r+1)) ℤ_[ell.val] := ∑ j, C ((n : ℤ_[ell.val]) ^ j.val) * X j
  refine ⟨l ^ u.degree + q', ?_, ?_⟩
  · change MvPolynomial.map (algebraMap ℤ_[ell.val] ℚ_[ell.val]) (l ^ u.degree + q') =
      MvPolynomial.map (algebraMap ℚ ℚ_[ell.val]) (vandermondeForm (r+1) n ^ u.degree + q)
    simp only [map_add,map_pow,hq',map_vandermonde]
    simp [l,vandermondeForm]
  · simp [map_add,map_pow,hred,l]

end UnconditionalCounterexample.MultivariateSelection.Entry
