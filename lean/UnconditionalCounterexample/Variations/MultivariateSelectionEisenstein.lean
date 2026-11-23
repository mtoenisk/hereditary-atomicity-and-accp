import UnconditionalCounterexample.ShiftedEisenstein
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Irreducibility from a degree-preserving coordinate restriction

On the first coordinate axis the leading form of the stage polynomial is a monic
power of the variable. Lower coefficients modulo one auxiliary prime can
therefore impose Eisenstein on this univariate restriction. Since the
restriction preserves total degree, its irreducibility lifts to the entire
multivariate polynomial.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial Polynomial

variable {σ k : Type*} [Field k]

/-- Restrict to the coordinate axis on which all variables indexed by `some` vanish. -/
def axis : MvPolynomial (Option σ) k →+* Polynomial k :=
  (Polynomial.mapRingHom (MvPolynomial.constantCoeff : MvPolynomial σ k →+* k)).comp
    (optionEquivLeft k σ).toRingHom

theorem axis_coeff (f : MvPolynomial (Option σ) k) (n : ℕ) :
    (axis f).coeff n = f.coeff (Finsupp.single none n) := by
  classical
  change (((optionEquivLeft k σ f).map MvPolynomial.constantCoeff).coeff n) = _
  rw [Polynomial.coeff_map, constantCoeff_eq, optionEquivLeft_coeff_coeff]
  congr 1

theorem natDegree_axis_le (f : MvPolynomial (Option σ) k) : (axis f).natDegree ≤ f.totalDegree := by
  calc
    _ ≤ (optionEquivLeft k σ f).natDegree := Polynomial.natDegree_map_le
    _ = f.degreeOf none := natDegree_optionEquivLeft k _
    _ ≤ _ := degreeOf_le_totalDegree _ _

private theorem isUnit_of_totalDegree_zero {f : MvPolynomial (Option σ) k} (hf : f ≠ 0)
    (hd : f.totalDegree = 0) : IsUnit f := by
  rw [totalDegree_eq_zero_iff_eq_C.mp hd] at hf ⊢
  exact (isUnit_iff_ne_zero.mpr fun h => hf (by simp [h])).map MvPolynomial.C

theorem irreducible_of_axis {f : MvPolynomial (Option σ) k}
    (hd : f.totalDegree ≤ (axis f).natDegree) (hirr : Irreducible (axis f)) : Irreducible f := by
  refine ⟨fun h => hirr.not_isUnit (h.map axis), ?_⟩
  intro a b hab
  have hmap : axis f = axis a * axis b := hab ▸ map_mul axis a b
  have hn := mul_ne_zero_iff.mp (hmap ▸ hirr.ne_zero)
  have ha : a ≠ 0 := fun h => hn.1 (by simp [h])
  have hb : b ≠ 0 := fun h => hn.2 (by simp [h])
  have hg := congrArg Polynomial.natDegree hmap
  rw [Polynomial.natDegree_mul hn.1 hn.2] at hg
  rw [hab, totalDegree_mul_of_isDomain ha hb] at hd
  have h₁ := natDegree_axis_le a
  have h₂ := natDegree_axis_le b
  have hdeg : a.totalDegree + b.totalDegree ≤ (axis a).natDegree + (axis b).natDegree := by
    simpa only [← hab, hg] using hd
  rcases hirr.isUnit_or_isUnit hmap with h | h
  · exact Or.inl (isUnit_of_totalDegree_zero ha (by have := Polynomial.natDegree_eq_zero_of_isUnit h; omega))
  · exact Or.inr (isUnit_of_totalDegree_zero hb (by have := Polynomial.natDegree_eq_zero_of_isUnit h; omega))

/-- Auxiliary prime-square residues of the lower coefficients enforce
irreducibility, without any demands on reductions at previously processed primes. -/
theorem irreducible_of_coefficient_residues (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) (f : Polynomial ℚ) (hm : f.Monic) (hd : f.natDegree = n+1)
    (h : ∀ j : Fin (n+1), ∃ x : ℤ_[ell], (x : ℚ_[ell]) = (f.coeff j : ℚ) ∧
      PadicInt.toZModPow 2 x = if j.val = 0 then (ell : ZMod (ell^2)) else 0) :
    Irreducible f := by
  classical
  choose a ha hres using h
  let g := ShiftedEisenstein.monicFamily n (a 0) (fun j => a j.succ)
  obtain ⟨hgm,hgd⟩ := ShiftedEisenstein.monicFamily_monic_degree n (a 0) (fun j => a j.succ)
  have hcoeff (j : Fin (n+1)) : g.coeff j = a j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ShiftedEisenstein.monicFamily_coeff_zero _ _ _
    · exact ShiftedEisenstein.monicFamily_coeff_succ _ _ _ j
  have he : g.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[ell]) := by
    apply hgm.isEisensteinAt_of_mem_of_notMem (IsLocalRing.maximalIdeal.isMaximal ℤ_[ell]).ne_top
    · intro j hj
      let i : Fin (n+1) := ⟨j, hj.trans_eq hgd⟩
      rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (ell : ℤ_[ell]), ← PadicInt.ker_toZModPow 1, RingHom.mem_ker]
      have ha' := hres i
      let φ := ZMod.castHom (pow_dvd_pow ell (show 1 ≤ 2 by decide)) (ZMod (ell ^ 1))
      have hφ : φ.comp (PadicInt.toZModPow 2) = PadicInt.toZModPow 1 := PadicInt.zmod_cast_comp_toZModPow 1 2 (by decide)
      change PadicInt.toZModPow 1 (g.coeff i) = 0
      rw [hcoeff, ← hφ, RingHom.comp_apply, ha']
      split_ifs
      · rw [map_natCast, ZMod.natCast_eq_zero_iff, pow_one]
      · exact map_zero _
    · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow 2, RingHom.mem_ker]
      change PadicInt.toZModPow 2 (g.coeff (0 : Fin (n+1))) ≠ 0
      rw [hcoeff, hres]
      simpa using ShiftedEisenstein.prime_ne_zero_mod_square ell Fact.out
  apply ShiftedEisenstein.irreducible_of_padic_model ell f hm g
  · rw [ShiftedEisenstein.monicFamily_map]
    apply ShiftedEisenstein.monicFamily_eq _ _ _ _ (hm.map _) ((hm.natDegree_map _).trans hd)
    · simpa using (ha 0).symm
    · intro j
      simpa using (ha j.succ).symm
  · exact (hgm.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp
      (he.irreducible inferInstance hgm.isPrimitive (by dsimp [g]; omega))

/-- A linear leading form restricting to `X` along the axis shifts the
coordinate system while retaining the degree of the specialization. -/
theorem irreducible_leading_power [DecidableEq σ] (ell : ℕ) [Fact ell.Prime]
    (l q : MvPolynomial (Option σ) ℚ) (d : ℕ) (hd : 0 < d)
    (hl : l.totalDegree ≤ 1) (ha : axis l = Polynomial.X) (hq : q.totalDegree < d)
    (h : ∀ m : (Option σ →₀ ℕ), ∃ x : ℤ_[ell], (x : ℚ_[ell]) = (q.coeff m : ℚ) ∧
      PadicInt.toZModPow 2 x = if m = 0 then (ell : ZMod (ell ^ 2)) else 0) :
    Irreducible (l ^ d + q) ∧ (l ^ d + q).totalDegree = d := by
  classical
  have hlow := (natDegree_axis_le q).trans_lt hq
  have hf : axis (l ^ d + q) = Polynomial.X ^ d + axis q := by rw [map_add, map_pow, ha]
  have hdeg : (axis (l ^ d + q)).natDegree = d := by
    rw [hf, Polynomial.natDegree_add_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    simpa using hlow
  have htot : (l ^ d + q).totalDegree ≤ d := by
    apply (totalDegree_add _ _).trans (max_le ?_ hq.le)
    exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left d hl)
  refine ⟨irreducible_of_axis (htot.trans_eq hdeg.symm) ?_, htot.antisymm (hdeg.ge.trans (natDegree_axis_le _))⟩
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  refine irreducible_of_coefficient_residues ell n _ ?_ hdeg ?_
  · rw [hf]
    exact Polynomial.monic_X_pow_add (Polynomial.degree_lt_degree (p := axis q)
      (q := Polynomial.X ^ (n+1)) (by simpa using hlow) |>.trans_eq (Polynomial.degree_X_pow _))
  · intro j
    obtain ⟨x,hx,hr⟩ := h (Finsupp.single none j.val)
    refine ⟨x, ?_, ?_⟩
    · rw [hf, Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_right j.isLt.ne, zero_add, axis_coeff, hx]
    · simpa using hr

/-- Transport the axis criterion to any labeling of the coordinates. -/
theorem irreducible_leading_power_equiv {τ : Type*} [DecidableEq τ] [DecidableEq σ]
    (e : τ ≃ Option σ) (ell : ℕ) [Fact ell.Prime] (l q : MvPolynomial τ ℚ)
    (d : ℕ) (hd : 0 < d) (hl : l.totalDegree ≤ 1)
    (ha : axis (rename e l) = Polynomial.X) (hq : q.totalDegree < d)
    (h : ∀ m : τ →₀ ℕ, ∃ x : ℤ_[ell], (x : ℚ_[ell]) = (q.coeff m : ℚ) ∧
      PadicInt.toZModPow 2 x = if m = 0 then (ell : ZMod (ell ^ 2)) else 0) :
    Irreducible (l ^ d + q) ∧ (l ^ d + q).totalDegree = d := by
  have hcoeff (m : Option σ →₀ ℕ) : ∃ x : ℤ_[ell],
      (x : ℚ_[ell]) = ((rename e q).coeff m : ℚ) ∧
      PadicInt.toZModPow 2 x = if m = 0 then (ell : ZMod (ell ^ 2)) else 0 := by
    obtain ⟨j, rfl⟩ := (Finsupp.domCongr e : (τ →₀ ℕ) ≃+ (Option σ →₀ ℕ)).surjective m
    have hz : Finsupp.mapDomain (⇑e) j = 0 ↔ j = 0 := by
      simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain] using ((Finsupp.domCongr e).map_eq_zero_iff (x := j))
    simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _ e.injective,
      hz] using h j
  obtain ⟨hi,ht⟩ := irreducible_leading_power ell (rename e l) (rename e q) d hd
    ((totalDegree_renameEquiv e l).le.trans hl) ha ((totalDegree_renameEquiv e q).le.trans_lt hq) hcoeff
  have he : rename e (l^d + q) = rename e l ^ d + rename e q := by rw [map_add, map_pow]
  rw [← he] at hi ht
  exact ⟨(MulEquiv.irreducible_iff (renameEquiv ℚ e)).mp hi, (totalDegree_renameEquiv e _).symm.trans ht⟩

end UnconditionalCounterexample.MultivariateSelection
