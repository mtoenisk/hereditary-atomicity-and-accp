import UnconditionalCounterexample.Variations.MultivariateSelectionChain

/-!
# Good reduction and fixed points on the chronological multivariate sequence

The coefficient of the pure first-coordinate monomial of the prescribed
degree is one. Thus the integral model at every unassigned prime has
nonzero reduction. At the auxiliary prime its reduction is exactly the
chosen leading power, as needed to assign its guard.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport MultivariateListedWords MultivariateSchedule
open MultivariateInfinity

variable {r : ℕ} {M : ℕ → Type*} {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable (R : Requirements r M K)

theorem raw_pairwise_nonassociated {i j : ℕ} (hij : i ≠ j) :
    ¬ Associated (raw R i) (raw R j) := by
  intro h
  apply hij ((degree_strictMono R).injective ?_)
  exact (totalDegree_le_of_dvd_of_isDomain h.dvd (raw_irreducible R j).ne_zero).antisymm
    (totalDegree_le_of_dvd_of_isDomain h.symm.dvd (raw_irreducible R i).ne_zero)

theorem fixed_survives (n : ℕ) (u : Fin (r+1) → K) (hu : u ∈ R.fixed) :
    eval u (extend (raw R n)) ≠ 0 := by
  classical
  apply stage_tests R n (.point u)
  apply point_mem_tests
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)

/-- Protecting the origin ensures every subsequent primary can be screened
against all preceding raw polynomials on the first-coordinate hyperplane. -/
theorem first_variable_not_dvd (h0 : (0 : Fin (r+1) → K) ∈ R.fixed) (n : ℕ) :
    ¬ X (0 : Fin (r+1)) ∣ raw R n := by
  rintro ⟨g,hg⟩
  apply fixed_survives R n 0 h0
  simp [hg,extend]

/-- The pure top coefficient is one even though the rest of the leading form varies. -/
theorem axis_top_coeff (r s d : ℕ) (q : Poly r) (hq : q.totalDegree < d) :
    (vandermondeForm (r+1) s ^ d + q).coeff (Finsupp.single 0 d) = 1 := by
  let e := _root_.finSuccEquiv r
  let l := vandermondeForm (k := ℚ) (r+1) s
  let F := l ^ d + q
  have he : (Finsupp.single (0 : Fin (r+1)) d).mapDomain e = Finsupp.single none d := by
    rw [Finsupp.mapDomain_single]
    rfl
  have haxis : axis (rename e F) = Polynomial.X ^ d + axis (rename e q) := by
    simp only [F,map_add,map_pow]
    rw [show axis (rename e l) = Polynomial.X from vandermonde_axis r s]
  have hlow : (axis (rename e q)).natDegree < d :=
    (natDegree_axis_le _).trans_lt ((totalDegree_renameEquiv e q).le.trans_lt hq)
  calc
    F.coeff (Finsupp.single 0 d) = (rename e F).coeff (Finsupp.single none d) := by
      rw [← he, coeff_rename_mapDomain _ e.injective]
    _ = (axis (rename e F)).coeff d := (axis_coeff _ _).symm
    _ = 1 := by rw [haxis, Polynomial.coeff_add, Polynomial.coeff_X_pow_self,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlow, add_zero]

def localInput (n : ℕ) := R.sites n (fun j : Fin n => chain R j.val) _ (threshold_le R _)

theorem raw_top_coeff (n : ℕ) : (raw R n).coeff (Finsupp.single 0 (chain R n).degree) = 1 :=
  axis_top_coeff r n _ _ (chain R n).lower_lt

theorem map_vandermonde {A B : Type*} [Field A] [Field B] (φ : A →+* B) (r s : ℕ) :
    MvPolynomial.map φ (vandermondeForm (k := A) r s) = vandermondeForm r s := by
  simp [vandermondeForm]

/-- A polynomial model in the integers, with nonzero reduction, at every prime
outside that stage's processed set. -/
theorem raw_good_reduction (n : ℕ) (v : PrimeIndex) (hv : v ∉ (localInput R n).primes) :
    ∃ Q : MvPolynomial (Fin (r+1)) ℤ_[v.val],
      MvPolynomial.map (algebraMap ℤ_[v.val] ℚ_[v.val]) Q = MvPolynomial.map (algebraMap ℚ ℚ_[v.val]) (raw R n) ∧
      Q.coeff (Finsupp.single 0 (chain R n).degree) = 1 ∧ MvPolynomial.map PadicInt.toZMod Q ≠ 0 := by
  classical
  let L := localInput R n
  let p (i : L.primes) := i.val.val
  have hnew (i : L.primes) : p i ≠ v.val := fun h => hv ((Subtype.ext h : i.val = v) ▸ i.property)
  obtain ⟨q',hq'⟩ := exists_integral_model p (chain R n).lower (chain_accepted R n).supported v.val hnew
  let l : MvPolynomial (Fin (r+1)) ℤ_[v.val] := ∑ j, C ((n : ℤ_[v.val]) ^ j.val) * X j
  have hl : MvPolynomial.map (algebraMap ℤ_[v.val] ℚ_[v.val]) l = vandermondeForm (r+1) n := by
    simp [l,vandermondeForm]
  let F := l ^ (chain R n).degree + q'
  have hF : MvPolynomial.map (algebraMap ℤ_[v.val] ℚ_[v.val]) F =
      MvPolynomial.map (algebraMap ℚ ℚ_[v.val]) (raw R n) := by
    simp only [F, raw, Entry.raw, map_add, map_pow, map_vandermonde, hl, hq']
  have hc := congrArg (fun f : MvPolynomial (Fin (r+1)) ℚ_[v.val] => f.coeff (Finsupp.single 0 (chain R n).degree)) hF
  simp only [coeff_map,raw_top_coeff, map_one] at hc
  have ht : F.coeff (Finsupp.single 0 (chain R n).degree) = 1 := Subtype.ext hc
  refine ⟨F,hF,ht,?_⟩
  intro hzero
  have h := congrArg (fun f : MvPolynomial (Fin (r+1)) (ZMod v.val) => f.coeff (Finsupp.single 0 (chain R n).degree)) hzero
  change (MvPolynomial.map PadicInt.toZMod F).coeff (Finsupp.single 0 (chain R n).degree) = 0 at h
  rw [coeff_map,ht,map_one] at h
  exact one_ne_zero h

private theorem residue_one_zero (v : PrimeIndex) (a : ℤ_[v.val]) {m : (Fin (r+1)) →₀ ℕ}
    (hr : PadicInt.toZModPow 2 a = if m = 0 then (v.val : ZMod (v.val^2)) else 0) :
    PadicInt.toZModPow 1 a = 0 := by
  let φ := ZMod.castHom (pow_dvd_pow v.val (show 1 ≤ 2 by decide)) (ZMod (v.val^1))
  have hφ : φ.comp (PadicInt.toZModPow 2) = PadicInt.toZModPow 1 := PadicInt.zmod_cast_comp_toZModPow 1 2 (by decide)
  rw [← hφ, RingHom.comp_apply, hr]
  split_ifs
  · rw [map_natCast, ZMod.natCast_eq_zero_iff, pow_one]
  · exact map_zero _

/-- The auxiliary-prime residue is exactly the leading power. A guard tuple
off its leading hyperplane therefore sees the polynomial as a unit. -/
theorem raw_auxiliary_model (n : ℕ) :
    let ell := (localInput R n).aux.val
    ∃ Q : MvPolynomial (Fin (r+1)) ℤ_[ell],
      MvPolynomial.map (algebraMap ℤ_[ell] ℚ_[ell]) Q = MvPolynomial.map (algebraMap ℚ ℚ_[ell]) (raw R n) ∧
      MvPolynomial.map (PadicInt.toZModPow 1) Q =
        (∑ j : Fin (r+1), C ((n : ZMod (ell^1)) ^ j.val) * X j) ^ (chain R n).degree := by
  classical
  let ell := (localInput R n).aux
  let q := (chain R n).lower
  have hm : ∀ m, HasAuxiliaryResidue ell.val (q.coeff m) (if m = 0 then (ell.val : ZMod (ell.val^2)) else 0) :=
    (chain_accepted R n).residue
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
  refine ⟨l ^ (chain R n).degree + q', ?_, ?_⟩
  · change MvPolynomial.map (algebraMap ℤ_[ell.val] ℚ_[ell.val]) (l ^ (chain R n).degree + q') =
      MvPolynomial.map (algebraMap ℚ ℚ_[ell.val]) (vandermondeForm (r+1) n ^ (chain R n).degree + q)
    simp only [map_add,map_pow,hq',map_vandermonde]
    simp [l,vandermondeForm]
  · simp [map_add,map_pow,hred,l]

end UnconditionalCounterexample.MultivariateSelection
