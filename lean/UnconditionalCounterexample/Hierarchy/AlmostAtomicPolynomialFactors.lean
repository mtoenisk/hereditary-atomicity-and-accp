import UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomialBase

/-! # Normalizing the polynomial irreducibles at the two residue classes

An irreducible over the rationals is nonzero at 0 or 1. After clearing its
coefficients, that evaluation bounds the finitely many primes where both
p-adic branches have positive order. A rational rescaling makes the minimum
order zero at every prime and prevents any nonunit constant from dividing it.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial

open GuardSupport Polynomial

private def residue (b : Bool) : ℤ := if b then 1 else 0

private theorem nonroot_branch (f : ℚ[X]) (hf : Irreducible f) :
    ∃ b : Bool, f.eval (residue b : ℚ) ≠ 0 := by
  by_cases h : f.eval 0 = 0
  · refine ⟨true,?_⟩
    have hX : X ∣ f := X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero])
    obtain ⟨g,hg⟩ := (irreducible_X.associated_of_dvd hf hX).symm.dvd
    intro he
    change f.eval 1 = 0 at he
    have e := congrArg (eval (1 : ℚ)) hg
    exact one_ne_zero (by simpa only [eval_X,eval_mul,he,zero_mul] using e)
  · exact ⟨false,h⟩

private theorem eval_integer_model (V : ℤ[X]) (p : PrimeIndex) (b : Bool) :
    value p b (V.map (algebraMap ℤ ℚ)) =
      ((V.eval₂ (Int.castRingHom ℤ_[p.val]) (point p b) : ℤ_[p.val]) : ℚ_[p.val]) := by
  rw [coe_intPolynomial_eval]
  change (V.map _).eval₂ (Rat.castHom ℚ_[p.val]) _ = _
  rw [eval₂_map]
  congr 1

private theorem residue_unit (V : ℤ[X]) (p : PrimeIndex) (b : Bool)
    (hv : ¬ (p.val : ℤ) ∣ V.eval (residue b)) :
    ‖value p b (V.map (algebraMap ℤ ℚ))‖ = 1 := by
  rw [eval_integer_model]
  apply PadicInt.isUnit_iff.mp
  apply intPolynomial_eval_unit_of_residue_nonzero
  have hr : PadicInt.toZMod (point p b) = (residue b : ZMod p.val) := by
    cases b <;> simp [residue,point_residue]
  rw [hr]
  change V.eval₂ (Int.castRingHom (ZMod p.val)) ((Int.castRingHom (ZMod p.val)) (residue b)) ≠ 0
  rw [eval₂_at_apply]
  exact fun h => hv ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

private theorem match_norm (S : Finset PrimeIndex) (a : (p : PrimeIndex) → ℚ_[p.val])
    (ha : ∀ p, a p ≠ 0) (hS : ∀ p ∉ S, ‖a p‖ = 1) :
    ∃ z : ℚ, z ≠ 0 ∧ ∀ p : PrimeIndex, ‖(z : ℚ_[p.val])‖ = ‖a p‖ := by
  classical
  let e (p : PrimeIndex) := (a p).valuation
  let z := ∏ p ∈ S, (p.val : ℚ) ^ e p
  refine ⟨z,Finset.prod_ne_zero_iff.mpr (fun p _ => zpow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero)),?_⟩
  intro p
  have he (v : PrimeIndex) (hv : v ≠ p) : ‖(v.val : ℚ_[p.val]) ^ e v‖ = 1 := by
    have hcop : p.val.Coprime v.val := (Nat.coprime_primes p.property v.property).mpr
      (fun h => hv (Subtype.ext h.symm))
    rw [norm_zpow,Padic.norm_natCast_eq_one_iff.mpr hcop,one_zpow]
  have hprod : ‖(z : ℚ_[p.val])‖ = ∏ v ∈ S, ‖(v.val : ℚ_[p.val]) ^ e v‖ := by
    simp [z,norm_prod]
  rw [hprod]
  by_cases hp : p ∈ S
  · rw [Finset.prod_eq_single p (fun v _ hv => he v hv) (fun hn => (hn hp).elim)]
    have hne : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
    rw [Padic.norm_eq_zpow_neg_valuation (zpow_ne_zero _ hne),Padic.valuation_zpow,
      Padic.valuation_p,mul_one,Padic.norm_eq_zpow_neg_valuation (ha p)]
  · rw [Finset.prod_eq_one (fun v hv => he v (fun h => hp (h ▸ hv))),hS p hp]

private theorem scalar_divisor_isUnit (a x y : ring) (hxy : a = x*y)
    (h : ∀ p, ∃ b, ‖value p b a.val‖ = 1) (hx : IsUnit x.val) : IsUnit x := by
  obtain ⟨u,hu,hu'⟩ := Polynomial.isUnit_iff.mp hx
  have hunit (p : PrimeIndex) : ‖(u : ℚ_[p.val])‖ = 1 := by
    obtain ⟨b,hb⟩ := h p
    have hxle := (mem_ring x.val).mp x.property p b
    have hyle := (mem_ring y.val).mp y.property p b
    rw [← hu',value_C] at hxle
    have hp := congrArg Subtype.val hxy
    change a.val = x.val*y.val at hp
    rw [hp,value_mul,← hu',value_C,norm_mul] at hb
    exact hxle.antisymm (by nlinarith [norm_nonneg (u : ℚ_[p.val])])
  have hinv : C u⁻¹ ∈ ring := (mem_ring _).mpr fun p b => by
    rw [value_C,Rat.cast_inv,norm_inv,hunit,inv_one]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨_,hinv⟩,Subtype.ext ?_⟩
  change x.val * C u⁻¹ = 1
  rw [← hu',← C_mul,mul_inv_cancel₀ hu.ne_zero,C_1]

private theorem atom_of_normalized (a : ring) (ha : Irreducible a.val)
    (h : ∀ p, ∃ b, ‖value p b a.val‖ = 1) : Irreducible a := by
  refine ⟨fun hu => ha.not_isUnit (hu.map ring.subtype),?_⟩
  intro x y he
  rcases ha.isUnit_or_isUnit (congrArg Subtype.val he) with hx | hy
  · exact Or.inl (scalar_divisor_isUnit a x y he h hx)
  · exact Or.inr (scalar_divisor_isUnit a y x (he.trans (mul_comm ..)) h hy)

/-- Normalize every rational irreducible by a scalar so that at least one
branch above each prime has order zero. The resulting element is an atom. -/
theorem exists_normalized_irreducible_scalar (f : ℚ[X]) (hf : Irreducible f) :
    ∃ a : ring, Irreducible a ∧ (∀ p, ∃ b, ‖value p b a.val‖ = 1) ∧
      ∃ q : ℚ, q ≠ 0 ∧ f = C q * a.val := by
  classical
  obtain ⟨d,V,hd,_,hm⟩ := exists_integer_multiple f hf.ne_zero
  let g := V.map (algebraMap ℤ ℚ)
  have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hg : Irreducible g := by
    rw [show g = C (d : ℚ)*f from hm]
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hd').map C)).mpr hf
  obtain ⟨b,hb⟩ := nonroot_branch g hg
  have hV : V.eval (residue b) ≠ 0 := by
    intro h
    apply hb
    change eval ((algebraMap ℤ ℚ) (residue b)) (V.map _) = 0
    rw [eval_map,eval₂_at_apply,h,map_zero]
  let S : Finset PrimeIndex := (Finset.range ((V.eval (residue b)).natAbs + 1)).subtype Nat.Prime
  let branch (p : PrimeIndex) := decide (‖value p false g‖ ≤ ‖value p true g‖)
  have largest (p : PrimeIndex) (i : Bool) : ‖value p i g‖ ≤ ‖value p (branch p) g‖ := by
    cases i <;> by_cases h : ‖value p false g‖ ≤ ‖value p true g‖ <;> simp [branch,h, le_of_not_ge]
  have integral (p : PrimeIndex) (i : Bool) : ‖value p i g‖ ≤ 1 :=
    (eval_integer_model V p i) ▸ (V.eval₂ (Int.castRingHom ℤ_[p.val]) (point p i)).property
  obtain ⟨z,hz,hZ⟩ := match_norm S (fun p => value p (branch p) g)
    (fun p => value_ne_zero p (branch p) hg.ne_zero) (by
      intro p hp
      have hbig : (V.eval (residue b)).natAbs < p.val := by simpa [S,Nat.lt_succ_iff] using hp
      have hn : ¬ (p.val : ℤ) ∣ V.eval (residue b) := fun h =>
        hbig.not_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr hV) (by simpa using Int.natAbs_dvd_natAbs.mpr h))
      exact (integral p _).antisymm ((residue_unit V p b hn) ▸ largest p b))
  let a₀ := C z⁻¹ * g
  have valnorm (p : PrimeIndex) (i : Bool) : ‖value p i a₀‖ = ‖value p i g‖ / ‖(z : ℚ_[p.val])‖ := by
    simp [a₀,value_mul,value_C,norm_mul,div_eq_inv_mul]
  have hzp (p : PrimeIndex) : 0 < ‖(z : ℚ_[p.val])‖ := norm_pos_iff.mpr (Rat.cast_ne_zero.mpr hz)
  let a : ring := ⟨a₀,(mem_ring _).mpr fun p i => by
    rw [valnorm,div_le_one (hzp p),hZ]
    exact largest p i⟩
  have hi : Irreducible a.val := (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hz)).map C)).mpr hg
  have ha (p : PrimeIndex) : ∃ b, ‖value p b a.val‖ = 1 := by
    refine ⟨branch p,?_⟩
    change ‖value p (branch p) a₀‖ = 1
    rw [valnorm,← hZ,div_self (hzp p).ne']
  refine ⟨a,atom_of_normalized a hi ha,ha,z/(d : ℚ),div_ne_zero hz hd',?_⟩
  change f = C (z/(d : ℚ)) * (C z⁻¹ * g)
  rw [show g = C (d : ℚ)*f from hm,← mul_assoc,← C_mul,← mul_assoc,← C_mul]
  have hz' : z / (d : ℚ) * z⁻¹ * d = 1 := by field_simp
  rw [hz',C_1,one_mul]

/-- Rational irreducibles have atom representatives in the evaluation ring. -/
theorem exists_irreducible_scalar (f : ℚ[X]) (hf : Irreducible f) :
    ∃ a : ring, Irreducible a ∧ ∃ q : ℚ, q ≠ 0 ∧ f = C q * a.val := by
  obtain ⟨a,ha,_,hq⟩ := exists_normalized_irreducible_scalar f hf
  exact ⟨a,ha,hq⟩

end UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial
