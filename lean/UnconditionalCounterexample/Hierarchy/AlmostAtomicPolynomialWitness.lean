import UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomialBase
import Factorization.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# The quadratic obstruction in the two-point polynomial overring

A divisor of the quadratic has at most one copy of each of its two linear
factors over the rationals. Integer leading coefficients exclude all products
of atoms, even after multiplying by a unit of the overring.
-/

noncomputable section

namespace UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial

open Polynomial GuardSupport

private abbrev quad : ℚ[X] := X * (X - 1)

private theorem divisor_linear_shape {L f : ℚ[X]} (hL : Irreducible L) (hf : f ∣ L) :
    ∃ c : ℚ, f = C c ∨ f = C c * L := by
  rcases hL.dvd_iff.mp hf with h | ⟨u, hu⟩
  · obtain ⟨c, _, hc⟩ := Polynomial.isUnit_iff.mp h
    exact ⟨c, Or.inl hc.symm⟩
  · obtain ⟨c, _, hc⟩ := Polynomial.isUnit_iff.mp u.isUnit
    exact ⟨c, Or.inr (by rw [← hu, hc, mul_comm])⟩

private theorem divisor_quadratic_shape {f : ℚ[X]} (hf : f ∣ quad) :
    ∃ c : ℚ, f = C c ∨ f = C c * X ∨ f = C c * (X - 1) ∨ f = C c * quad := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hf
  obtain ⟨c, hc⟩ := divisor_linear_shape irreducible_X ha
  have hirr : Irreducible (X - 1 : ℚ[X]) := by simpa using (irreducible_X_sub_C (1 : ℚ))
  obtain ⟨d, hd⟩ := divisor_linear_shape hirr hb
  refine ⟨c*d, ?_⟩
  rw [map_mul]
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl (by ring)))
  · exact Or.inr (Or.inl (by ring))
  · exact Or.inr (Or.inr (Or.inr (by unfold quad; ring)))

private theorem linear_atom
    (L : ring) (hm : (L : ℚ[X]).Monic) (hirr : Irreducible (L : ℚ[X]))
    (hint : ∀ c : ℚ, C c * (L : ℚ[X]) ∈ ring → ∃ n : ℤ, (n : ℚ) = c) :
    Irreducible L := by
  have hcoeff (a : ring) (ha : (a : ℚ[X]) ∣ (L : ℚ[X])) :
      ∃ n : ℤ, (n : ℚ) = (a : ℚ[X]).leadingCoeff := by
    obtain ⟨c, hc | hc⟩ := divisor_linear_shape hirr ha
    · obtain ⟨n, hn⟩ := (constant_mem c).mp (hc ▸ a.property)
      exact ⟨n, by simpa [hc] using hn⟩
    · obtain ⟨n, hn⟩ := hint c (hc ▸ a.property)
      exact ⟨n, by simpa [hc, leadingCoeff_mul, hm.leadingCoeff] using hn⟩
  have leftUnit (a b : ring) (hab : L = a * b) (ha : IsUnit (a : ℚ[X])) : IsUnit a := by
    obtain ⟨j, rfl⟩ := eq_intCast_of_polynomial_unit ha
    have hp : (L : ℚ[X]) = (j : ℚ[X]) * (b : ℚ[X]) :=
      congrArg (fun x : ring => (x : ℚ[X])) hab
    obtain ⟨k, hk⟩ := hcoeff b (hp ▸ dvd_mul_left _ _)
    have hcj : (j : ℚ[X]) = C (j : ℚ) := (map_intCast (C : ℚ →+* ℚ[X]) j).symm
    have he := congrArg leadingCoeff hp
    have hrat : (1 : ℚ) = (j : ℚ) * k := by
      simpa only [leadingCoeff_mul, hm.leadingCoeff, ← hk, hcj, leadingCoeff_C] using he
    have hInt : (1 : ℤ) = j * k := by exact_mod_cast hrat
    exact (isUnit_iff_dvd_one.mpr ⟨k, hInt⟩).map (Int.castRingHom ring)
  refine ⟨fun h => hirr.not_isUnit (h.map ring.subtype), fun {a b} hab => ?_⟩
  have hp : (L : ℚ[X]) = (a : ℚ[X]) * (b : ℚ[X]) := congrArg (fun x : ring => (x : ℚ[X])) hab
  rcases hirr.isUnit_or_isUnit hp with ha | hb
  · exact Or.inl (leftUnit a b hab ha)
  · exact Or.inr (leftUnit b a (hab.trans (mul_comm _ _)) hb)

private theorem product_integer_leadingCoeff {R : Subring ℚ[X]} (s : Multiset R)
    (h : ∀ a ∈ s, ∃ n : ℤ, (n : ℚ) = (a : ℚ[X]).leadingCoeff) :
    ∃ n : ℤ, (n : ℚ) = (s.prod : ℚ[X]).leadingCoeff := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | cons a s ih =>
    obtain ⟨j, hj⟩ := h a (Multiset.mem_cons_self ..)
    obtain ⟨k, hk⟩ := ih (fun v hv => h v (Multiset.mem_cons_of_mem hv))
    exact ⟨j*k, by simp [leadingCoeff_mul, hj, hk]⟩


/-- The coordinate in the two-point ring. -/
def parameter : ring := ⟨X, X_mem⟩

theorem parameter_atom : Irreducible parameter := by
  apply linear_atom parameter monic_X irreducible_X
  intro c hc
  apply linear_scalar_integer false c
  simpa [parameter] using hc

theorem parameter_sub_one_atom : Irreducible (parameter - 1) := by
  apply linear_atom
  · change (X - 1 : ℚ[X]).Monic
    simpa using monic_X_sub_C (1 : ℚ)
  · change Irreducible (X - 1 : ℚ[X])
    simpa using irreducible_X_sub_C (1 : ℚ)
  · intro c hc
    apply linear_scalar_integer true c
    simpa [parameter] using hc

/-- At each of the two arguments, one of the factors has norm exactly that
of the residue characteristic and the other has norm at most one. -/
private theorem quad_bound (p : PrimeIndex) (b : Bool) :
    ‖value p b quad‖ ≤ ‖(p.val : ℚ_[p.val])‖ := by
  have ho := point_order p b
  have hn : (point p b).val - (if b then 1 else 0) ≠ 0 := by
    intro hz
    simp [hz] at ho
  have hnear : ‖(point p b).val - (if b then 1 else 0)‖ = ‖(p.val : ℚ_[p.val])‖ := by
    rw [Padic.norm_eq_zpow_neg_valuation hn, ho, Padic.norm_p]
    simp
  have h0 := (point p b).property
  have h1 : ‖(point p b).val - 1‖ ≤ 1 := by
    simpa only [PadicInt.coe_sub, PadicInt.coe_one] using (point p b - 1).property
  simp only [quad, map_mul, map_sub, map_one, value_X, norm_mul]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ite_false, sub_zero] at hnear
    rw [← hnear]
    exact mul_le_of_le_one_right (norm_nonneg _) h1
  | true =>
    simp only [ite_true] at hnear
    rw [← hnear]
    exact mul_le_of_le_one_left (norm_nonneg _) h0

private theorem divide_quad_mem (c : ℚ) (p : PrimeIndex)
    (hc : C c * quad ∈ ring) (hcp : ‖(c : ℚ_[p.val])‖ ≤ 1) :
    C (c / p.val) * quad ∈ ring := by
  apply (mem_ring _).mpr
  intro r b
  have hnorm : 0 < ‖(p.val : ℚ_[r.val])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr p.property.ne_zero)
  rw [map_mul, value_C, Rat.cast_div, Rat.cast_natCast, norm_mul, norm_div, div_mul_eq_mul_div,
    div_le_one hnorm]
  by_cases h : r = p
  · subst r
    exact (mul_le_of_le_one_left (norm_nonneg _) hcp).trans (quad_bound p b)
  · have hcop : r.val.Coprime p.val := r.property.coprime_iff_not_dvd.mpr fun hd =>
      h (Subtype.ext (p.property.eq_one_or_self_of_dvd r.val hd |>.resolve_left r.property.ne_one))
    rw [Padic.norm_natCast_eq_one_iff.mpr hcop]
    simpa only [map_mul, value_C, norm_mul] using (mem_ring _).mp hc r b

/-- The rational quadratic with leading coefficient one half. -/
def z : ring :=
  ⟨C (1/2) * quad, by
    have h := divide_quad_mem 1 ⟨2, Nat.prime_two⟩
      (by simpa [quad] using ring.mul_mem X_mem (ring.sub_mem X_mem ring.one_mem)) (by simp)
    simpa using h⟩

theorem two_mul_z : 2 * z = parameter * (parameter - 1) := by
  apply Subtype.ext
  change (2 : ℚ[X]) * (C (1/2) * quad) = quad
  rw [show (2 : ℚ[X]) = C (2 : ℚ) from (map_ofNat (C : ℚ →+* ℚ[X]) 2).symm, ← mul_assoc, ← map_mul]
  norm_num

theorem z_ne_zero : z ≠ 0 := by
  intro hz
  have h := two_mul_z
  rw [hz, mul_zero] at h
  exact (mul_ne_zero parameter_atom.ne_zero parameter_sub_one_atom.ne_zero) h.symm

/-- No scalar multiple of the full quadratic can be irreducible. At a prime
larger than the denominator of the scalar, it still lies in the ring after
division by that prime. -/
private theorem not_atom_quad (a : ring) (c : ℚ) (ha : (a : ℚ[X]) = C c * quad) :
    ¬ Irreducible a := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (c.den + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let r : PrimeIndex := ⟨p, hprime⟩
  have hcp : ‖(c : ℚ_[r.val])‖ ≤ 1 := Padic.norm_rat_le_one fun hd =>
    (show ¬ p ≤ c.den by omega) (Nat.le_of_dvd c.den_pos hd)
  let b : ring := ⟨_, divide_quad_mem c r (ha ▸ a.property) hcp⟩
  have he : a = (p : ring) * b := by
    apply Subtype.ext
    change (a : ℚ[X]) = (p : ℚ[X]) * (C (c / p) * quad)
    have hq : (p : ℚ) * (c / p) = c := by
      field_simp [Nat.cast_ne_zero.mpr hprime.ne_zero]
    rw [ha, ← map_natCast (C : ℚ →+* ℚ[X]) p, ← mul_assoc (C (p : ℚ)), ← map_mul, hq]
  intro hirr
  have hb := (hirr.isUnit_or_isUnit he).resolve_left (prime_atom p hprime).not_isUnit
  have hx : (X : ℚ[X]) ∣ (b : ℚ[X]) := by
    change X ∣ C _ * (X * (X - 1))
    exact dvd_mul_of_dvd_right (dvd_mul_right ..) _
  exact (irreducible_X (R := ℚ)).not_isUnit (isUnit_of_dvd_unit hx (hb.map ring.subtype))

private theorem atom_leadingCoeff_integer {a : ring} (ha : Irreducible a) (hd : a ∣ z) :
    ∃ n : ℤ, (n : ℚ) = (a : ℚ[X]).leadingCoeff := by
  have hq : (a : ℚ[X]) ∣ quad := by
    have h := (map_dvd ring.subtype hd).trans (dvd_mul_left (z : ℚ[X]) 2)
    have he : (2 : ℚ[X]) * (z : ℚ[X]) = quad := congrArg (fun x : ring => (x : ℚ[X])) two_mul_z
    exact he ▸ h
  obtain ⟨c, hc | hc | hc | hc⟩ := divisor_quadratic_shape hq
  · obtain ⟨n, hn⟩ := (constant_mem c).mp (hc ▸ a.property)
    exact ⟨n, by simpa [hc] using hn⟩
  · obtain ⟨n, hn⟩ := linear_scalar_integer false c (by simpa using hc ▸ a.property)
    exact ⟨n, by simpa [hc, leadingCoeff_mul] using hn⟩
  · obtain ⟨n, hn⟩ := linear_scalar_integer true c (by simpa using hc ▸ a.property)
    have hl : (X - 1 : ℚ[X]).leadingCoeff = 1 := by simpa using leadingCoeff_X_sub_C (1 : ℚ)
    exact ⟨n, by simpa [hc, leadingCoeff_mul, hl] using hn⟩
  · exact (not_atom_quad a c hc ha).elim

theorem z_not_atomic : ¬ Factorization.HasAtomicFactorization z := by
  rintro ⟨s, hs, hassoc⟩
  obtain ⟨m, hm⟩ := product_integer_leadingCoeff s fun a ha =>
    atom_leadingCoeff_integer (hs a ha) ((Multiset.dvd_prod ha).trans hassoc.dvd)
  obtain ⟨u, hu⟩ := hassoc
  obtain ⟨n, hn⟩ := eq_intCast_of_polynomial_unit (u.isUnit.map ring.subtype)
  have hlead := congrArg (fun v : ring => (v : ℚ[X]).leadingCoeff) hu
  have hl : (X - 1 : ℚ[X]).leadingCoeff = 1 := by simpa using leadingCoeff_X_sub_C (1 : ℚ)
  have hn' : ((u : ring) : ℚ[X]) = C (n : ℚ) := by rw [hn]; simp
  have he : (m : ℚ) * n = 1/2 := by
    simpa only [Subring.coe_mul, leadingCoeff_mul, hn', leadingCoeff_C, ← hm,
      z, quad, leadingCoeff_X, hl, mul_one] using hlead
  have hc : (2 : ℚ) * ((m*n : ℤ) : ℚ) = 1 := by push_cast; linarith
  have : (2 : ℤ) * (m*n) = 1 := by exact_mod_cast hc
  omega

theorem ring_not_atomic : ¬ Factorization.IsAtomicDomain ring := fun h => z_not_atomic (h z z_ne_zero)

/-- The failed factorization of the quadratic is repaired by the single atom 2. -/
theorem quadratic_repair :
    ¬ Factorization.HasAtomicFactorization z ∧ Irreducible (2 : ring) ∧
    Irreducible parameter ∧ Irreducible (parameter - 1) ∧
    2 * z = parameter * (parameter - 1) ∧ Factorization.HasAtomicFactorization (2 * z) := by
  refine ⟨z_not_atomic, prime_atom 2 Nat.prime_two, parameter_atom, parameter_sub_one_atom,
    two_mul_z, ?_⟩
  rw [two_mul_z]
  exact (Factorization.hasAtomicFactorization_of_irreducible parameter_atom).mul
    (Factorization.hasAtomicFactorization_of_irreducible parameter_sub_one_atom)

end UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial
