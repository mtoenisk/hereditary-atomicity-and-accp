import UnconditionalCounterexample.Variations.UnivariateCentres
import UnconditionalCounterexample.RationalSigns
import Factorization.Definitions
import UnconditionalCounterexample.Hierarchy.EvaluationRing

/-! # The two-point polynomial evaluation domain -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial

open GuardSupport Polynomial WithZero

private def centre (b : Bool) : ℕ := if b then 1 else 0

/-- Two transcendental points of exact displacement order one from 0 and 1. -/
def point (p : PrimeIndex) (b : Bool) : ℤ_[p.val] :=
  (Variations.UnivariateCentres.exists_primary_at p.val (centre b) 1 (by decide)).choose

theorem point_trans (p : PrimeIndex) (b : Bool) : Transcendental ℚ (point p b : ℚ_[p.val]) :=
  (Variations.UnivariateCentres.exists_primary_at p.val (centre b) 1 (by decide)).choose_spec.1

theorem point_residue (p : PrimeIndex) (b : Bool) : PadicInt.toZMod (point p b) = (if b then 1 else 0) := by
  have h := (Variations.UnivariateCentres.exists_primary_at p.val (centre b) 1 (by decide)).choose_spec.2.1
  change PadicInt.toZMod (point p b) = (centre b : ZMod p.val) at h
  cases b <;> simpa [centre] using h

theorem point_order (p : PrimeIndex) (b : Bool) :
    ((point p b).val - (if b then 1 else 0)).valuation = 1 := by
  have h := (Variations.UnivariateCentres.exists_primary_at p.val (centre b) 1 (by decide)).choose_spec.2.2
  change ((point p b).val - (centre b : ℚ_[p.val])).valuation = 1 at h
  cases b <;> simpa [centre] using h

def fibres (p : PrimeIndex) : Set ℤ_[p.val] := {point p false,point p true}

def value (p : PrimeIndex) (b : Bool) : ℚ[X] →+* ℚ_[p.val] := eval₂RingHom (Rat.castHom _) (point p b).val

@[simp] theorem value_C (p : PrimeIndex) (b : Bool) (a : ℚ) : value p b (C a) = a := by simp [value]
@[simp] theorem value_X (p : PrimeIndex) (b : Bool) : value p b X = (point p b).val := by simp [value]
@[simp] theorem value_mul (p : PrimeIndex) (b : Bool) (f g : ℚ[X]) : value p b (f*g) = value p b f * value p b g :=
  map_mul _ _ _

theorem value_ne_zero (p : PrimeIndex) (b : Bool) {f : ℚ[X]} (hf : f ≠ 0) : value p b f ≠ 0 := by
  change f.eval₂ (Rat.castHom _) _ ≠ 0
  rw [← show algebraMap ℚ ℚ_[p.val] = Rat.castHom ℚ_[p.val] from Subsingleton.elim ..]
  exact mt ((transcendental_iff.mp (point_trans p b)) f) hf

/-- The polynomial ring integral at each of the two chosen points over every prime. -/
abbrev ring := evaluationPolynomials fibres

theorem mem_ring (f : ℚ[X]) : f ∈ ring ↔ ∀ p b, ‖value p b f‖ ≤ 1 := by
  rw [mem_evaluationPolynomials_iff]
  constructor
  · intro h p b
    apply h
    cases b <;> simp [fibres]
  · intro h p a ha
    rcases ha with rfl | ha
    · exact h p false
    · exact Set.mem_singleton_iff.mp ha ▸ h p true

theorem X_mem : (X : ℚ[X]) ∈ ring := X_mem_evaluationPolynomials fibres

private theorem integer_of_norm (q : ℚ) (h : ∀ p : PrimeIndex, ‖(q : ℚ_[p.val])‖ ≤ 1) :
    ∃ z : ℤ, (z : ℚ) = q := by
  apply RationalSigns.integer_of_padic_le_one
  intro p
  have hval : Padic.mulValuation (q : ℚ_[p.val]) ≤ 1 := by
    apply le_of_not_gt
    intro hn
    have hv : Padic.mulValuation (1 : ℚ_[p.val]) < Padic.mulValuation (q : ℚ_[p.val]) := by simpa using hn
    exact (h p).not_gt (by simpa only [norm_one] using Padic.norm_lt_norm_iff_mulValuation_lt.mpr hv)
  exact congrArg (fun v : Valuation ℚ ℤᵐ⁰ => v q) (Padic.comap_mulValuation_eq_padicValuation (p := p.val)) ▸ hval

theorem constant_mem (q : ℚ) : C q ∈ ring ↔ ∃ z : ℤ, (z : ℚ) = q := by
  constructor
  · intro h
    exact integer_of_norm q fun p => by simpa using (mem_ring _).mp h p false
  · rintro ⟨z,rfl⟩
    rw [map_intCast]
    exact intCast_mem ring z

theorem linear_scalar_integer (b : Bool) (a : ℚ) (h : C a * (X - C (if b then 1 else 0)) ∈ ring) :
    ∃ n : ℤ, (n : ℚ) = a := by
  apply integer_of_norm a
  intro p
  let s := point p (!b) - (if b then 1 else 0)
  have hu : IsUnit s := by
    apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
    cases b <;> simp [s,point_residue]
  have hv : ‖(s : ℚ_[p.val])‖ = 1 := PadicInt.isUnit_iff.mp hu
  have H := (mem_ring _).mp h p (!b)
  simp only [value_mul,norm_mul,map_sub,value_X,value_C] at H
  have hs : ‖(point p (!b)).val - (((if b then 1 else 0) : ℚ) : ℚ_[p.val])‖ = 1 := by
    cases b <;> simpa [s] using hv
  rwa [hs,mul_one] at H

theorem eq_intCast_of_polynomial_unit {x : ring} (h : IsUnit x.val) : ∃ a : ℤ, x = a := by
  obtain ⟨c,_,hc⟩ := Polynomial.isUnit_iff.mp h
  obtain ⟨a,ha⟩ := (constant_mem c).mp (hc ▸ x.property)
  refine ⟨a,Subtype.ext ?_⟩
  rw [← hc,← ha,map_intCast]
  rfl

theorem prime_atom (p : ℕ) (hp : p.Prime) : Irreducible (p : ring) := by
  have hi : Irreducible (p : ℤ) := (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).irreducible
  constructor
  · intro h
    let pr : PrimeIndex := ⟨p,hp⟩
    let e := integralEvaluation fibres pr ⟨point pr false,Set.mem_insert ..⟩
    have : Fact p.Prime := ⟨hp⟩
    have hm := h.map ((PadicInt.toZMod : ℤ_[p] →+* ZMod p).comp e)
    simp at hm
  · intro x y he
    have hc : IsUnit (x.val*y.val) := by
      rw [← Subring.coe_mul, ← he]
      change IsUnit (p : ℚ[X])
      rw [← map_natCast (C : ℚ →+* ℚ[X]) p]
      exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℚ) ≠ 0)).map C
    obtain ⟨a,rfl⟩ := eq_intCast_of_polynomial_unit (isUnit_of_mul_isUnit_left hc)
    obtain ⟨b,rfl⟩ := eq_intCast_of_polynomial_unit (isUnit_of_mul_isUnit_right hc)
    have hEq : (p : ℤ) = a*b := by exact_mod_cast he
    exact (hi.isUnit_or_isUnit hEq).imp (fun h => h.map (Int.castRingHom ring)) (fun h => h.map (Int.castRingHom ring))

end UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial
