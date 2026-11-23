import UnconditionalCounterexample.RadicalConductor
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.Tactic.Linarith

/-!
# Recovering the radical of a local conductor

The coefficients of an auxiliary polynomial generate the ideal of
the retained points. At unbounded stages the word estimates give large inverse
powers of the uniformizer times an approximate value of a fixed power of this
polynomial. Successively isolating its coefficients in the subring puts each
in the actual conductor. Reducing modulo primes and testing integral values at
the retained points then identifies the radical.
-/

namespace UnconditionalCounterexample.Variations

open Polynomial RadicalConductor

variable {B : Type*} [CommRing B]

private theorem mul_inv_pow_add (u : Bˣ) (a b : ℕ) :
    (u : B)^a * (↑(u⁻¹) : B)^(a+b) = (↑(u⁻¹) : B)^b := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  simp

/-- All the coefficients of a local scheduling polynomial belong to the actual conductor
when evaluations on unbounded stages have quadratic growth in their denominator exponents. -/
theorem coeff_mem_conductor_of_scaled_evaluations (T : Subring B) (u : Bˣ)
    (hu : (u : B) ∈ T) (hclear : ∀ x : B, ∃ k : ℕ, (u : B)^k * x ∈ T)
    (F : B[X]) (hc : ∀ j, F.coeff j ∈ T)
    (heval : ∀ n : ℕ, ∃ i ≥ n,
      (↑(u⁻¹) : B)^(i*i) * F.eval ((u : B)^i) ∈ T) :
    ∀ e, F.coeff e ∈ conductorIdeal T := by
  classical
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    have hdivide (k : ℕ) : (↑(u⁻¹) : B)^k * F.coeff e ∈ T := by
      obtain ⟨i, hi, hstage⟩ := heval (e + k + 1)
      have hscale : i*e+k ≤ i*i := by nlinarith [Nat.mul_le_mul_left i hi]
      obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hscale
      have hbase : (↑(u⁻¹) : B)^(i*e+k) * F.eval ((u : B)^i) ∈ T := by
        have h := T.mul_mem (T.pow_mem hu s) hstage
        rwa [hs, Nat.add_comm (i*e+k) s, ← mul_assoc, mul_inv_pow_add] at h
      let term (j : ℕ) := F.coeff j * ((↑(u⁻¹) : B)^(i*e+k) * (u : B)^(i*j))
      let t := Finset.range (max F.natDegree e + 1)
      have hsum : ∑ j ∈ t, term j ∈ T := by
        rw [eval_eq_sum_range' (n := max F.natDegree e + 1) (by omega), Finset.mul_sum] at hbase
        simpa only [term, t, mul_comm, mul_left_comm, mul_assoc, pow_mul] using hbase
      have he : e ∈ t := Finset.mem_range.mpr (by omega)
      have htail : ∑ j ∈ t.erase e, term j ∈ T := by
        apply T.sum_mem
        intro j hj
        obtain hlt | hgt := lt_or_gt_of_ne (Finset.ne_of_mem_erase hj)
        · exact ih j hlt _
        · have hj' : i*e+k ≤ i*j := by
            nlinarith [Nat.mul_le_mul_left i (show e+1 ≤ j by omega)]
          obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hj'
          dsimp only [term]
          rw [hs]
          have hcancel := mul_inv_pow_add u⁻¹ (i*e+k) s
          simp only [inv_inv] at hcancel
          rw [hcancel]
          exact T.mul_mem (hc j) (T.pow_mem hu s)
      rw [← Finset.add_sum_erase t term he] at hsum
      have hsingle : term e ∈ T := by simpa using T.sub_mem hsum htail
      dsimp only [term] at hsingle
      rw [mul_comm _ ((u : B)^(i*e)), mul_inv_pow_add, mul_comm] at hsingle
      exact hsingle
    intro z
    obtain ⟨k, hk⟩ := hclear z
    have h := T.mul_mem (hdivide k) hk
    convert h using 1
    have hinv : (↑(u⁻¹) : B)^k * (u : B)^k = 1 := by rw [← mul_pow]; simp
    calc
      F.coeff e * z = ((↑(u⁻¹) : B)^k * (u : B)^k) * (F.coeff e * z) := by rw [hinv, one_mul]
      _ = _ := by ring

/-- If every coefficient of some positive power of a polynomial belongs to an ideal,
its coefficients belong to the radical. -/
theorem contentIdeal_le_radical_of_pow_coeff_mem (I : Ideal B) (F : B[X]) (a : ℕ)
    (hc : ∀ e, (F ^ a).coeff e ∈ I) :
    F.contentIdeal ≤ I.radical := by
  classical
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hIP, hP⟩ ↦ ?_
  let := hP
  have hpow : (F.map (Ideal.Quotient.mk P)) ^ a = 0 := by
    rw [← Polynomial.map_pow]
    ext e
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIP (hc e))
  have hF : F.map (Ideal.Quotient.mk P) = 0 := by
    by_contra hn
    exact pow_ne_zero a hn hpow
  rw [Polynomial.contentIdeal_def, Ideal.span_le]
  intro v hv
  obtain ⟨e, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hv
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using congrArg (fun Q : (B ⧸ P)[X] ↦ Q.coeff e) hF)

/-- Integral values force the conductor to vanish at a closed point, including points
whose residue field extends the scalar field. -/
theorem conductor_le_ker_of_bounded_surjective {E : Type*} [NontriviallyNormedField E]
    (T : Subring B) (f : B →+* E) (hf : Function.Surjective f)
    (hint : ∀ z ∈ T, ‖f z‖ ≤ 1) : conductorIdeal T ≤ RingHom.ker f := by
  intro x hx
  change f x = 0
  by_contra hne
  obtain ⟨b, hb⟩ := NormedField.exists_one_lt_norm E
  obtain ⟨z, hz⟩ := hf (b / f x)
  have h := hint _ (hx z)
  rw [map_mul, hz, mul_comm, div_mul_cancel₀ _ hne] at h
  exact hb.not_ge h

/-- Passing to a fixed power preserves congruence at the original precision. -/
private theorem scaled_pow_sub_mem (T : Subring B) (w a b : B)
    (ha : a ∈ T) (hb : b ∈ T) (hd : w * (a - b) ∈ T) (e : ℕ) :
    w * (a^e - b^e) ∈ T := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h := T.add_mem (T.mul_mem ih ha) (T.mul_mem hd (T.pow_mem hb e))
    convert h using 1
    ring

/-- Quadratically accurate approximations to the scheduling polynomial and the normalized
word powers give the radical of the actual conductor. The generators of the point ideal
are the coefficients of the scheduling polynomial. -/
theorem radical_conductor_of_approximating_words {ι : Type*} {E : ι → Type*}
    [∀ j, NontriviallyNormedField (E j)] (T : Subring B) (u : Bˣ) (hu : (u : B) ∈ T)
    (hclear : ∀ x : B, ∃ k : ℕ, (u : B)^k * x ∈ T) (F : T[X]) (a : ℕ)
    (ev : ∀ j, B →+* E j) (hsurj : ∀ j, Function.Surjective (ev j))
    (hint : ∀ j z, z ∈ T → ‖ev j z‖ ≤ 1)
    (hgen : (F.map T.subtype).contentIdeal = ⨅ j, RingHom.ker (ev j))
    (hword : ∀ n : ℕ, ∃ i ≥ n, ∃ P : T, ∃ δ : T,
        (P : B) - (F.map T.subtype).eval ((u : B)^i) = (u : B)^(i*i) * δ ∧
        (↑(u⁻¹) : B)^(i*i) * (P : B)^a ∈ T) :
    (conductorIdeal T).radical = ⨅ j, RingHom.ker (ev j) := by
  let V := F.map T.subtype
  have hcoeff (e : ℕ) : (V ^ a).coeff e ∈ T := by
    rw [show V ^ a = (F ^ a).map T.subtype from (Polynomial.map_pow ..).symm, Polynomial.coeff_map]
    exact ((F ^ a).coeff e).property
  have heval (n : ℕ) : ∃ i ≥ n, (↑(u⁻¹) : B)^(i*i) * (V ^ a).eval ((u : B)^i) ∈ T := by
    obtain ⟨i, hi, P, δ, heq, hp⟩ := hword n
    refine ⟨i, hi, ?_⟩
    let b := V.eval ((u : B)^i)
    have hb : b ∈ T := by
      let t : T := ⟨(u : B)^i, T.pow_mem hu i⟩
      have h : T.subtype (F.eval t) = b := by
        exact (Polynomial.eval_map_apply T.subtype t).symm
      exact h ▸ (F.eval t).property
    have hd : (↑(u⁻¹) : B)^(i*i) * ((P : B) - b) ∈ T := by
      change (↑(u⁻¹) : B)^(i*i) * ((P : B) - V.eval ((u : B)^i)) ∈ T
      rw [show (P : B) - V.eval ((u : B)^i) = _ from heq, ← mul_assoc, ← mul_pow]
      simp
    have h := T.sub_mem hp (scaled_pow_sub_mem T _ _ _ P.property hb hd a)
    rw [mul_sub, sub_sub_cancel] at h
    simpa only [b, Polynomial.eval_pow] using h
  apply le_antisymm
  · refine le_iInf fun j ↦ (RingHom.ker_isPrime (ev j)).radical_le_iff.mpr ?_
    exact conductor_le_ker_of_bounded_surjective T (ev j) (hsurj j) (hint j)
  · rw [← hgen]
    exact contentIdeal_le_radical_of_pow_coeff_mem _ V a
      (coeff_mem_conductor_of_scaled_evaluations T u hu hclear _ hcoeff heval)

end UnconditionalCounterexample.Variations
