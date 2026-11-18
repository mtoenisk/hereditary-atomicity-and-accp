import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Guard residues avoiding previous polynomial roots

Choose a guard residue between floor(log₂ p) and twice that number. The cutoff
supplies more choices than the total number of roots of the preceding polynomials.
Representatives are distinct modulo p and avoid zero and one.

The monic version works with any supplied reduction homomorphism; it does not
assume a homomorphism from the rational field to a finite field. Construction
of that coefficient ring and reduction map remains a separate input.
-/

namespace UnconditionalCounterexample.GuardResidues

open Polynomial

/-- A finite collection of nonzero polynomials cannot cover an injectively
labelled finite set with more points than the sum of their degrees. -/
theorem exists_simultaneous_nonzero_of_card
    {K X J : Type*} [CommRing K] [IsDomain K] [Fintype X]
    (f : X → K) (hf : Function.Injective f)
    (I : Finset J) (P : J → K[X])
    (hP : ∀ j ∈ I, P j ≠ 0)
    (hcard : (∑ j ∈ I, (P j).natDegree) < Fintype.card X) :
    ∃ x : X, ∀ j ∈ I, (P j).eval (f x) ≠ 0 := by
  classical
  let Q : K[X] := ∏ j ∈ I, P j
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr hP
  have hdeg : Q.natDegree < Fintype.card X :=
    (Polynomial.natDegree_prod_le I P).trans_lt hcard
  have hex : ∃ x : X, Q.eval (f x) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hQ (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q hf hn hdeg)
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, ?_⟩
  have hprod : (∏ j ∈ I, (P j).eval (f x)) ≠ 0 := by
    simpa only [Q, eval_prod] using hx
  exact Finset.prod_ne_zero_iff.mp hprod

/-- Beyond the small initial range, twice a natural number is below its power
of two. -/
theorem two_mul_lt_two_pow {n : ℕ} (hn : 3 ≤ n) : 2 * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Nat.pow_succ]
    omega

/-- The logarithmic interval has more than D entries and lies strictly between
one and p under the construction's explicit prime cutoff. -/
theorem log_interval_bounds {p D : ℕ} (hp : 2 ^ (4 + D) < p) :
    D < (Finset.Icc (Nat.log 2 p) (2 * Nat.log 2 p)).card ∧
      1 < Nat.log 2 p ∧ 2 * Nat.log 2 p < p := by
  have hlog : 4 + D ≤ Nat.log 2 p := Nat.le_log_of_pow_le (by decide) hp.le
  have hp0 : p ≠ 0 := Nat.ne_of_gt ((Nat.two_pow_pos (4 + D)).trans hp)
  have hupper : 2 * Nat.log 2 p < p :=
    (two_mul_lt_two_pow (by omega)).trans_le (Nat.pow_log_le_self 2 hp0)
  refine ⟨?_, by omega, hupper⟩
  rw [Nat.card_Icc]
  omega

/-- A guard residue can avoid every earlier reduced polynomial while staying in
the prescribed logarithmic interval. The representative also avoids 0 and 1. -/
theorem exists_guard_residue
    {p : ℕ} [Fact p.Prime] {J : Type*}
    (I : Finset J) (P : J → (ZMod p)[X])
    (hP : ∀ j ∈ I, P j ≠ 0)
    (hp : 2 ^ (4 + ∑ j ∈ I, (P j).natDegree) < p) :
    ∃ w : ℕ, Nat.log 2 p ≤ w ∧ w ≤ 2 * Nat.log 2 p ∧
      1 < w ∧ w < p ∧ ∀ j ∈ I, (P j).eval (w : ZMod p) ≠ 0 := by
  classical
  obtain ⟨hcard, hlow, hupp⟩ := log_interval_bounds hp
  let S := Finset.Icc (Nat.log 2 p) (2 * Nat.log 2 p)
  have hinj : Function.Injective (fun w : S => (w.val : ZMod p)) := by
    intro a b h
    apply Subtype.ext
    have ha : a.val < p := lt_of_le_of_lt (Finset.mem_Icc.mp a.property).2 hupp
    have hb : b.val < p := lt_of_le_of_lt (Finset.mem_Icc.mp b.property).2 hupp
    have heq := (ZMod.natCast_eq_natCast_iff' a.val b.val p).mp h
    simpa only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using heq
  obtain ⟨w, hw⟩ := exists_simultaneous_nonzero_of_card
    (fun w : S => (w.val : ZMod p)) hinj I P hP (by simpa [S] using hcard)
  have hwI := Finset.mem_Icc.mp w.property
  exact ⟨w.val, hwI.1, hwI.2, hlow.trans_le hwI.1, hwI.2.trans_lt hupp, hw⟩

/-- Monic polynomials stay nonzero under reduction. The cutoff may therefore
use their degrees before reduction in any specified coefficient ring. -/
theorem exists_guard_residue_of_monic
    {p : ℕ} [Fact p.Prime] {J R : Type*} [Semiring R]
    (I : Finset J) (P : J → R[X]) (φ : R →+* ZMod p)
    (hP : ∀ j ∈ I, (P j).Monic)
    (hp : 2 ^ (4 + ∑ j ∈ I, (P j).natDegree) < p) :
    ∃ w : ℕ, Nat.log 2 p ≤ w ∧ w ≤ 2 * Nat.log 2 p ∧
      1 < w ∧ w < p ∧ ∀ j ∈ I, (P j).eval₂ φ (w : ZMod p) ≠ 0 := by
  have hdeg : (∑ j ∈ I, ((P j).map φ).natDegree) =
      ∑ j ∈ I, (P j).natDegree := by
    apply Finset.sum_congr rfl
    intro j hj
    exact (hP j hj).natDegree_map φ
  obtain ⟨w, hwl, hwu, hw1, hwp, hw⟩ := exists_guard_residue I
    (fun j => (P j).map φ) (fun j hj => ((hP j hj).map φ).ne_zero) (by simpa [hdeg] using hp)
  refine ⟨w, hwl, hwu, hw1, hwp, ?_⟩
  simpa only [eval_map] using hw

end UnconditionalCounterexample.GuardResidues
