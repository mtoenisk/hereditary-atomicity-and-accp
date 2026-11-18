import UnconditionalCounterexample.GuardSupport
import UnconditionalCounterexample.GuardResidues
import UnconditionalCounterexample.EvaluationChoices
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The manuscript's logarithmic guards

In the construction of Proposition 3.1, new guard
representatives lie between floor(log₂ p) and twice that number, except for
the finite initial batch. The existing finite root bound selects such a residue
and an actual transcendental p-adic unit lifts it.

For every fixed nonzero integer polynomial V, the lower logarithmic bound
passes all integer roots, while the upper bound and polynomial growth give
0 < |V(w_p)| < p eventually. Reduction therefore detects an actual p-adic unit.
Coefficient clearing and numerator/denominator evaluation prove finite guard
valuation support for every nonzero rational function.

No integer-polynomial enumeration avoidance is assumed in this module. The
finite initial exception is expressed by an eventual interval hypothesis.
-/

namespace UnconditionalCounterexample.LogarithmicGuards

open Polynomial Filter Asymptotics GuardSupport


/-- The paper's exact finite guard choice, with the logarithmic representative
and an actual transcendental lift. The same bound also excludes residue one. -/
theorem exists_logarithmic_guard
    {p : ℕ} [Fact p.Prime] {J : Type*}
    (I : Finset J) (F : J → ℤ_[p][X]) (hF : ∀ j ∈ I, (F j).Monic)
    (hp : 2 ^ (4 + ∑ j ∈ I, (F j).natDegree) < p) :
    ∃ w : ℕ, ∃ β : ℤ_[p],
      Nat.log 2 p ≤ w ∧ w ≤ 2 * Nat.log 2 p ∧ 1 < w ∧ w < p ∧
      Transcendental ℚ β.val ∧ IsUnit β ∧ PadicInt.toZMod β = (w : ZMod p) ∧
      PadicInt.toZMod β ≠ 1 ∧ ∀ j ∈ I, IsUnit ((F j).eval β) := by
  obtain ⟨w, hwlo, hwhi, hw1, hwp, hw⟩ := GuardResidues.exists_guard_residue_of_monic
    I F PadicInt.toZMod hF hp
  have hnotdvd : ¬ p ∣ w := by
    intro hdvd
    have := Nat.le_of_dvd (by omega : 0 < w) hdvd
    omega
  obtain ⟨β, ht, hu, hr, _⟩ :=
    EvaluationChoices.exists_transcendental_unit_residue p w hnotdvd
  refine ⟨w, β, hwlo, hwhi, hw1, hwp, ht, hu, hr, ?_, ?_⟩
  · rw [hr]
    intro heq
    have hmod := (ZMod.natCast_eq_natCast_iff' w 1 p).mp (by simpa using heq)
    rw [Nat.mod_eq_of_lt hwp, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at hmod
    omega
  · intro j hj
    apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
    have hav := hw j hj
    rw [← hr, eval₂_at_apply] at hav
    exact hav

/-- Every fixed polynomial in the binary floor logarithm is eventually smaller
than its argument. No primality hypothesis is required. -/
theorem eventually_mul_log_pow_lt (C d : ℕ) :
    ∀ᶠ p : ℕ in atTop, C * (2 * Nat.log 2 p + 1) ^ d < p := by
  have ho : (fun x : ℝ => ((C : ℝ) * 3 ^ d) * Real.logb 2 x ^ d) =o[atTop] id :=
    (Real.isLittleO_pow_logb_id_atTop (b := 2) (n := d)).const_mul_left ((C : ℝ) * 3 ^ d)
  have he : ∀ᶠ p : ℕ in atTop,
      ‖((C : ℝ) * 3 ^ d) * Real.logb 2 p ^ d‖ ≤ (1 / 2 : ℝ) * ‖(p : ℝ)‖ :=
    (show Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop from
      tendsto_natCast_atTop_atTop).eventually (ho.bound (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [he, eventually_ge_atTop 2] with p hep hp
  have hn : 1 ≤ Nat.log 2 p := Nat.le_log_of_pow_le (by decide) (by simpa using hp)
  have hnat : 2 * Nat.log 2 p + 1 ≤ 3 * Nat.log 2 p := by omega
  have hlog : (Nat.log 2 p : ℝ) ≤ Real.logb 2 p := Real.natLog_le_logb p 2
  have hbase : ((2 * Nat.log 2 p + 1 : ℕ) : ℝ) ≤ 3 * Real.logb 2 p := by
    have hnat' : ((2 * Nat.log 2 p + 1 : ℕ) : ℝ) ≤ 3 * (Nat.log 2 p : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (2 * Nat.log 2 p + 1)) hbase d
  have hbound : (C : ℝ) * ((2 * Nat.log 2 p + 1 : ℕ) : ℝ) ^ d ≤
      ((C : ℝ) * 3 ^ d) * Real.logb 2 p ^ d := by
    simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg C)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hfinal : (C : ℝ) * ((2 * Nat.log 2 p + 1 : ℕ) : ℝ) ^ d < p := by
    calc
      _ ≤ ((C : ℝ) * 3 ^ d) * Real.logb 2 p ^ d := hbound
      _ ≤ ‖((C : ℝ) * 3 ^ d) * Real.logb 2 p ^ d‖ := le_abs_self _
      _ ≤ (1 / 2 : ℝ) * ‖(p : ℝ)‖ := hep
      _ < p := by rw [Real.norm_eq_abs, abs_of_pos hpR]; linarith
  exact_mod_cast hfinal


/-- A coefficient-sum bound uniform in the nonnegative integer argument. -/
theorem natAbs_eval_le (U : ℤ[X]) (w : ℕ) :
    (U.eval (w : ℤ)).natAbs ≤
      (∑ j ∈ U.support, (U.coeff j).natAbs) * (w + 1) ^ U.natDegree := by
  rw [eval_eq_sum, Polynomial.sum]
  calc
    (∑ j ∈ U.support, U.coeff j * (w : ℤ) ^ j).natAbs ≤
        ∑ j ∈ U.support, (U.coeff j * (w : ℤ) ^ j).natAbs := Int.natAbs_sum_le _ _
    _ ≤ (∑ j ∈ U.support, (U.coeff j).natAbs) * (w + 1) ^ U.natDegree := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      apply Nat.mul_le_mul_left
      exact (Nat.pow_le_pow_left (Nat.le_succ w) j).trans
        (Nat.pow_le_pow_right (Nat.succ_pos w) (le_natDegree_of_mem_supp j hj))

/-- Integer evaluation cannot vanish once the logarithmic lower bound has
passed the finitely many roots of a fixed nonzero polynomial. -/
theorem eventually_eval_ne_zero_on_log_interval (U : ℤ[X]) (hU : U ≠ 0) :
    ∀ᶠ p : ℕ in atTop, ∀ w : ℕ, Nat.log 2 p ≤ w → U.eval (w : ℤ) ≠ 0 := by
  obtain ⟨B, hB⟩ := U.exists_max_root hU
  filter_upwards [eventually_ge_atTop (2 ^ (B.natAbs + 1))] with p hp
  intro w hw hzero
  have hlog : B.natAbs + 1 ≤ Nat.log 2 p := Nat.le_log_of_pow_le (by decide) hp
  have hroot : (w : ℤ) ≤ B := hB _ hzero
  have hBabs : B ≤ (B.natAbs : ℤ) := Int.le_natAbs
  omega

/-- The rational-prime values tend to infinity along the cofinite filter. -/
theorem eventually_prime_ge (N : ℕ) :
    ∀ᶠ p : PrimeIndex in cofinite, N ≤ p.val := by
  apply Filter.eventually_cofinite.mpr
  apply ((Finset.range N).subtype Nat.Prime).finite_toSet.subset
  intro p hp
  change ¬ N ≤ p.val at hp
  exact Finset.mem_subtype.mpr (Finset.mem_range.mpr (by omega))

/-- Transfer a natural eventual statement to all but finitely many rational primes. -/
theorem eventually_primes_of_eventually_nat {P : ℕ → Prop}
    (h : ∀ᶠ n : ℕ in atTop, P n) : ∀ᶠ p : PrimeIndex in cofinite, P p.val := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  filter_upwards [eventually_prime_ge N] with p hp
  exact hN p.val hp

/-- The precise integer estimate used in the paper's passage to all primes. -/
theorem eventually_natAbs_eval_bounds_on_log_interval (U : ℤ[X]) (hU : U ≠ 0) :
    ∀ᶠ p : ℕ in atTop, ∀ w : ℕ, Nat.log 2 p ≤ w → w ≤ 2 * Nat.log 2 p →
      0 < (U.eval (w : ℤ)).natAbs ∧ (U.eval (w : ℤ)).natAbs < p := by
  filter_upwards [eventually_eval_ne_zero_on_log_interval U hU,
    eventually_mul_log_pow_lt (∑ j ∈ U.support, (U.coeff j).natAbs) U.natDegree]
    with p hn hb
  intro w hwlo hwhi
  refine ⟨Int.natAbs_pos.mpr (hn w hwlo), ?_⟩
  apply (natAbs_eval_le U w).trans_lt
  apply lt_of_le_of_lt ?_ hb
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (by omega : w + 1 ≤ 2 * Nat.log 2 p + 1) U.natDegree

section LogarithmicArguments

variable (β : (p : PrimeIndex) → ℤ_[p.val]) (w : PrimeIndex → ℕ)
  (hres : ∀ p, PadicInt.toZMod (β p) = (w p : ZMod p.val))
  (hinterval : ∀ᶠ p : PrimeIndex in cofinite,
    Nat.log 2 p.val ≤ w p ∧ w p ≤ 2 * Nat.log 2 p.val)

include hres hinterval

/-- Logarithmic representatives force every fixed integer polynomial to be a
unit at all but finitely many actual guard arguments. -/
theorem eventually_intPolynomial_isUnit (U : ℤ[X]) (hU : U ≠ 0) :
    ∀ᶠ p : PrimeIndex in cofinite,
      IsUnit (U.eval₂ (Int.castRingHom ℤ_[p.val]) (β p)) := by
  have hb := eventually_primes_of_eventually_nat
    (eventually_natAbs_eval_bounds_on_log_interval U hU)
  filter_upwards [hb, hinterval] with p hp hi
  obtain ⟨hpos, hlt⟩ := hp (w p) hi.1 hi.2
  apply intPolynomial_eval_unit_of_residue_nonzero
  have heval : U.eval₂ (Int.castRingHom (ZMod p.val)) (PadicInt.toZMod (β p)) =
      ((U.eval (w p : ℤ) : ℤ) : ZMod p.val) := by
    rw [hres p]
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      (Polynomial.eval₂_at_apply (p := U) (Int.castRingHom (ZMod p.val)) (w p : ℤ))
  rw [heval]
  intro hz
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd (U.eval (w p : ℤ)) p.val).mp hz
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv (Int.natAbs_pos.mp hpos)
  exact (not_le_of_gt hlt) (by simpa using hle)

theorem eventually_intPolynomial_norm_one (U : ℤ[X]) (hU : U ≠ 0) :
    ∀ᶠ p : PrimeIndex in cofinite,
      ‖U.eval₂ (Int.castRingHom ℚ_[p.val]) (β p).val‖ = 1 := by
  filter_upwards [eventually_intPolynomial_isUnit β w hres hinterval U hU] with p hp
  rw [← coe_intPolynomial_eval]
  exact PadicInt.isUnit_iff.mp hp

theorem eventually_ratPolynomial_norm_one (f : ℚ[X]) (hf : f ≠ 0) :
    ∀ᶠ p : PrimeIndex in cofinite,
      ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) (β p).val‖ = 1 := by
  obtain ⟨d, V, hd, hV, hmul⟩ := exists_integer_multiple f hf
  have hVn := eventually_intPolynomial_norm_one β w hres hinterval V hV
  have hdn := eventually_intPolynomial_norm_one β w hres hinterval
    (Polynomial.C d) (by simpa using hd)
  filter_upwards [hVn, hdn] with p hpV hpd
  simp only [eval₂_C] at hpd
  change ‖(d : ℚ_[p.val])‖ = 1 at hpd
  have heval := congrArg (Polynomial.eval₂ (algebraMap ℚ ℚ_[p.val]) (β p).val) hmul
  have hc : (algebraMap ℚ ℚ_[p.val]).comp (algebraMap ℤ ℚ) =
      Int.castRingHom ℚ_[p.val] := Subsingleton.elim _ _
  rw [eval₂_map, eval₂_mul, eval₂_C, hc] at heval
  simp only [map_intCast] at heval
  have hn := congrArg norm heval
  rw [norm_mul, hpd, one_mul, hpV] at hn
  exact hn.symm

/-- The paper's logarithmic guard choice gives finite support for the actual
rational-function evaluation valuations, without enumeration avoidance. -/
theorem ratFunc_guardSupport_finite
    (htrans : (p : PrimeIndex) → Transcendental ℚ (β p).val)
    (f : RatFunc ℚ) (hf : f ≠ 0) :
    {p : PrimeIndex |
      EvaluationDVR.valuation p.val (guardEvaluation β htrans p) f ≠ 1}.Finite := by
  apply Filter.eventually_cofinite.mp
  have hn := eventually_ratPolynomial_norm_one β w hres hinterval
    f.num (RatFunc.num_ne_zero hf)
  have hd := eventually_ratPolynomial_norm_one β w hres hinterval
    f.denom (RatFunc.denom_ne_zero f)
  filter_upwards [hn, hd] with p hpn hpd
  apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
  have heval : guardEvaluation β htrans p f =
      aeval (β p).val f.num / aeval (β p).val f.denom :=
    LocalEvaluation.evalAt_apply _ _ _
  rw [heval, norm_div]
  change ‖f.num.eval₂ (algebraMap ℚ ℚ_[p.val]) (β p).val‖ /
    ‖f.denom.eval₂ (algebraMap ℚ ℚ_[p.val]) (β p).val‖ = 1
  rw [hpn, hpd, div_self one_ne_zero]

end LogarithmicArguments

end UnconditionalCounterexample.LogarithmicGuards
