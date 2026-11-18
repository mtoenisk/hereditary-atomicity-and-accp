import UnconditionalCounterexample.ShiftedEisenstein
import UnconditionalCounterexample.AffineNormEscape
import Lean.Elab.Tactic.Omega

/-!
# Simultaneous signed constant and exponent selection

The signed constant in Proposition 3.1 fixes the denominator at all chosen primes. Stages begin at one. Each exponent is a positive multiple
of `ell-1` and meets the paper budget `h + stage ≤ N`. Actual local norms and valuations are
computed from the finite prime product, so choices at distinct primes are
independent. The same choice meets finite affine derivative bounds, gives the
coefficient clearing precision, and supplies the auxiliary Fermat residue.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace UnconditionalCounterexample.SignedConstant

/-- The source denominator contains precisely the chosen processed-prime powers. -/
def denominator {ι : Type*} [Fintype ι] (p : ι → ℕ) (N : ι → ℕ) : ℕ := ∏ i, p i ^ N i

/-- The signed constant prescribed in Proposition 3.1. -/
def constant {ι : Type*} [Fintype ι] (p : ι → ℕ) (N : ι → ℕ) (d : ℕ) : ℚ :=
  (-1) ^ d / denominator p N

theorem denominator_ne_zero {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (N : ι → ℕ) : denominator p N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero)

theorem constant_ne_zero {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (N : ι → ℕ) (d : ℕ) : constant p N d ≠ 0 := by
  exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Nat.cast_ne_zero.mpr (denominator_ne_zero p hp N))

theorem denominator_prime_support {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (N : ι → ℕ)
    (q : ℕ) (hq : q.Prime) (hdiv : q ∣ denominator p N) : ∃ i, q = p i := by
  obtain ⟨i, _, hi⟩ := ((Nat.prime_iff.mp hq).dvd_finsetProd_iff _).mp hdiv
  exact ⟨i, Nat.prime_eq_prime_of_dvd_pow hq (hp i) hi⟩

theorem constant_denominator_support {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (N : ι → ℕ) (d : ℕ)
    (q : ℕ) (hq : q.Prime) (hdiv : q ∣ (constant p N d).den) : ∃ i, q = p i := by
  have hden : (constant p N d).den ∣ denominator p N := by
    simpa only [constant, Int.cast_pow, Int.cast_neg, Int.cast_one] using
      CoefficientApproximation.denominator_divides ((-1 : ℤ) ^ d) (denominator p N)
  exact denominator_prime_support p hp N q hq (hdiv.trans hden)

/-- At one processed prime, every other denominator factor has norm one. -/
theorem norm_denominator_at_processed {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (N : ι → ℕ) (i : ι) :
    ‖(denominator p N : ℚ_[p i])‖ = (p i : ℝ)⁻¹ ^ N i := by
  classical
  simp only [denominator, Nat.cast_prod, Nat.cast_pow, norm_prod, norm_pow]
  rw [Finset.prod_eq_single i]
  · rw [Padic.norm_p]
  · intro j _ hji
    have hu : ‖(p j : ℚ_[p i])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr
      ((Nat.coprime_primes (show (p i).Prime from Fact.out)
        (show (p j).Prime from Fact.out)).mpr (hinj.ne hji.symm))
    simp only [hu, one_pow]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Exact local growth, independent of the exponents chosen at all other primes. -/
theorem norm_constant_at_processed {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (N : ι → ℕ) (d : ℕ) (i : ι) : ‖(constant p N d : ℚ_[p i])‖ = (p i : ℝ) ^ N i := by
  simp only [constant, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Rat.cast_natCast, norm_div, norm_pow, norm_neg, norm_one, one_pow,
    norm_denominator_at_processed p hinj N i, one_div, inv_pow, inv_inv]

/-- The additive valuation has exactly the sign and exponent used in the paper. -/
theorem valuation_constant_at_processed {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (N : ι → ℕ) (d : ℕ) (i : ι) : (constant p N d : ℚ_[p i]).valuation = -(N i : ℤ) := by
  have hc0 : (constant p N d : ℚ_[p i]) ≠ 0 := Rat.cast_ne_zero.mpr
    (constant_ne_zero p (fun j => Fact.out) N d)
  have hnorm := norm_constant_at_processed p hinj N d i
  rw [Padic.norm_eq_zpow_neg_valuation hc0, ← zpow_natCast] at hnorm
  have hp1 : (1 : ℝ) < p i := by exact_mod_cast (show (p i).Prime from Fact.out).one_lt
  have he := zpow_right_injective₀ (zero_lt_one.trans hp1) (ne_of_gt hp1) hnorm
  omega

/-- The constant is a unit in norm at every unassigned prime. -/
theorem norm_constant_at_unassigned {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (N : ι → ℕ) (d : ℕ)
    (q : ℕ) [Fact q.Prime] (hfresh : ∀ i, p i ≠ q) : ‖(constant p N d : ℚ_[q])‖ = 1 := by
  have hu (i : ι) : ‖(p i : ℚ_[q])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr
    ((Nat.coprime_primes (show q.Prime from Fact.out) (hp i)).mpr (hfresh i).symm)
  have hden : ‖(denominator p N : ℚ_[q])‖ = 1 := by
    simp only [denominator, Nat.cast_prod, Nat.cast_pow, norm_prod, norm_pow,
      hu, one_pow, Finset.prod_const_one]
  simp only [constant, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Rat.cast_natCast, norm_div, norm_pow, norm_neg, norm_one, one_pow, hden, div_one]

/-- A positive multiple can exceed a natural budget and any real norm threshold. -/
theorem exists_large_multiple (m p budget : ℕ) (hm : 0 < m) (hp : 1 < p) (B : ℝ) :
    ∃ e : ℕ, 0 < e ∧ budget < m * e ∧ B < (p : ℝ) ^ (m * e) := by
  obtain ⟨k, hk⟩ := exists_nat_gt B
  let e := k + budget + 1
  have he : e ≤ m * e := Nat.le_mul_of_pos_left e hm
  have hbudget : budget < m * e := (show budget < e by dsimp [e]; omega).trans_le he
  have hkN : k ≤ m * e := (show k ≤ e by dsimp [e]; omega).trans he
  refine ⟨e, by dsimp [e]; omega, hbudget, ?_⟩
  apply (hk.trans_le (Nat.cast_le.mpr hkN)).trans
  exact_mod_cast (Nat.lt_pow_self hp : m * e < p ^ (m * e))

/-- Simultaneous source constant selection with independent local exponent growth.
All local real thresholds are fixed before the exponents are chosen. -/
theorem exists_constant_exponents {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (d stage : ℕ) (hstage : 1 ≤ stage) (h : ι → ℕ) (B : ι → ℝ) :
    ∃ N : ι → ℕ,
      (∀ i, ∃ e : ℕ, 0 < e ∧ N i = (ell - 1) * e) ∧
      (∀ i, 0 < N i) ∧
      (∀ i, h i + stage ≤ N i) ∧
      (∀ i, B i < ‖(constant p N d : ℚ_[p i])‖) ∧
      ∃ c : ℤ_[ell], (c : ℚ_[ell]) = (constant p N d : ℚ_[ell]) ∧
        PadicInt.toZModPow 1 c = (-1) ^ d := by
  have hm : 0 < ell - 1 := Nat.sub_pos_of_lt (show ell.Prime from Fact.out).one_lt
  choose e he hbudget hlarge using fun i => exists_large_multiple (ell - 1) (p i)
    (h i + stage) hm (show (p i).Prime from Fact.out).one_lt (B i)
  let N : ι → ℕ := fun i => (ell - 1) * e i
  refine ⟨N, fun i => ⟨e i, he i, rfl⟩,
    fun i => (Nat.zero_lt_one.trans_le hstage).trans_le
      ((show stage ≤ h i + stage by omega).trans (hbudget i).le),
    fun i => (hbudget i).le, ?_, ?_⟩
  · intro i
    rw [norm_constant_at_processed p hinj N d i]
    exact hlarge i
  · apply ShiftedEisenstein.exists_signed_reciprocal_model ell d (denominator p N)
    apply ShiftedEisenstein.supported_denominator_residue_one
    intro i
    exact (Nat.coprime_primes (show (p i).Prime from Fact.out)
      (show ell.Prime from Fact.out)).mpr (hfresh i)

/-- The constant has an actual unit model at every unassigned prime. -/
theorem exists_unit_at_unassigned {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (N : ι → ℕ) (d : ℕ)
    (q : ℕ) [Fact q.Prime] (hfresh : ∀ i, p i ≠ q) :
    ∃ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) = (constant p N d : ℚ_[q]) := by
  have hnorm := norm_constant_at_unassigned p hp N d q hfresh
  let x : ℤ_[q] := ⟨(constant p N d : ℚ_[q]), hnorm.le⟩
  have hx : IsUnit x := PadicInt.isUnit_iff.mpr hnorm
  exact ⟨hx.unit, by rw [hx.unit_spec]⟩

/-- A strict norm threshold is exactly the desired strict negative valuation bound. -/
theorem valuation_lt_neg_of_pow_lt_norm (p : ℕ) [Fact p.Prime]
    (x : ℚ_[p]) (i : ℕ) (hx : (p : ℝ) ^ i < ‖x‖) : x.valuation < -(i : ℤ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show p.Prime from Fact.out).one_lt
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((pow_pos (zero_lt_one.trans hp1) i).trans hx)
  rw [Padic.norm_eq_zpow_neg_valuation hx0, ← zpow_natCast,
    zpow_lt_zpow_iff_right₀ hp1] at hx
  omega

/-- One signed rational constant meets all finite affine derivative conditions,
all additional fixed local norm thresholds, and the paper's clearing budgets.
The affine coefficients are fixed independently of the chosen exponents. -/
theorem exists_constant_for_affine_bounds {ι κ : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (d stage : ℕ) (hstage : 1 ≤ stage) (h : ι → ℕ) (B : ι → ℝ)
    (t : ι → Finset κ) (s b : ∀ i, κ → ℚ_[p i])
    (hs : ∀ i j, j ∈ t i → s i j ≠ 0) :
    ∃ N : ι → ℕ,
      (∀ i, ∃ e : ℕ, 0 < e ∧ N i = (ell - 1) * e) ∧
      (∀ i, 0 < N i) ∧
      (∀ i, h i + stage ≤ N i) ∧
      (∀ i, B i < ‖(constant p N d : ℚ_[p i])‖) ∧
      (∀ i j, j ∈ t i →
        ‖b i j‖ < ‖s i j * (constant p N d : ℚ_[p i])‖ ∧
        (s i j * (constant p N d : ℚ_[p i]) + b i j).valuation < -(stage : ℤ)) ∧
      ∃ c : ℤ_[ell], (c : ℚ_[ell]) = (constant p N d : ℚ_[ell]) ∧
        PadicInt.toZModPow 1 c = (-1) ^ d := by
  choose A hA hlargeA using fun i => AffineNormEscape.exists_bound_norm_affine_gt
    (t i) (s i) (b i) (fun _ => (p i : ℝ) ^ stage) (hs i)
  choose V hV hlargeV using fun i => AffineNormEscape.exists_bound_norm_affine_gt
    (t i) (s i) (fun _ => 0) (fun j => ‖b i j‖) (hs i)
  obtain ⟨N, hmult, hbudget, hclear, hlarge, hmodel⟩ := exists_constant_exponents
    p hinj ell hfresh d stage hstage h (fun i => max (B i) (max (A i) (V i)))
  refine ⟨N, hmult, hbudget, hclear, ?_, ?_, hmodel⟩
  · intro i
    exact (le_max_left _ _).trans_lt (hlarge i)
  · intro i j hj
    have hAc : A i < ‖(constant p N d : ℚ_[p i])‖ :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (hlarge i)
    have hVc : V i < ‖(constant p N d : ℚ_[p i])‖ :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (hlarge i)
    refine ⟨?_, valuation_lt_neg_of_pow_lt_norm (p i) _ stage
      (hlargeA i _ hAc j hj)⟩
    simpa only [add_zero] using hlargeV i _ hVc j hj

/-- The clearing budget makes every previously cleared coefficient divisible
by the full stage precision after division by the signed constant, including zero. -/
theorem norm_div_constant_le_stage_precision {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (N : ι → ℕ) (d : ℕ) (i : ι) (h stage : ℕ) (hbudget : h + stage ≤ N i)
    (x : ℚ_[p i]) (hx : ‖x‖ ≤ (p i : ℝ) ^ h) :
    ‖x / (constant p N d : ℚ_[p i])‖ ≤ (p i : ℝ) ^ (-(stage : ℤ)) := by
  have hp1 : (1 : ℝ) < p i := by exact_mod_cast (show (p i).Prime from Fact.out).one_lt
  have hp0 := zero_lt_one.trans hp1
  rw [norm_div, norm_constant_at_processed p hinj N d i]
  apply (div_le_iff₀ (pow_pos hp0 (N i))).mpr
  apply hx.trans
  rw [← zpow_natCast (p i : ℝ) h, ← zpow_natCast (p i : ℝ) (N i),
    ← zpow_add₀ hp0.ne']
  exact zpow_le_zpow_right₀ hp1.le (by omega)

/-- Every coefficient of finitely many fixed local polynomials admits one
common prime-power denominator clearing. The polynomials are fixed before h. -/
theorem exists_polynomial_clearing_exponent {κ : Type*}
    (p : ℕ) [Fact p.Prime] (t : Finset κ) (F : κ → ℚ_[p][X]) :
    ∃ h : ℕ, ∀ j ∈ t, ∀ k : ℕ,
      ‖(F j).coeff k‖ ≤ (p : ℝ) ^ h ∧
      (p : ℚ_[p]) ^ h * (F j).coeff k ∈ PadicInt.subring p := by
  classical
  obtain ⟨B, _, hB⟩ := AffineNormEscape.finite_nonneg_upper_bound
    (t.sigma fun j => (F j).support) (fun jk => ‖(F jk.1).coeff jk.2‖)
  obtain ⟨h, _, _, hh⟩ := exists_large_multiple 1 p 0 (by decide)
    (show p.Prime from Fact.out).one_lt B
  simp only [one_mul] at hh
  refine ⟨h, ?_⟩
  intro j hj k
  have hcoeff : ‖(F j).coeff k‖ ≤ (p : ℝ) ^ h := by
    by_cases hk : k ∈ (F j).support
    · exact (hB ⟨j, k⟩ (Finset.mem_sigma.mpr ⟨hj, hk⟩)).trans hh.le
    · simp only [Polynomial.notMem_support_iff.mp hk, norm_zero]
      exact pow_nonneg (Nat.cast_nonneg p) _
  refine ⟨hcoeff, ?_⟩
  change ‖(p : ℚ_[p]) ^ h * (F j).coeff k‖ ≤ 1
  rw [norm_mul, norm_pow, Padic.norm_p]
  calc
    (p : ℝ)⁻¹ ^ h * ‖(F j).coeff k‖ ≤ (p : ℝ)⁻¹ ^ h * (p : ℝ) ^ h :=
      mul_le_mul_of_nonneg_left hcoeff (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) _)
    _ = 1 := by
      rw [inv_pow, inv_mul_cancel₀]
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (show p.Prime from Fact.out).ne_zero)

end UnconditionalCounterexample.SignedConstant
