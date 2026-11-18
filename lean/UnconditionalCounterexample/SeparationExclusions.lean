import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Derivative
import UnconditionalCounterexample.PolynomialAvoidance

/-!
# Proper geometric exclusions on a two-coefficient grid

Fix all but the linear and quadratic coefficients. Interpolation in the family G + uX
+ vX² gives nonzero exclusion polynomials for retained points, separation of pairs and
nonvanishing tangents. A prescribed nonzero constant coefficient handles the point
zero. The tangent argument uses characteristic zero.

Finite valid tests can therefore be avoided on any already-fixed pair of rational
arithmetic progressions, even when their points lie in an extension field. These
progressions describe coefficient increments; subtract the baseline linear and
quadratic coefficients from desired offsets when necessary. Higher coefficients,
the constant, and (for degree greater than two) degree and monicity are unchanged.
This proves properness of the actual exclusions, without assuming it as an input.
-/

noncomputable section

namespace UnconditionalCounterexample.SeparationExclusions

open scoped Polynomial

variable {K : Type*} [Field K]

/-- The two free coefficient increments, indexed by Bool. -/
def coefficientPair (u v : K) : Bool → K := fun b => if b then v else u

/-- The actual polynomial obtained by varying only its linear and quadratic coefficients. -/
def family (G : K[X]) (u v : K) : K[X] :=
  G + Polynomial.C u * Polynomial.X + Polynomial.C v * Polynomial.X ^ 2

/-- Evaluation of the family as a polynomial in its two free coefficients. -/
def value (G : K[X]) (a : K) : MvPolynomial Bool K :=
  MvPolynomial.C (G.eval a) + MvPolynomial.C a * MvPolynomial.X false +
    MvPolynomial.C (a ^ 2) * MvPolynomial.X true

/-- The cross-multiplied equation forbidding separation by the word F^m/H. -/
def pairExclusion (G H : K[X]) (a b : K) (m : ℕ) : MvPolynomial Bool K :=
  value G a ^ m * MvPolynomial.C (H.eval b) -
    value G b ^ m * MvPolynomial.C (H.eval a)

/-- The coefficient-polynomial evaluation has the expected affine expression. -/
@[simp]
theorem eval_value (G : K[X]) (a u v : K) :
    MvPolynomial.eval (coefficientPair u v) (value G a) = G.eval a + a * u + a ^ 2 * v := by
  simp [value, coefficientPair]

/-- The coefficient-polynomial value is evaluation of the actual family member. -/
theorem eval_value_eq_eval_family (G : K[X]) (a u v : K) :
    MvPolynomial.eval (coefficientPair u v) (value G a) = (family G u v).eval a := by
  rw [eval_value]
  simp only [family, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- At a nonzero point the linear coefficient can prescribe any value. -/
theorem exists_eval_value (G : K[X]) (a : K) (ha : a ≠ 0) (r : K) :
    ∃ u v : K, MvPolynomial.eval (coefficientPair u v) (value G a) = r := by
  refine ⟨(r - G.eval a) / a, 0, ?_⟩
  rw [eval_value]
  field_simp
  ring

/-- Two coefficients prescribe arbitrary values at distinct nonzero points. -/
theorem exists_eval_value_pair (G : K[X]) (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (r s : K) :
    ∃ u v : K, MvPolynomial.eval (coefficientPair u v) (value G a) = r ∧
      MvPolynomial.eval (coefficientPair u v) (value G b) = s := by
  let d : K := a * b ^ 2 - b * a ^ 2
  have hd : d ≠ 0 := by
    have heq : d = a * b * (b - a) := by dsimp [d]; ring
    rw [heq]
    exact mul_ne_zero (mul_ne_zero ha hb) (sub_ne_zero.mpr hab.symm)
  refine ⟨((r - G.eval a) * b ^ 2 - (s - G.eval b) * a ^ 2) / d,
    (a * (s - G.eval b) - b * (r - G.eval a)) / d, ?_, ?_⟩
  · rw [eval_value]
    field_simp
    dsimp [d]
    ring
  · rw [eval_value]
    field_simp
    dsimp [d]
    ring

/-- Retaining a point imposes a proper exclusion, including the point zero. -/
theorem value_ne_zero (G : K[X]) (hG : G.coeff 0 ≠ 0) (a : K) : value G a ≠ 0 := by
  by_cases ha : a = 0
  · subst a
    simpa [value, ← Polynomial.coeff_zero_eq_eval_zero] using hG
  · obtain ⟨u, v, huv⟩ := exists_eval_value G a ha 1
    intro h
    rw [h, map_zero] at huv
    exact zero_ne_one huv

/-- Distinct retained points give a proper word-separation exclusion. -/
theorem pairExclusion_ne_zero (G H : K[X]) (hG : G.coeff 0 ≠ 0)
    (a b : K) (hab : a ≠ b) (m : ℕ) (hm : 0 < m)
    (haH : H.eval a ≠ 0) (hbH : H.eval b ≠ 0) : pairExclusion G H a b m ≠ 0 := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := Ne.symm hab
    obtain ⟨u, v, hv⟩ := exists_eval_value G b hb 0
    intro he
    have h := congrArg (MvPolynomial.eval (coefficientPair u v)) he
    simp only [pairExclusion, map_sub, map_mul, map_pow, MvPolynomial.eval_C,
      eval_value, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero,
      ← Polynomial.coeff_zero_eq_eval_zero] at h
    have hv' : G.eval b + b * u + b ^ 2 * v = 0 := by simpa only [eval_value] using hv
    rw [hv', zero_pow hm0, zero_mul, sub_zero,
      (MvPolynomial.eval (coefficientPair u v)).map_zero] at h
    exact mul_ne_zero (pow_ne_zero m hG) hbH h
  · by_cases hb : b = 0
    · subst b
      obtain ⟨u, v, hu⟩ := exists_eval_value G a ha 0
      intro he
      have h := congrArg (MvPolynomial.eval (coefficientPair u v)) he
      simp only [pairExclusion, map_sub, map_mul, map_pow, MvPolynomial.eval_C,
        eval_value, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero,
        ← Polynomial.coeff_zero_eq_eval_zero] at h
      have hu' : G.eval a + a * u + a ^ 2 * v = 0 := by simpa only [eval_value] using hu
      rw [hu', zero_pow hm0, zero_mul, zero_sub,
        (MvPolynomial.eval (coefficientPair u v)).map_zero, neg_eq_zero] at h
      exact mul_ne_zero (pow_ne_zero m hG) haH h
    · obtain ⟨u, v, hu, hv⟩ := exists_eval_value_pair G a b ha hb hab 1 0
      intro he
      have h := congrArg (MvPolynomial.eval (coefficientPair u v)) he
      exact hbH (by
        simpa only [pairExclusion, map_sub, map_mul, map_pow, MvPolynomial.eval_C,
          hu, hv, one_pow, one_mul, zero_pow hm0, zero_mul, sub_zero, map_zero] using h)


/-- The fixed constant coefficient is preserved. -/
@[simp]
theorem family_coeff_zero (G : K[X]) (u v : K) : (family G u v).coeff 0 = G.coeff 0 := by
  simp [family]

/-- The first parameter is exactly the increment of the linear coefficient. -/
@[simp] theorem family_coeff_one (G : K[X]) (u v : K) :
    (family G u v).coeff 1 = G.coeff 1 + u := by
  simp [family]

/-- The second parameter is exactly the increment of the quadratic coefficient. -/
@[simp] theorem family_coeff_two (G : K[X]) (u v : K) :
    (family G u v).coeff 2 = G.coeff 2 + v := by
  simp [family]

/-- Every higher coefficient is preserved. -/
theorem family_coeff_of_two_lt (G : K[X]) (u v : K) (n : ℕ) (hn : 2 < n) :
    (family G u v).coeff n = G.coeff n := by
  have hn1 : n ≠ 1 := Nat.ne_of_gt (lt_trans (by decide : 1 < 2) hn)
  have hn2 : n ≠ 2 := Nat.ne_of_gt hn
  simp [family, Polynomial.coeff_X, Polynomial.coeff_X_pow, Ne.symm hn1, hn2]

/-- The varying part has degree at most two. -/
theorem perturbation_natDegree_le (u v : K) :
    (Polynomial.C u * Polynomial.X + Polynomial.C v * Polynomial.X ^ 2).natDegree ≤ 2 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_C_mul_le u Polynomial.X).trans
      (Polynomial.natDegree_X_le.trans (by decide))
  · exact Polynomial.natDegree_C_mul_X_pow_le v 2

/-- A baseline of degree greater than two retains its degree. -/
theorem family_natDegree (G : K[X]) (hG : 2 < G.natDegree) (u v : K) :
    (family G u v).natDegree = G.natDegree := by
  unfold family
  rw [add_assoc]
  exact Polynomial.natDegree_add_eq_left_of_natDegree_lt
    ((perturbation_natDegree_le u v).trans_lt hG)

/-- A monic baseline of degree greater than two remains monic. -/
theorem family_monic (G : K[X]) (hG : G.Monic) (hdeg : 2 < G.natDegree) (u v : K) :
    (family G u v).Monic := by
  unfold family
  rw [add_assoc]
  exact hG.add_of_left (Polynomial.degree_lt_degree
    ((perturbation_natDegree_le u v).trans_lt hdeg))


/-- The derivative of the family evaluated at a point, as a coefficient polynomial. -/
def derivativeValue (G : K[X]) (a : K) : MvPolynomial Bool K :=
  MvPolynomial.C (G.derivative.eval a) + MvPolynomial.X false +
    MvPolynomial.C (2 * a) * MvPolynomial.X true

/-- The coefficient-polynomial derivative has the expected affine expression. -/
@[simp] theorem eval_derivativeValue (G : K[X]) (a u v : K) :
    MvPolynomial.eval (coefficientPair u v) (derivativeValue G a) =
      G.derivative.eval a + u + (2 * a) * v := by
  simp [derivativeValue, coefficientPair]

/-- The derivative coefficient polynomial agrees with the actual formal derivative. -/
theorem eval_derivativeValue_eq_derivative_family (G : K[X]) (a u v : K) :
    MvPolynomial.eval (coefficientPair u v) (derivativeValue G a) =
      (family G u v).derivative.eval a := by
  simp only [eval_derivativeValue, family, Polynomial.derivative_add,
    Polynomial.derivative_C_mul, Polynomial.derivative_X,
    Polynomial.derivative_X_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

/-- At a nonzero point, the two coefficients prescribe value and first derivative. -/
theorem exists_value_derivative (G : K[X]) (a : K) (ha : a ≠ 0) (s t : K) :
    ∃ u v : K, MvPolynomial.eval (coefficientPair u v) (value G a) = s ∧
      MvPolynomial.eval (coefficientPair u v) (derivativeValue G a) = t := by
  refine ⟨2 * (s - G.eval a) / a - (t - G.derivative.eval a),
    (a * (t - G.derivative.eval a) - (s - G.eval a)) / a ^ 2, ?_, ?_⟩
  · rw [eval_value]
    field_simp
    ring
  · rw [eval_derivativeValue]
    field_simp
    ring

/-- The numerator of the formal derivative of the word F^m/H. -/
def tangentExclusion (G H : K[X]) (a : K) (m : ℕ) : MvPolynomial Bool K :=
  MvPolynomial.C (m : K) * value G a ^ (m - 1) * derivativeValue G a *
    MvPolynomial.C (H.eval a) - value G a ^ m * MvPolynomial.C (H.derivative.eval a)

/-- The pair exclusion evaluates to the actual cross-multiplied values. -/
theorem eval_pairExclusion_eq (G H : K[X]) (a b u v : K) (m : ℕ) :
    MvPolynomial.eval (coefficientPair u v) (pairExclusion G H a b m) =
      (family G u v).eval a ^ m * H.eval b -
        (family G u v).eval b ^ m * H.eval a := by
  simp only [pairExclusion, map_sub, map_mul, map_pow, MvPolynomial.eval_C,
    eval_value_eq_eval_family]

/-- The tangent exclusion evaluates to the actual quotient-rule numerator. -/
theorem eval_tangentExclusion_eq (G H : K[X]) (a u v : K) (m : ℕ) :
    MvPolynomial.eval (coefficientPair u v) (tangentExclusion G H a m) =
      (m : K) * (family G u v).eval a ^ (m - 1) *
        (family G u v).derivative.eval a * H.eval a -
          (family G u v).eval a ^ m * H.derivative.eval a := by
  simp only [tangentExclusion, map_sub, map_mul, map_pow, MvPolynomial.eval_C,
    eval_value_eq_eval_family, eval_derivativeValue_eq_derivative_family]

variable [CharZero K]

/-- Every valid tangent test has a proper bad locus, including the point zero. -/
theorem tangentExclusion_ne_zero (G H : K[X]) (hG : G.coeff 0 ≠ 0)
    (a : K) (hH : H.eval a ≠ 0) (m : ℕ) (hm : 0 < m) :
    tangentExclusion G H a m ≠ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  obtain ⟨u, v, s, hs, hv, hd⟩ : ∃ u v s : K, s ≠ 0 ∧
      MvPolynomial.eval (coefficientPair u v) (value G a) = s ∧
      MvPolynomial.eval (coefficientPair u v) (derivativeValue G a) =
        (s * H.derivative.eval a + 1) / (((n + 1 : ℕ) : K) * H.eval a) := by
    by_cases ha : a = 0
    · subst a
      refine ⟨(G.coeff 0 * H.derivative.eval 0 + 1) /
        (((n + 1 : ℕ) : K) * H.eval 0) - G.derivative.eval 0, 0, G.coeff 0, hG, ?_, ?_⟩
      · simpa using G.coeff_zero_eq_eval_zero.symm
      · simp
    · obtain ⟨u, v, hv, hd⟩ := exists_value_derivative G a ha 1
        ((H.derivative.eval a + 1) / (((n + 1 : ℕ) : K) * H.eval a))
      exact ⟨u, v, 1, one_ne_zero, hv, by simpa using hd⟩
  have he : MvPolynomial.eval (coefficientPair u v) (tangentExclusion G H a (n + 1)) = s ^ n := by
    simp only [tangentExclusion, map_sub, map_mul, map_pow, MvPolynomial.eval_C,
      Nat.add_sub_cancel, hv, hd, pow_succ]
    field_simp
    ring
  intro hz
  apply pow_ne_zero n hs
  rw [← he, hz, map_zero]



/-- A finite geometric test whose bad locus is an explicit coefficient polynomial. -/
inductive Test (K : Type*) [Field K] where
  | point (a : K)
  | pair (a b : K) (m : ℕ) (H : K[X])
  | tangent (a : K) (m : ℕ) (H : K[X])

/-- Exactly the geometric nondegeneracy conditions for the indicated test. -/
def Test.Valid : Test K → Prop
  | .point _ => True
  | .pair a b m H => a ≠ b ∧ 0 < m ∧ H.eval a ≠ 0 ∧ H.eval b ≠ 0
  | .tangent a m H => 0 < m ∧ H.eval a ≠ 0

/-- The forbidden equation as a polynomial in the two free coefficients. -/
def Test.exclusion (G : K[X]) : Test K → MvPolynomial Bool K
  | .point a => value G a
  | .pair a b m H => pairExclusion G H a b m
  | .tangent a m H => tangentExclusion G H a m

/-- The concrete point, pair, or tangent inequality for a polynomial family member. -/
def Test.Holds (F : K[X]) : Test K → Prop
  | .point a => F.eval a ≠ 0
  | .pair a b m H => F.eval a ^ m * H.eval b - F.eval b ^ m * H.eval a ≠ 0
  | .tangent a m H =>
    (m : K) * F.eval a ^ (m - 1) * F.derivative.eval a * H.eval a -
      F.eval a ^ m * H.derivative.eval a ≠ 0

omit [CharZero K] in
/-- The explicit bad polynomial expresses exactly the requested geometric inequality. -/
theorem Test.holds_family_iff (G : K[X]) (u v : K) (t : Test K) :
    t.Holds (family G u v) ↔
      MvPolynomial.eval (coefficientPair u v) (t.exclusion G) ≠ 0 := by
  cases t with
  | point a => simp only [Test.Holds, Test.exclusion, eval_value_eq_eval_family]
  | pair a b m H => simp only [Test.Holds, Test.exclusion, eval_pairExclusion_eq]
  | tangent a m H => simp only [Test.Holds, Test.exclusion, eval_tangentExclusion_eq]

/-- Every valid geometric test has a proper bad locus. -/
theorem Test.exclusion_ne_zero (G : K[X]) (hG : G.coeff 0 ≠ 0)
    (t : Test K) (ht : t.Valid) : t.exclusion G ≠ 0 := by
  cases t with
  | point a => exact value_ne_zero G hG a
  | pair a b m H =>
    obtain ⟨hab, hm, haH, hbH⟩ := ht
    exact pairExclusion_ne_zero G H hG a b hab m hm haH hbH
  | tangent a m H =>
    obtain ⟨hm, hH⟩ := ht
    exact tangentExclusion_ne_zero G H hG a hH m hm

/-- Finite geometric tests can all be met on already-fixed rational arithmetic
progressions for the linear and quadratic coefficient increments. -/
theorem exists_rational_grid_avoiding_tests (G : K[X]) (hG : G.coeff 0 ≠ 0)
    (offset step : Bool → ℚ) (hstep : ∀ i, step i ≠ 0) (N : Bool → ℕ)
    (I : Finset (Test K)) (hI : ∀ t ∈ I, t.Valid) :
    ∃ n : Bool → ℕ, ∀ t ∈ I,
      MvPolynomial.eval (fun i => algebraMap ℚ K
        (offset i + step i * ((N i + n i : ℕ) : ℚ))) (t.exclusion G) ≠ 0 := by
  exact UnconditionalCounterexample.PolynomialAvoidance.exists_rational_grid_avoiding
    offset step hstep N I (fun t => t.exclusion G)
      (fun t ht => t.exclusion_ne_zero G hG (hI t ht))


/-- A single member of the two-coefficient family meets all valid tests while
its coefficient increments stay on the fixed rational grid. -/
theorem exists_rational_grid_family (G : K[X]) (hG : G.coeff 0 ≠ 0)
    (offset step : Bool → ℚ) (hstep : ∀ i, step i ≠ 0) (N : Bool → ℕ)
    (I : Finset (Test K)) (hI : ∀ t ∈ I, t.Valid) :
    ∃ n : Bool → ℕ, ∀ t ∈ I, t.Holds (family G
      (algebraMap ℚ K (offset false + step false * ((N false + n false : ℕ) : ℚ)))
      (algebraMap ℚ K (offset true + step true * ((N true + n true : ℕ) : ℚ)))) := by
  obtain ⟨n, hn⟩ := exists_rational_grid_avoiding_tests G hG offset step hstep N I hI
  refine ⟨n, fun t ht => (t.holds_family_iff G _ _).mpr ?_⟩
  have heq : coefficientPair
      (algebraMap ℚ K (offset false + step false * ((N false + n false : ℕ) : ℚ)))
      (algebraMap ℚ K (offset true + step true * ((N true + n true : ℕ) : ℚ))) =
      (fun i => algebraMap ℚ K (offset i + step i * ((N i + n i : ℕ) : ℚ))) := by
    funext i
    cases i <;> rfl
  rw [heq]
  exact hn t ht

end UnconditionalCounterexample.SeparationExclusions
