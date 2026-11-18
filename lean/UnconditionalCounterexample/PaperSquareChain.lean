import UnconditionalCounterexample.PairedDomain
import UnconditionalCounterexample.PaperTargets
import UnconditionalCounterexample.PrincipalChain
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# The manuscript's square chain and its same-ratio independence

Given the constructor's pole-algebra units `q n` with primary orders `(2,1,2)`
and guard order zero, the literal endpoints `X² / ∏ j < n, q (2*j)` belong to
`PairedDomain.domain`. The even profiles have disjoint supports, so their
prefixes divide `X²` at every defining valuation. The odd coordinate of each
ratio proves that it is a nonunit in the intersection.

A guard and primary over the same rational prime agree on rational constants.
Comparing them at coordinate `4*j+1` proves independence of these same ratios
modulo `ℚˣ`. The constructor hypotheses remain explicit; this module does not
assert the existence of their input data.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperSquareChain
open Polynomial WithZero UnconditionalCounterexample
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Primary order of the constructor ratio `q_n`. -/
def qProfile (n i : ℕ) : ℤ :=
  if i = 2 * n then 2 else if i = 2 * n + 1 then 1 else if i = 2 * n + 2 then 2 else 0

theorem qProfile_nonneg (n i : ℕ) : 0 ≤ qProfile n i := by
  unfold qProfile
  split_ifs <;> omega

theorem qProfile_le_two (n i : ℕ) : qProfile n i ≤ 2 := by
  unfold qProfile
  split_ifs <;> omega

theorem qProfile_ne_zero_bounds {n i : ℕ} (h : qProfile n i ≠ 0) :
    2 * n ≤ i ∧ i ≤ 2 * n + 2 := by
  unfold qProfile at h
  split_ifs at h <;> omega

theorem qProfile_even_unique {j k i : ℕ}
    (hj : qProfile (2 * j) i ≠ 0) (hk : qProfile (2 * k) i ≠ 0) : j = k := by
  have h1 := qProfile_ne_zero_bounds hj
  have h2 := qProfile_ne_zero_bounds hk
  omega

theorem sum_qProfile_even_le_two (s : Finset ℕ) (i : ℕ) :
    (∑ j ∈ s, qProfile (2 * j) i) ≤ 2 := by
  classical
  by_cases h : ∃ j ∈ s, qProfile (2 * j) i ≠ 0
  · obtain ⟨j, hj, hjv⟩ := h
    rw [Finset.sum_eq_single j]
    · exact qProfile_le_two _ _
    · intro k hk hkj
      by_contra hkv
      exact hkj (qProfile_even_unique hkv hjv)
    · exact fun hnot => (hnot hj).elim
  · have hzero : ∀ j ∈ s, qProfile (2 * j) i = 0 := by
      intro j hj
      by_contra hne
      exact h ⟨j, hj, hne⟩
    simp [Finset.sum_eq_zero hzero]

variable {S : Set ℚ[X]} (d : PairedDomain.Places)
  (q : ℕ → PoleAlgebra.generated S)
  (hunit : ∀ n, IsUnit (q n))
  (hp : ∀ n i, PairedDomain.vertical d (.inl i) (q n : RatFunc ℚ) = exp (-qProfile n i))
  (hg : ∀ n p, PairedDomain.vertical d (.inr p) (q n : RatFunc ℚ) = 1)

/-- The actual finite product of even-indexed constructor ratios. -/
def evenPrefix (n : ℕ) : RatFunc ℚ := ∏ j ∈ Finset.range n, (q (2 * j) : RatFunc ℚ)

/-- The manuscript endpoint, as a literal rational function. -/
def chainValue (n : ℕ) : RatFunc ℚ := RatFunc.X ^ 2 / evenPrefix q n

include hunit

theorem q_ne_zero (n : ℕ) : (q n : RatFunc ℚ) ≠ 0 :=
  fun h => (hunit n).ne_zero (Subtype.ext h)

theorem q_inv_mem (n : ℕ) : (q n : RatFunc ℚ)⁻¹ ∈ PoleAlgebra.generated S := by
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp (hunit n)
  have hmul : (q n : RatFunc ℚ) * (y : RatFunc ℚ) = 1 :=
    congrArg (fun z : PoleAlgebra.generated S => (z : RatFunc ℚ)) hy
  have heq : (y : RatFunc ℚ) = (q n : RatFunc ℚ)⁻¹ := by
    calc
      (y : RatFunc ℚ) = 1 * (y : RatFunc ℚ) := by simp
      _ = ((q n : RatFunc ℚ)⁻¹ * (q n : RatFunc ℚ)) * (y : RatFunc ℚ) := by
        rw [inv_mul_cancel₀ (q_ne_zero q hunit n)]
      _ = (q n : RatFunc ℚ)⁻¹ * ((q n : RatFunc ℚ) * (y : RatFunc ℚ)) := by ring
      _ = (q n : RatFunc ℚ)⁻¹ := by rw [hmul, mul_one]
  rw [← heq]
  exact y.property

theorem prefix_ne_zero (n : ℕ) : evenPrefix q n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => q_ne_zero q hunit (2 * j))

theorem prefix_inv_mem (n : ℕ) : (evenPrefix q n)⁻¹ ∈ PoleAlgebra.generated S := by
  induction n with
  | zero => simp [evenPrefix]
  | succ n ih =>
    simp only [evenPrefix, Finset.prod_range_succ, mul_inv_rev]
    exact (PoleAlgebra.generated S).mul_mem (q_inv_mem q hunit (2 * n)) ih

theorem chainValue_mem_pole (n : ℕ) : chainValue q n ∈ PoleAlgebra.generated S := by
  simpa only [chainValue, div_eq_mul_inv] using
    (PoleAlgebra.generated S).mul_mem ((PoleAlgebra.generated S).pow_mem (PoleAlgebra.X_mem S) 2)
      (prefix_inv_mem q hunit n)

omit hunit
include hp

theorem primary_prefix (n i : ℕ) : PairedDomain.vertical d (.inl i) (evenPrefix q n) =
    exp (-(∑ j ∈ Finset.range n, qProfile (2 * j) i)) := by
  induction n with
  | zero => simp [evenPrefix]
  | succ n ih =>
    simp only [evenPrefix, Finset.prod_range_succ, map_mul] at ih ⊢
    rw [ih, hp, Finset.sum_range_succ, neg_add, exp_add]

omit hp
include hg

theorem guard_prefix (n : ℕ) (p : GuardSupport.PrimeIndex) :
    PairedDomain.vertical d (.inr p) (evenPrefix q n) = 1 := by
  simp only [evenPrefix, map_prod, hg, Finset.prod_const_one]

omit hg

theorem primary_X_le (hfirst : (d.primary 0).val.valuation = 2) (i : ℕ) :
    PairedDomain.vertical d (.inl i) RatFunc.X ≤ exp (-1) := by
  change EvaluationDVR.evaluationValuation _ _ _ RatFunc.X ≤ _
  rw [EvaluationDVR.evaluationValuation_X]
  have hz := (d.primary_trans i).ne_zero
  rw [Padic.mulValuation_toFun, ite_eq_right hz]
  cases i with
  | zero => rw [hfirst]; simp
  | succ i => rw [d.primary_late (i + 1) (by omega)]

include hunit hp hg

/-- The literal square endpoint satisfies every defining valuation. -/
theorem chainValue_mem (hfirst : (d.primary 0).val.valuation = 2) (n : ℕ) :
    chainValue q n ∈ PairedDomain.domain S d := by
  apply (IntersectionDomain.div_mem_iff _ _ (prefix_ne_zero q hunit n)).mpr
  refine ⟨chainValue_mem_pole q hunit n, ?_⟩
  rintro (i | p)
  · have hX : PairedDomain.vertical d (.inl i) (RatFunc.X ^ 2) ≤ exp (-2) := by
      rw [map_pow]
      calc
        PairedDomain.vertical d (.inl i) RatFunc.X ^ 2 ≤ exp (-1 : ℤ) ^ 2 :=
          pow_le_pow_left₀ zero_le (primary_X_le d hfirst i) 2
        _ = exp (-2 : ℤ) := by norm_num [← exp_nsmul, nsmul_eq_mul]
    rw [primary_prefix d q hp]
    exact hX.trans (WithZero.exp_le_exp.mpr (by have h := sum_qProfile_even_le_two (Finset.range n) i; omega))
  · rw [guard_prefix d q hg]
    exact ((IntersectionDomain.mem_intersection _ _ _).mp
      ((PairedDomain.domain S d).pow_mem (PairedDomain.X_mem S d) 2)).2 (.inr p)

omit hunit hp hg
include hp hg

theorem q_mem_domain (n : ℕ) : (q n : RatFunc ℚ) ∈ PairedDomain.domain S d := by
  apply (IntersectionDomain.mem_intersection _ _ _).mpr
  refine ⟨(q n).property, ?_⟩
  rintro (i | p)
  · rw [hp]
    rw [← exp_zero]
    exact exp_le_exp.mpr (neg_nonpos.mpr (qProfile_nonneg n i))
  · rw [hg]

/-- The supplied constructor ratio, now as an element of the actual intersection. -/
def domainRatio (n : ℕ) : PairedDomain.domain S d :=
  ⟨q n, q_mem_domain d q hp hg n⟩

omit hg
include hp

/-- The odd primary coordinate proves every supplied ratio is a nonunit. -/
theorem q_not_isUnit {n : ℕ} (hq : (q n : RatFunc ℚ) ∈ PairedDomain.domain S d) :
    ¬ IsUnit (⟨q n, hq⟩ : PairedDomain.domain S d) := by
  intro hu
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
  have hm : (q n : RatFunc ℚ) * (y : RatFunc ℚ) = 1 :=
    congrArg (fun z : PairedDomain.domain S d => (z : RatFunc ℚ)) hy
  have hvy := ((IntersectionDomain.mem_intersection _ _ _).mp y.property).2
    (.inl (2 * n + 1))
  have hvq : PairedDomain.vertical d (.inl (2 * n + 1)) (q n : RatFunc ℚ) < 1 := by
    rw [hp]
    have hprof : qProfile n (2 * n + 1) = 1 := by simp [qProfile]
    rw [hprof]
    rw [← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  have hvprod := congrArg (PairedDomain.vertical d (.inl (2 * n + 1))) hm
  rw [map_mul, map_one] at hvprod
  have hlt : PairedDomain.vertical d (.inl (2 * n + 1)) (q n : RatFunc ℚ) *
      PairedDomain.vertical d (.inl (2 * n + 1)) (y : RatFunc ℚ) < 1 := by
    calc
      _ ≤ PairedDomain.vertical d (.inl (2 * n + 1)) (q n : RatFunc ℚ) * 1 :=
        mul_le_mul_of_nonneg_left hvy zero_le
      _ < 1 := by simpa only [mul_one] using hvq
  rw [hvprod] at hlt
  exact (lt_irrefl _ hlt)

omit hp
include hunit

theorem chainValue_ne_zero (n : ℕ) : chainValue q n ≠ 0 := by
  exact div_ne_zero (pow_ne_zero 2 RatFunc.X_ne_zero) (prefix_ne_zero q hunit n)

theorem chainValue_recurrence (n : ℕ) :
    chainValue q n = (q (2 * n) : RatFunc ℚ) * chainValue q (n + 1) := by
  simp only [chainValue, evenPrefix, Finset.prod_range_succ]
  field_simp [prefix_ne_zero q hunit n, q_ne_zero q hunit (2 * n)]

include hp hg

/-- The explicit square-chain endpoint in the actual intersection. -/
def endpoint (hfirst : (d.primary 0).val.valuation = 2) (n : ℕ) :
    PairedDomain.domain S d := ⟨chainValue q n, chainValue_mem d q hunit hp hg hfirst n⟩

omit hunit hp hg

theorem qProfile_even_odd (j k : ℕ) :
    qProfile (2 * j) (4 * k + 1) = if j = k then 1 else 0 := by
  have h₀ : 4 * k + 1 ≠ 2 * (2 * j) := by omega
  have h₂ : 4 * k + 1 ≠ 2 * (2 * j) + 2 := by omega
  have h₁ : 4 * k + 1 = 2 * (2 * j) + 1 ↔ j = k := by omega
  simp only [qProfile, ite_eq_right h₀, ite_eq_right h₂, h₁]

theorem q_ne_zero_from_profile (d : PairedDomain.Places) (q : ℕ → RatFunc ℚ)
    (hp : ∀ n i, PairedDomain.vertical d (.inl i) (q n) = exp (-qProfile n i))
    (n : ℕ) : q n ≠ 0 := by
  intro hz
  have h := hp n 0
  rw [hz, map_zero] at h
  exact exp_ne_zero h.symm

/-- Primary and guard evaluations over the same prime agree on rational constants. -/
theorem vertical_C_primary_eq_guard (d : PairedDomain.Places) (i : ℕ) (c : ℚ) :
    PairedDomain.vertical d (.inl i) (RatFunc.C c) =
      PairedDomain.vertical d (.inr (d.primes i)) (RatFunc.C c) := by
  have hC : RatFunc.C c = (c : RatFunc ℚ) := by
    exact map_ratCast RatFunc.C c
  rw [hC]
  change Padic.mulValuation
      (EvaluationDVR.evaluationHom (d.primes i).val (d.primary i).val
        (d.primary_trans i) (c : RatFunc ℚ)) =
    Padic.mulValuation
      (GuardSupport.guardEvaluation d.guard d.guard_trans (d.primes i) (c : RatFunc ℚ))
  simp only [map_ratCast]

theorem guard_prod_eq_one (d : PairedDomain.Places) (q : ℕ → RatFunc ℚ)
    (hg : ∀ n p, PairedDomain.vertical d (.inr p) (q n) = 1)
    (e : ℕ →₀ ℤ) (p : GuardSupport.PrimeIndex) :
    PairedDomain.vertical d (.inr p) (e.prod fun j m => (q (2 * j)) ^ m) = 1 := by
  simp [map_finsuppProd, map_zpow₀, hg]

theorem primary_prod_eq_exp_neg (d : PairedDomain.Places) (q : ℕ → RatFunc ℚ)
    (hp : ∀ n i, PairedDomain.vertical d (.inl i) (q n) = exp (-qProfile n i))
    (e : ℕ →₀ ℤ) (k : ℕ) :
    PairedDomain.vertical d (.inl (4 * k + 1)) (e.prod fun j m => (q (2 * j)) ^ m) =
      exp (-(e k)) := by
  rw [map_finsuppProd]
  rw [Finsupp.prod_eq_single k]
  · rw [map_zpow₀, hp, qProfile_even_odd, ite_eq_left rfl]
    simp
  · intro j _hj hjk
    simp only [map_zpow₀, hp, qProfile_even_odd, ite_eq_right hjk, neg_zero, exp_zero, one_zpow]
  · intro _hk
    simp

theorem even_ratios_independent (d : PairedDomain.Places) (q : ℕ → RatFunc ℚ)
    (hp : ∀ n i, PairedDomain.vertical d (.inl i) (q n) = exp (-qProfile n i))
    (hg : ∀ n p, PairedDomain.vertical d (.inr p) (q n) = 1)
    (e : ℕ →₀ ℤ) (c : ℚ) (_hc : c ≠ 0)
    (hrel : e.prod (fun j m => (q (2 * j)) ^ m) = RatFunc.C c) : e = 0 := by
  ext k
  have hgC : PairedDomain.vertical d (.inr (d.primes (4 * k + 1))) (RatFunc.C c) = 1 := by
    rw [← hrel]
    exact guard_prod_eq_one d q hg e _
  have hpC : PairedDomain.vertical d (.inl (4 * k + 1)) (RatFunc.C c) = 1 := by
    rw [vertical_C_primary_eq_guard]
    exact hgC
  have h := primary_prod_eq_exp_neg d q hp e k
  rw [hrel, hpC] at h
  have he : -(e k) = 0 := exp_eq_one.mp h.symm
  simpa using he

/-- The actual even ratios are independent modulo rational constants. -/
theorem evenRatiosIndependentModuloRationals
    (D : Subring (RatFunc ℚ)) (d : PairedDomain.Places) (q : ℕ → D)
    (hp : ∀ n i, PairedDomain.vertical d (.inl i) (q n) = exp (-qProfile n i))
    (hg : ∀ n p, PairedDomain.vertical d (.inr p) (q n) = 1) :
    PaperTargets.EvenRatiosIndependentModuloRationals D q := by
  constructor
  · intro j hz
    apply q_ne_zero_from_profile d (fun n => (q n : RatFunc ℚ)) hp (2 * j)
    exact congrArg (fun z : D => (z : RatFunc ℚ)) hz
  · intro e c hc hrel
    exact even_ratios_independent d (fun n => (q n : RatFunc ℚ)) hp hg e c hc hrel


include hunit hp hg

/-- The full manuscript square-chain conclusion, with the supplied ratios. -/
theorem squareChainConclusion (hfirst : (d.primary 0).val.valuation = 2) :
    PaperTargets.SquareChainConclusion (PairedDomain.domain S d)
      ⟨RatFunc.X, PairedDomain.X_mem S d⟩ := by
  let qD := domainRatio d q hp hg
  let xD := endpoint d q hunit hp hg hfirst
  have hqD : ∀ n, qD n ≠ 0 ∧ ¬ IsUnit (qD n) := by
    intro n
    constructor
    · intro hn
      exact q_ne_zero q hunit n (congrArg (fun z : PairedDomain.domain S d =>
        (z : RatFunc ℚ)) hn)
    · exact q_not_isUnit d q hp _
  have hxD : ∀ n, xD n ≠ 0 := by
    intro n hn
    exact chainValue_ne_zero q hunit n (congrArg (fun z : PairedDomain.domain S d =>
      (z : RatFunc ℚ)) hn)
  have hrec : ∀ n, xD n = qD (2 * n) * xD (n + 1) := by
    intro n
    exact Subtype.ext (chainValue_recurrence q hunit n)
  refine ⟨qD, xD, hqD, hxD, ?_, ?_, hrec, ?_, ?_⟩
  · apply Subtype.ext
    simp [xD, endpoint, chainValue, evenPrefix]
  · intro n
    rfl
  · apply strictMono_principalIdeals_of_nonunit_recurrence xD (fun n => qD (2 * n)) hxD
      (fun n => (hqD (2 * n)).2)
    intro n
    rw [hrec n, mul_comm]
  · exact evenRatiosIndependentModuloRationals _ d qD hp hg

/-- The same explicit square chain proves failure of ACCP. -/
theorem not_wfDvdMonoid (hfirst : (d.primary 0).val.valuation = 2) :
    ¬ WfDvdMonoid (PairedDomain.domain S d) := by
  obtain ⟨r, x, hr, hx, _, _, hrec, _⟩ := squareChainConclusion d q hunit hp hg hfirst
  exact not_wfDvdMonoid_of_nonunit_recurrence x (fun n => r (2 * n)) hx
    (fun n => (hr (2 * n)).2) (fun n => by rw [hrec n, mul_comm])

end UnconditionalCounterexample.PaperSquareChain
