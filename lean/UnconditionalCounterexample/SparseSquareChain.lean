import UnconditionalCounterexample.PaperSquareChain
import UnconditionalCounterexample.SparsePrimaryDomain

/-!
# Square chain for sparse primary intersections

The explicit endpoints and even ratio profiles from PaperSquareChain
work for any injective primary enumeration, retaining every guard. The proof
of independence compares a primary with its guard over the same rational prime;
it never needs a primary over every prime. Constructor columns remain explicit.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseSquareChain
open Polynomial WithZero PaperSquareChain
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable {S : Set ℚ[X]} (d : SparsePrimaryDomain.Places)
  (q : ℕ → PoleAlgebra.generated S)
  (hunit : ∀ n, IsUnit (q n))
  (hp : ∀ n i, SparsePrimaryDomain.vertical d (.inl i) (q n : RatFunc ℚ) = exp (-qProfile n i))
  (hg : ∀ n p, SparsePrimaryDomain.vertical d (.inr p) (q n : RatFunc ℚ) = 1)

include hp

theorem primary_prefix (n i : ℕ) : SparsePrimaryDomain.vertical d (.inl i) (evenPrefix q n) =
    exp (-(∑ j ∈ Finset.range n, qProfile (2 * j) i)) := by
  induction n with
  | zero => simp [evenPrefix]
  | succ n ih =>
    simp only [evenPrefix, Finset.prod_range_succ, map_mul] at ih ⊢
    rw [ih, hp, Finset.sum_range_succ, neg_add, exp_add]

omit hp
include hg

theorem guard_prefix (n : ℕ) (p : GuardSupport.PrimeIndex) :
    SparsePrimaryDomain.vertical d (.inr p) (evenPrefix q n) = 1 := by
  simp only [evenPrefix, map_prod, hg, Finset.prod_const_one]

omit hg

theorem primary_X_le (hfirst : (d.primary 0).val.valuation = 2) (i : ℕ) :
    SparsePrimaryDomain.vertical d (.inl i) RatFunc.X ≤ exp (-1) := by
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
    chainValue q n ∈ SparsePrimaryDomain.domain S d := by
  apply (IntersectionDomain.div_mem_iff _ _ (prefix_ne_zero q hunit n)).mpr
  refine ⟨chainValue_mem_pole q hunit n, ?_⟩
  rintro (i | p)
  · have hX : SparsePrimaryDomain.vertical d (.inl i) (RatFunc.X ^ 2) ≤ exp (-2) := by
      rw [map_pow]
      calc
        SparsePrimaryDomain.vertical d (.inl i) RatFunc.X ^ 2 ≤ exp (-1 : ℤ) ^ 2 :=
          pow_le_pow_left₀ zero_le (primary_X_le d hfirst i) 2
        _ = exp (-2 : ℤ) := by norm_num [← exp_nsmul, nsmul_eq_mul]
    rw [primary_prefix d q hp]
    exact hX.trans (WithZero.exp_le_exp.mpr (by have h := sum_qProfile_even_le_two (Finset.range n) i; omega))
  · rw [guard_prefix d q hg]
    exact ((IntersectionDomain.mem_intersection _ _ _).mp
      ((SparsePrimaryDomain.domain S d).pow_mem (SparsePrimaryDomain.X_mem S d) 2)).2 (.inr p)

omit hunit hp hg
include hp hg

theorem q_mem_domain (n : ℕ) : (q n : RatFunc ℚ) ∈ SparsePrimaryDomain.domain S d := by
  apply (IntersectionDomain.mem_intersection _ _ _).mpr
  refine ⟨(q n).property, ?_⟩
  rintro (i | p)
  · rw [hp]
    rw [← exp_zero]
    exact exp_le_exp.mpr (neg_nonpos.mpr (qProfile_nonneg n i))
  · rw [hg]

/-- The supplied constructor ratio, now as an element of the actual intersection. -/
def domainRatio (n : ℕ) : SparsePrimaryDomain.domain S d :=
  ⟨q n, q_mem_domain d q hp hg n⟩

omit hg
include hp

/-- The odd primary coordinate proves every supplied ratio is a nonunit. -/
theorem q_not_isUnit {n : ℕ} (hq : (q n : RatFunc ℚ) ∈ SparsePrimaryDomain.domain S d) :
    ¬ IsUnit (⟨q n, hq⟩ : SparsePrimaryDomain.domain S d) := by
  intro hu
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
  have hm : (q n : RatFunc ℚ) * (y : RatFunc ℚ) = 1 :=
    congrArg (fun z : SparsePrimaryDomain.domain S d => (z : RatFunc ℚ)) hy
  have hvy := ((IntersectionDomain.mem_intersection _ _ _).mp y.property).2
    (.inl (2 * n + 1))
  have hvq : SparsePrimaryDomain.vertical d (.inl (2 * n + 1)) (q n : RatFunc ℚ) < 1 := by
    rw [hp]
    have hprof : qProfile n (2 * n + 1) = 1 := by simp [qProfile]
    rw [hprof]
    rw [← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  have hvprod := congrArg (SparsePrimaryDomain.vertical d (.inl (2 * n + 1))) hm
  rw [map_mul, map_one] at hvprod
  have hlt : SparsePrimaryDomain.vertical d (.inl (2 * n + 1)) (q n : RatFunc ℚ) *
      SparsePrimaryDomain.vertical d (.inl (2 * n + 1)) (y : RatFunc ℚ) < 1 := by
    calc
      _ ≤ SparsePrimaryDomain.vertical d (.inl (2 * n + 1)) (q n : RatFunc ℚ) * 1 :=
        mul_le_mul_of_nonneg_left hvy zero_le
      _ < 1 := by simpa only [mul_one] using hvq
  rw [hvprod] at hlt
  exact (lt_irrefl _ hlt)

omit hp
include hunit

include hp hg

/-- The explicit square-chain endpoint in the actual intersection. -/
def endpoint (hfirst : (d.primary 0).val.valuation = 2) (n : ℕ) :
    SparsePrimaryDomain.domain S d := ⟨chainValue q n, chainValue_mem d q hunit hp hg hfirst n⟩

omit hunit hp hg

theorem q_ne_zero_from_profile (d : SparsePrimaryDomain.Places) (q : ℕ → RatFunc ℚ)
    (hp : ∀ n i, SparsePrimaryDomain.vertical d (.inl i) (q n) = exp (-qProfile n i))
    (n : ℕ) : q n ≠ 0 := by
  intro hz
  have h := hp n 0
  rw [hz, map_zero] at h
  exact exp_ne_zero h.symm

/-- Primary and guard evaluations over the same prime agree on rational constants. -/
theorem vertical_C_primary_eq_guard (d : SparsePrimaryDomain.Places) (i : ℕ) (c : ℚ) :
    SparsePrimaryDomain.vertical d (.inl i) (RatFunc.C c) =
      SparsePrimaryDomain.vertical d (.inr (d.primes i)) (RatFunc.C c) := by
  have hC : RatFunc.C c = (c : RatFunc ℚ) := by
    exact map_ratCast RatFunc.C c
  rw [hC]
  change Padic.mulValuation
      (EvaluationDVR.evaluationHom (d.primes i).val (d.primary i).val
        (d.primary_trans i) (c : RatFunc ℚ)) =
    Padic.mulValuation
      (GuardSupport.guardEvaluation d.guard d.guard_trans (d.primes i) (c : RatFunc ℚ))
  simp only [map_ratCast]

theorem guard_prod_eq_one (d : SparsePrimaryDomain.Places) (q : ℕ → RatFunc ℚ)
    (hg : ∀ n p, SparsePrimaryDomain.vertical d (.inr p) (q n) = 1)
    (e : ℕ →₀ ℤ) (p : GuardSupport.PrimeIndex) :
    SparsePrimaryDomain.vertical d (.inr p) (e.prod fun j m => (q (2 * j)) ^ m) = 1 := by
  simp [map_finsuppProd, map_zpow₀, hg]

theorem primary_prod_eq_exp_neg (d : SparsePrimaryDomain.Places) (q : ℕ → RatFunc ℚ)
    (hp : ∀ n i, SparsePrimaryDomain.vertical d (.inl i) (q n) = exp (-qProfile n i))
    (e : ℕ →₀ ℤ) (k : ℕ) :
    SparsePrimaryDomain.vertical d (.inl (4 * k + 1)) (e.prod fun j m => (q (2 * j)) ^ m) =
      exp (-(e k)) := by
  rw [map_finsuppProd]
  rw [Finsupp.prod_eq_single k]
  · rw [map_zpow₀, hp, qProfile_even_odd, ite_eq_left rfl]
    simp
  · intro j _hj hjk
    simp only [map_zpow₀, hp, qProfile_even_odd, ite_eq_right hjk, neg_zero, exp_zero, one_zpow]
  · intro _hk
    simp

theorem even_ratios_independent (d : SparsePrimaryDomain.Places) (q : ℕ → RatFunc ℚ)
    (hp : ∀ n i, SparsePrimaryDomain.vertical d (.inl i) (q n) = exp (-qProfile n i))
    (hg : ∀ n p, SparsePrimaryDomain.vertical d (.inr p) (q n) = 1)
    (e : ℕ →₀ ℤ) (c : ℚ) (_hc : c ≠ 0)
    (hrel : e.prod (fun j m => (q (2 * j)) ^ m) = RatFunc.C c) : e = 0 := by
  ext k
  have hgC : SparsePrimaryDomain.vertical d (.inr (d.primes (4 * k + 1))) (RatFunc.C c) = 1 := by
    rw [← hrel]
    exact guard_prod_eq_one d q hg e _
  have hpC : SparsePrimaryDomain.vertical d (.inl (4 * k + 1)) (RatFunc.C c) = 1 := by
    rw [vertical_C_primary_eq_guard]
    exact hgC
  have h := primary_prod_eq_exp_neg d q hp e k
  rw [hrel, hpC] at h
  have he : -(e k) = 0 := exp_eq_one.mp h.symm
  simpa using he

/-- The actual even ratios are independent modulo rational constants. -/
theorem evenRatiosIndependentModuloRationals
    (D : Subring (RatFunc ℚ)) (d : SparsePrimaryDomain.Places) (q : ℕ → D)
    (hp : ∀ n i, SparsePrimaryDomain.vertical d (.inl i) (q n) = exp (-qProfile n i))
    (hg : ∀ n p, SparsePrimaryDomain.vertical d (.inr p) (q n) = 1) :
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
    PaperTargets.SquareChainConclusion (SparsePrimaryDomain.domain S d)
      ⟨RatFunc.X, SparsePrimaryDomain.X_mem S d⟩ := by
  let qD := domainRatio d q hp hg
  let xD := endpoint d q hunit hp hg hfirst
  have hqD : ∀ n, qD n ≠ 0 ∧ ¬ IsUnit (qD n) := by
    intro n
    constructor
    · intro hn
      exact q_ne_zero q hunit n (congrArg (fun z : SparsePrimaryDomain.domain S d =>
        (z : RatFunc ℚ)) hn)
    · exact q_not_isUnit d q hp _
  have hxD : ∀ n, xD n ≠ 0 := by
    intro n hn
    exact chainValue_ne_zero q hunit n (congrArg (fun z : SparsePrimaryDomain.domain S d =>
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
    ¬ WfDvdMonoid (SparsePrimaryDomain.domain S d) := by
  obtain ⟨r, x, hr, hx, _, _, hrec, _⟩ := squareChainConclusion d q hunit hp hg hfirst
  exact not_wfDvdMonoid_of_nonunit_recurrence x (fun n => r (2 * n)) hx
    (fun n => (hr (2 * n)).2) (fun n => by rw [hrec n, mul_comm])

end UnconditionalCounterexample.SparseSquareChain
