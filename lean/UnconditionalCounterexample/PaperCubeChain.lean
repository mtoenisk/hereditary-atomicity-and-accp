import UnconditionalCounterexample.PaperSquareChainActual

/-!
# The older cube chain in the actual constructed domain

The literal endpoints `X³ / ∏ j < n, b_j` belong to the same domain used by
the manuscript square chain. Each actual normalized `b_j` has primary order
three at coordinate `2*j` and order zero elsewhere; each guard sees a unit.
Their disjoint primary supports bound every prefix order by three. The
recurrence with these nonunit ratios gives `HasStrictChainAt (parameter ^ 3)`,
closing the cube-chain clause of the older note-level `CoreConclusion`.

All inputs are the actual `PaperConstruction` data; no profile, membership,
or chain-existence hypotheses remain in the endpoint theorem.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperCubeChain
open Polynomial WithZero NormalizedWords PrimaryWordProfiles PaperConstruction
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- The actual normalized b_n, in the same pole algebra as the paper's q_n. -/
def bPole (n : ℕ) : PoleAlgebra.generated poles := generatorPole (Generator.b n).stage

@[simp] theorem bPole_coe (n : ℕ) : (bPole n : RatFunc ℚ) = construction.chain.b n := rfl

theorem bPole_isUnit (n : ℕ) : IsUnit (bPole n) := generatorPole_isUnit _

theorem b_primary (n i : ℕ) :
    PairedDomain.vertical places (.inl i) (construction.chain.b n) = exp (-bWeight n i) :=
  generator_b_valuation n i

theorem b_guard (n : ℕ) (p : GuardSupport.PrimeIndex) :
    PairedDomain.vertical places (.inr p) (construction.chain.b n) = 1 :=
  generator_guard_valuation (Generator.b n).stage p

theorem bWeight_nonneg (n i : ℕ) : 0 ≤ bWeight n i := by
  unfold bWeight
  split_ifs <;> norm_num

theorem sum_bWeight_le_three (s : Finset ℕ) (i : ℕ) :
    (∑ j ∈ s, bWeight j i) ≤ 3 := by
  classical
  by_cases h : ∃ j ∈ s, i = 2 * j
  · obtain ⟨j, hj, hij⟩ := h
    rw [Finset.sum_eq_single j]
    · simp [bWeight, hij]
    · intro k hk hkj
      have hik : i ≠ 2 * k := by omega
      simp [bWeight, hik]
    · exact fun hnot => (hnot hj).elim
  · have hzero : ∀ j ∈ s, bWeight j i = 0 := by
      intro j hj
      have hij : i ≠ 2 * j := fun hh => h ⟨j, hj, hh⟩
      simp [bWeight, hij]
    simp [Finset.sum_eq_zero hzero]

/-- The literal prefix product of the constructor's b_n. -/
def bPrefix (n : ℕ) : RatFunc ℚ := ∏ j ∈ Finset.range n, construction.chain.b j

/-- The legacy endpoint t³ / (b₀⋯b_(n−1)). -/
def chainValue (n : ℕ) : RatFunc ℚ := RatFunc.X ^ 3 / bPrefix n

theorem prefix_ne_zero (n : ℕ) : bPrefix n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => construction.chain.b_ne_zero j)

theorem prefix_inv_mem (n : ℕ) : (bPrefix n)⁻¹ ∈ PoleAlgebra.generated poles := by
  induction n with
  | zero => simp [bPrefix]
  | succ n ih =>
    simp only [bPrefix, Finset.prod_range_succ, mul_inv_rev]
    exact (PoleAlgebra.generated poles).mul_mem
      (PaperSquareChain.q_inv_mem bPole bPole_isUnit n) ih

theorem chainValue_mem_pole (n : ℕ) : chainValue n ∈ PoleAlgebra.generated poles := by
  simpa only [chainValue, div_eq_mul_inv] using
    (PoleAlgebra.generated poles).mul_mem
      ((PoleAlgebra.generated poles).pow_mem (PoleAlgebra.X_mem poles) 3) (prefix_inv_mem n)

theorem primary_prefix (n i : ℕ) : PairedDomain.vertical places (.inl i) (bPrefix n) =
    exp (-(∑ j ∈ Finset.range n, bWeight j i)) := by
  induction n with
  | zero => simp [bPrefix]
  | succ n ih =>
    simp only [bPrefix, Finset.prod_range_succ, map_mul] at ih ⊢
    rw [ih, b_primary, Finset.sum_range_succ, neg_add, exp_add]

theorem guard_prefix (n : ℕ) (p : GuardSupport.PrimeIndex) :
    PairedDomain.vertical places (.inr p) (bPrefix n) = 1 := by
  simp only [bPrefix, map_prod, b_guard, Finset.prod_const_one]

/-- Every literal cube endpoint lies in the actual constructed domain. -/
theorem chainValue_mem (n : ℕ) : chainValue n ∈ domain := by
  apply (IntersectionDomain.div_mem_iff _ _ (prefix_ne_zero n)).mpr
  refine ⟨chainValue_mem_pole n, ?_⟩
  rintro (i | p)
  · have hX : PairedDomain.vertical places (.inl i) (RatFunc.X ^ 3) ≤ exp (-3) := by
      rw [map_pow]
      calc
        PairedDomain.vertical places (.inl i) RatFunc.X ^ 3 ≤ exp (-1 : ℤ) ^ 3 :=
          pow_le_pow_left₀ zero_le
            (PaperSquareChain.primary_X_le places first_primary_valuation i) 3
        _ = exp (-3 : ℤ) := by norm_num [← exp_nsmul, nsmul_eq_mul]
    rw [primary_prefix]
    exact hX.trans (exp_le_exp.mpr (by have h := sum_bWeight_le_three (Finset.range n) i; omega))
  · rw [guard_prefix]
    exact ((IntersectionDomain.mem_intersection _ _ _).mp
      (domain.pow_mem (PairedDomain.X_mem poles places) 3)).2 (.inr p)

theorem b_mem (n : ℕ) : construction.chain.b n ∈ domain := by
  apply (IntersectionDomain.mem_intersection _ _ _).mpr
  refine ⟨(bPole n).property, ?_⟩
  rintro (i | p)
  · rw [b_primary, ← exp_zero]
    exact exp_le_exp.mpr (neg_nonpos.mpr (bWeight_nonneg n i))
  · rw [b_guard]

/-- The literal b_n as an element of the actual domain. -/
def ratio (n : ℕ) : domain := ⟨construction.chain.b n, b_mem n⟩

@[simp] theorem ratio_coe (n : ℕ) : (ratio n : RatFunc ℚ) = construction.chain.b n := rfl

theorem ratio_not_isUnit (n : ℕ) : ¬ IsUnit (ratio n) := by
  intro hu
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
  have hm : construction.chain.b n * (y : RatFunc ℚ) = 1 :=
    congrArg (fun z : domain => (z : RatFunc ℚ)) hy
  have hvy := ((IntersectionDomain.mem_intersection _ _ _).mp y.property).2 (.inl (2 * n))
  have hvb : PairedDomain.vertical places (.inl (2 * n)) (construction.chain.b n) < 1 := by
    rw [b_primary]
    simp only [bWeight]
    rw [← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  have hvprod := congrArg (PairedDomain.vertical places (.inl (2 * n))) hm
  rw [map_mul, map_one] at hvprod
  have hlt : PairedDomain.vertical places (.inl (2 * n)) (construction.chain.b n) *
      PairedDomain.vertical places (.inl (2 * n)) (y : RatFunc ℚ) < 1 := by
    calc
      _ ≤ PairedDomain.vertical places (.inl (2 * n)) (construction.chain.b n) * 1 :=
        mul_le_mul_of_nonneg_left hvy zero_le
      _ < 1 := by simpa only [mul_one] using hvb
  rw [hvprod] at hlt
  exact (lt_irrefl _ hlt)

def endpoint (n : ℕ) : domain := ⟨chainValue n, chainValue_mem n⟩

@[simp] theorem endpoint_coe (n : ℕ) :
    (endpoint n : RatFunc ℚ) = RatFunc.X ^ 3 / ∏ j ∈ Finset.range n, construction.chain.b j := rfl

@[simp] theorem endpoint_zero : endpoint 0 = parameter ^ 3 := by
  apply Subtype.ext
  simp [endpoint, chainValue, bPrefix, parameter]

theorem endpoint_ne_zero (n : ℕ) : endpoint n ≠ 0 := by
  intro h
  have hz : chainValue n = 0 := congrArg (fun z : domain => (z : RatFunc ℚ)) h
  exact (div_ne_zero (pow_ne_zero 3 RatFunc.X_ne_zero) (prefix_ne_zero n)) hz

/-- Each consecutive ratio is the actual b_n of the same selected raw family. -/
theorem endpoint_recurrence (n : ℕ) : endpoint n = endpoint (n + 1) * ratio n := by
  apply Subtype.ext
  change chainValue n = chainValue (n + 1) * construction.chain.b n
  simp only [chainValue, bPrefix, Finset.prod_range_succ]
  field_simp [prefix_ne_zero n, construction.chain.b_ne_zero n]

theorem strictMono_principalIdeals :
    StrictMono (fun n => Ideal.span ({endpoint n} : Set domain)) :=
  strictMono_principalIdeals_of_nonunit_recurrence endpoint ratio endpoint_ne_zero
    ratio_not_isUnit endpoint_recurrence

/-- The older note-level cube chain holds for the very same actual domain. -/
theorem hasStrictChainAt_cube : HasStrictChainAt (parameter ^ 3) :=
  ⟨endpoint, endpoint_zero, endpoint_ne_zero, strictMono_principalIdeals⟩

/-- The exact final clause of the older note-level `CoreConclusion`. -/
theorem exists_cube_chain :
    ∃ a : domain, (a : RatFunc ℚ) = RatFunc.X ^ 3 ∧ HasStrictChainAt a :=
  ⟨parameter ^ 3, rfl, hasStrictChainAt_cube⟩

end UnconditionalCounterexample.PaperCubeChain
