import Factorization.WeakACCP
import UnconditionalCounterexample.PaperSquareChain
import UnconditionalCounterexample.PrimaryWordProfiles

/-!
# The chains at the two squares in §9.2

Given the two-colour ratio profiles at the two centres on one intersection
ring, the finite products of even ratios can be divided out of both seed
squares. Scaling the second chain gives the literal square of `1 - t`.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open WithZero IntersectionDomain PaperSquareChain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Multiplying every endpoint by the same nonzero scalar preserves strictness. -/
theorem chainAt_mul {a : R} (h : HasStrictChainAt a) {s : R} (hs : s ≠ 0) :
    HasStrictChainAt (s * a) := by
  obtain ⟨x, hx, hn, hchain⟩ := h
  refine ⟨fun n => s * x n, congrArg (s * ·) hx, fun n => mul_ne_zero hs (hn n),
    strictMono_nat_of_lt_succ fun n => ?_⟩
  obtain ⟨_, u, hu, heq⟩ :=
    Ideal.span_singleton_lt_span_singleton.mp (hchain (Nat.lt_succ_self n))
  exact Ideal.span_singleton_lt_span_singleton.mpr
    ⟨mul_ne_zero hs (hn _), u, hu, by simpa only [mul_assoc] using congrArg (s * ·) heq⟩

omit [IsDomain R] in
/-- The integral Bézout coefficients apply in every unital ring containing the coordinate. -/
theorem squares_isCoprime (t : R) : IsCoprime (t ^ 2) ((1 - t) ^ 2) :=
  ⟨3 - 2 * t, 1 + 2 * t, by ring⟩

section Ratios

variable {K G : Type*} [Field K]
  (B : Subring K) (v : (Bool × ℕ ⊕ G) → Valuation K ℤᵐ⁰)
  (q : Bool → ℕ → Bˣ)
  (hp : ∀ c n d i, v (.inl (d, i)) (((q c n : B) : K)) =
    if c = d then exp (-qProfile n i) else 1)
  (hg : ∀ c n g, v (.inr g) (((q c n : B) : K)) = 1)

include hp hg

/-- Each prescribed ratio is integral, and its odd coordinate detects that it is a nonunit. -/
theorem ratio_mem_nonunit (c : Bool) (n : ℕ) :
    ∃ h : ((q c n : B) : K) ∈ intersection B v,
      ¬ IsUnit (⟨(q c n : B), h⟩ : intersection B v) := by
  refine ⟨(mem_intersection _ _ _).mpr ⟨(q c n : B).property, ?_⟩, ?_⟩
  · rintro (⟨d, i⟩ | g)
    · rw [hp]
      split_ifs
      · exact exp_le_one_iff.mpr (neg_nonpos.mpr (qProfile_nonneg _ _))
      · exact le_rfl
    · rw [hg]
  · intro hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
    let V := v (.inl (c, 2*n+1))
    have hv : V ((q c n : B) : K) < 1 := by
      simp [V, hp, qProfile, exp_lt_one_iff]
    have hy' := ((mem_intersection _ _ _).mp y.property).2 (.inl (c, 2*n+1))
    have hprod : ((q c n : B) : K) * (y : K) = 1 :=
      congrArg (intersection B v).subtype hy
    have hlt : V ((q c n : B) : K) * V (y : K) < 1 := calc
      _ ≤ V ((q c n : B) : K) * 1 := mul_le_mul_of_nonneg_left hy' zero_le
      _ < 1 := by simpa only [mul_one] using hv
    simp only [← map_mul, hprod, map_one, lt_self_iff_false] at hlt

/-- The finite product stays a unit in the pole ring, and at every primary of
the selected colour its additive order is at most two. -/
theorem square_prefix_quotient_mem (c : Bool) (s : intersection B v)
    (hs : ∀ i, v (.inl (c, i)) (s : K) ≤ exp (-1))
    (n : ℕ) :
    (s : K)^2 / (∏ j ∈ Finset.range n, ((q c (2*j) : B) : K)) ∈ intersection B v := by
  let P : Bˣ := ∏ j ∈ Finset.range n, q c (2*j)
  have hcoe : ((P : B) : K) = ∏ j ∈ Finset.range n, ((q c (2*j) : B) : K) := by
    simp [P]
  rw [← hcoe]
  have hP0 : ((P : B) : K) ≠ 0 := fun h => P.ne_zero (Subtype.ext h)
  apply (div_mem_iff B v hP0).mpr
  have hbase := (mem_intersection B v _).mp s.property
  constructor
  · have hinv : ((P⁻¹ : Bˣ) : B) * (P : B) = 1 := P.inv_mul
    have heq : ((((P⁻¹ : Bˣ) : B) : K)) = ((P : B) : K)⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrArg B.subtype hinv)
    rw [div_eq_mul_inv, ← heq]
    exact B.mul_mem (B.pow_mem hbase.1 _) ((P⁻¹ : Bˣ) : B).property
  · rw [hcoe]
    rintro (⟨d, i⟩ | g)
    · simp only [map_prod, hp]
      by_cases hcd : c = d
      · subst d
        simp only [eq_self, ite_true]
        rw [PrimaryWordProfiles.prod_exp_neg]
        have hbound := sum_qProfile_even_le_two (Finset.range n) i
        calc
          v (.inl (c, i)) ((s : K) ^ 2) ≤ exp (-1 : ℤ) ^ 2 := by
            rw [map_pow]
            exact pow_le_pow_left₀ zero_le (hs i) _
          _ = exp (-2 : ℤ) := by norm_num [← exp_nsmul, nsmul_eq_mul]
          _ ≤ _ := exp_le_exp.mpr (by omega)
      · simp only [ite_eq_right hcd, Finset.prod_const_one]
        exact ((mem_intersection _ _ _).mp ((intersection B v).pow_mem s.property 2)).2 _
    · simp only [map_prod, hg, Finset.prod_const_one]
      exact ((mem_intersection _ _ _).mp ((intersection B v).pow_mem s.property 2)).2 _

/-- The endpoints are the seed square divided by literal prefixes of the even ratios. -/
theorem seed_square_chain (c : Bool) (s : intersection B v) (hs0 : s ≠ 0)
    (hs : ∀ i, v (.inl (c, i)) (s : K) ≤ exp (-1)) : HasStrictChainAt (s^2) := by
  let P (n : ℕ) : K := ∏ j ∈ Finset.range n, ((q c (2*j) : B) : K)
  let x (n : ℕ) : intersection B v :=
    ⟨(s : K)^2 / P n, square_prefix_quotient_mem B v q hp hg c s hs n⟩
  let b (n : ℕ) : intersection B v :=
    ⟨(q c (2*n) : B), (ratio_mem_nonunit B v q hp hg c (2*n)).choose⟩
  have hq0 (n : ℕ) : ((q c n : B) : K) ≠ 0 := fun h => (q c n).ne_zero (Subtype.ext h)
  have hP0 (n : ℕ) : P n ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hq0 _
  have hx (n : ℕ) : x n ≠ 0 := fun h =>
    div_ne_zero (pow_ne_zero _ fun h => hs0 (Subtype.ext h)) (hP0 n)
      (congrArg (intersection B v).subtype h)
  refine ⟨x, Subtype.ext (by simp [x, P]), hx,
    strictMono_principalIdeals_of_nonunit_recurrence x b hx
      (fun n => (ratio_mem_nonunit B v q hp hg c (2*n)).choose_spec) ?_⟩
  intro n
  apply Subtype.ext
  change (s : K)^2 / P n = ((s : K)^2 / P (n+1)) * ((q c (2*n) : B) : K)
  rw [show P (n+1) = P n * ((q c (2*n) : B) : K) by exact Finset.prod_range_succ ..,
    div_mul_eq_div_div, div_mul_cancel₀ _ (hq0 _)]

/-- Both chains and the obstruction hold in the very same intersection.
The second input seed is specified by the integral equation `2s = t - 1`. -/
theorem two_square_chains [CharZero K] (t s : intersection B v)
    (ht0 : t ≠ 0) (hs0 : s ≠ 0) (hseed : 2 * s = t - 1)
    (ht : ∀ i, v (.inl (false, i)) (t : K) ≤ exp (-1))
    (hs : ∀ i, v (.inl (true, i)) (s : K) ≤ exp (-1)) :
    HasStrictChainAt (t^2) ∧ HasStrictChainAt ((1-t)^2) ∧
      IsCoprime (t^2) ((1-t)^2) ∧ ¬ Factorization.IsWeakACCP (intersection B v) := by
  have hleft := seed_square_chain B v q hp hg false t ht0 ht
  have hright := chainAt_mul (seed_square_chain B v q hp hg true s hs0 hs)
    (show (4 : intersection B v) ≠ 0 by norm_num)
  have heq : (1-t)^2 = 4*s^2 := by
    calc (1-t)^2 = (t-1)^2 := by ring
         _ = 4*s^2 := by rw [← hseed]; ring
  rw [← heq] at hright
  exact ⟨hleft, hright, squares_isCoprime t,
    Factorization.not_isWeakACCP_of_isCoprime_of_strictChains (squares_isCoprime t) hleft hright⟩

end Ratios
end UnconditionalCounterexample.TwoChains
