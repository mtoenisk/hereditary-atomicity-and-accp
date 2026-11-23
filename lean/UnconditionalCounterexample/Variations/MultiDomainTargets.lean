import UnconditionalCounterexample.Variations.MultiDomainLowMoving
import UnconditionalCounterexample.StageExponents

/-!
# Local target values for the multivariate singleton schedule

The targets use the same rules in the primary field, in an unramified
guard field, and at the rational point of the extra pullback. At a q-step
with zero prescribed order, the previous numerator is used whenever it
is a unit. Approximating the raw numerator in its indicated neighbourhood
then gives the prescribed order and the return modulo a power of p.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain.Targets

open NormalizedWords PrimaryWordProfiles WithZero
open scoped Topology

def generator (i : ℕ) : Generator := (StageExponents.stage_surjective i).choose

@[simp] theorem generator_stage (a : Generator) : generator a.stage = a :=
  StageExponents.stage_injective (StageExponents.stage_surjective a.stage).choose_spec

theorem stage_generator (i : ℕ) : (generator i).stage = i :=
  (StageExponents.stage_surjective i).choose_spec

/-- Guards and the reserved point have no primary label. -/
def order (g : Generator) : Option ℕ → ℕ
  | none => 0
  | some j => match g with
    | .b n => (bWeight n j).toNat
    | .q n => (qWeight n j).toNat

@[simp] theorem b_order (n j : ℕ) : (order (.b n) (some j) : ℤ) = bWeight n j :=
  Int.toNat_of_nonneg (PaperCubeChain.bWeight_nonneg n j)

@[simp] theorem q_order (n j : ℕ) : (order (.q n) (some j) : ℤ) = qWeight n j := by
  apply Int.toNat_of_nonneg
  simp only [qWeight]
  split_ifs <;> omega

theorem order_zero_later_birth (i j : ℕ) (h : 2*i+2 ≤ j) : order (generator i) (some j) = 0 := by
  obtain ⟨a,rfl⟩ := StageExponents.stage_surjective i
  rw [generator_stage]
  cases a with
  | b n =>
    cases n with
    | zero => simp only [Generator.stage] at h; simp [order,bWeight,show j ≠ 0 by omega]
    | succ n => simp only [Generator.stage] at h; simp [order,bWeight,show j ≠ 2*(n+1) by omega]
  | q n =>
    simp only [Generator.stage] at h
    simp [order,qWeight, show j ≠ 2*n by omega, show j ≠ 2*n+1 by omega, show j ≠ 2*n+2 by omega]

variable {L : Type*} [Field L]

/-- Values of the earlier moving elements computed in the local field. -/
def moving (t : L) (u : ℕ → L) : ℕ → L
  | 0 => t
  | n+1 => moving t u n * u (Generator.b (n+1)).stage / u (Generator.q n).stage

def previous (t : L) (u : ℕ → L) : Generator → L
  | .b _ => 0
  | .q n => moving t u n * u (Generator.b (n+1)).stage

theorem previous_congr (t : L) (u u' : ℕ → L) (a : Generator)
    (h : ∀ i < a.stage, u i = u' i) : previous t u a = previous t u' a := by
  cases a with
  | b n => rfl
  | q n =>
    have hm : ∀ k ≤ n, moving t u k = moving t u' k := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        simp only [moving]
        rw [ih (by omega), h _ (show (Generator.b (k+1)).stage < (Generator.q n).stage by
          simp only [Generator.stage]; omega), h _ (show (Generator.q k).stage < (Generator.q n).stage by
          simp only [Generator.stage]; omega)]
    simp only [previous, hm n le_rfl, h _ (show (Generator.b (n+1)).stage < (Generator.q n).stage by
      simp [Generator.stage])]

variable (v : Valuation L ℤᵐ⁰) (p : ℕ)

def target (k : ℕ) (z : L) : L := if k = 0 ∧ v z = 1 then z else (p : L)^k

theorem target_value (hp : v (p : L) = exp (-1)) (k : ℕ) (z : L) :
    v (target v p k z) = exp (-(k : ℤ)) := by
  unfold target
  split_ifs with h
  · simp [h.1, h.2]
  · rw [map_pow, hp, ← exp_nsmul]
    simp

theorem target_ne_zero (hp : v (p : L) = exp (-1)) (k : ℕ) (z : L) : target v p k z ≠ 0 :=
  fun he ↦ exp_ne_zero ((target_value v p hp k z).symm.trans (he ▸ v.map_zero))

/-- Prescribe the raw value using the denominator cleared at this stage.
The relative error allows division by p raised to the return precision. -/
def neighborhood (d y : L) (k : ℕ) : Set L :=
  {x | v (x - d*y) < v (d*y*(p : L)^k)}

theorem neighborhood_mem_nhds {L : Type*} [NormedField L] (v : Valuation L ℤᵐ⁰)
    (compat : ∀ a b : L, v a < v b ↔ ‖a‖ < ‖b‖) (p : ℕ) (hp : (p : L) ≠ 0)
    {d y : L} (hd : d ≠ 0) (hy : y ≠ 0) (k : ℕ) : neighborhood v p d y k ∈ 𝓝 (d*y) := by
  refine Filter.mem_of_superset (Metric.ball_mem_nhds _ (norm_pos_iff.mpr
    (mul_ne_zero (mul_ne_zero hd hy) (pow_ne_zero k hp)))) ?_
  intro x hx
  exact (compat _ _).mpr (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)

/-- The normalized value has the requested valuation and its relative
error is integral after division by the specified prime power. -/
theorem normalized_and_return (hp : (p : L) ≠ 0) {x d y : L} (hd : d ≠ 0) (hy : y ≠ 0)
    (k : ℕ) (h : x ∈ neighborhood v p d y k) :
    v (x/d) = v y ∧ v ((y/(x/d)-1)/(p : L)^k) ≤ 1 := by
  have h' : v (x-d*y) < v (d*y) * v ((p : L)^k) := by simpa only [neighborhood, Set.mem_ofPred_eq, map_mul] using h
  have hle : v ((p : L)^k) ≤ 1 := by
    rw [map_pow]
    exact pow_le_one₀ zero_le (IntersectionDomain.valuation_natCast_le_one v p)
  have hxv : v x = v (d*y) := v.map_eq_of_sub_lt (h'.trans_le (by simpa using mul_le_mul_of_nonneg_left hle (zero_le : 0 ≤ v (d*y))))
  have hx : x ≠ 0 := v.ne_zero_iff.mp (hxv ▸ v.ne_zero_iff.mpr (mul_ne_zero hd hy))
  constructor
  · rw [map_div₀, hxv, map_mul, mul_div_cancel_left₀ _ (v.ne_zero_iff.mpr hd)]
  · have he : (y/(x/d)-1)/(p : L)^k = (d*y-x) / (x*(p : L)^k) := by field_simp
    rw [he, map_div₀, div_le_one₀ (v.pos_iff.mpr (mul_ne_zero hx (pow_ne_zero _ hp))), map_mul,
      v.map_sub_swap, hxv]
    exact h'.le

end UnconditionalCounterexample.Variations.MultiDomain.Targets
