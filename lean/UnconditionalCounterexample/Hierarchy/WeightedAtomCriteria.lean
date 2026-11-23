import UnconditionalCounterexample.Hierarchy.WeightedQuasiAtomic

/-!
# Atom criteria from the integral orders of a pole unit

A prime with order one on exactly one fiber is irreducible when the orders
of pole units on that fiber all have the same parity. Dividing by a pole
unit supported on part of a fiber detects reducibility at larger orders.
-/

namespace UnconditionalCounterexample.Hierarchy.Weighted

open IntersectionDomain DiscreteOrders WithZero

variable {K I : Type*} [Field K] (B : Subring K) (v : I → Valuation K ℤᵐ⁰)

local notation "R" => intersection B v

theorem order_nonneg_on_ring (x : R) (i : I) : 0 ≤ order (v i) (x : K) := by
  by_cases h : (x : K) = 0
  · simp [h]
  exact (order_nonneg_iff _ h).mpr (((mem_intersection _ _ _).mp x.property).2 i)

theorem order_unit_on_ring (x : R) (hu : IsUnit x) (i : I) : order (v i) (x : K) = 0 :=
  order_eq_zero_of_isUnit R _ (fun _ ht => ((mem_intersection _ _ _).mp ht).2 i) hu

theorem poleUnit_isUnit_of_orders_zero (x : R) (hu : IsUnit (inclusion B v x))
    (h : ∀ i, order (v i) (x : K) = 0) : IsUnit x := by
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have he : (x : K) * (y : K) = 1 := congrArg Subtype.val hy
  have hx := left_ne_zero_of_mul (he.trans_ne one_ne_zero)
  have hy0 := right_ne_zero_of_mul (he.trans_ne one_ne_zero)
  have hymem : (y : K) ∈ R := by
    apply (mem_intersection _ _ _).mpr
    refine ⟨y.property, fun i => (order_nonneg_iff _ hy0).mp ?_⟩
    have hs := order_mul (v i) hx hy0
    rw [he, order_one, h i, zero_add] at hs
    exact hs.le
  exact isUnit_iff_exists_inv.mpr ⟨⟨y,hymem⟩, Subtype.ext he⟩

/-- An element with uniform order one on a single fiber is irreducible
if every pole unit has constant parity on that fiber. -/
theorem irreducible_of_fiber_parity (q : R) (hu : IsUnit (inclusion B v q))
    (C : Set I) [DecidablePred (· ∈ C)] (hC : C.Nonempty)
    (hq : ∀ i, order (v i) (q : K) = if i ∈ C then 1 else 0)
    (hpar : ∀ (x : R), IsUnit (inclusion B v x) → ∀ i ∈ C, ∀ j ∈ C,
      order (v i) (x : K) % 2 = order (v j) (x : K) % 2) : Irreducible q := by
  obtain ⟨j,hj⟩ := hC
  have hoj : order (v j) (q : K) = 1 := by simp [hq, hj]
  have hq0 : (q : K) ≠ 0 := by intro hz; simp [hz] at hoj
  refine ⟨fun h => by simp [order_unit_on_ring B v q h j] at hoj, fun {a b} he => ?_⟩
  have hprod : (q : K) = (a : K) * (b : K) := congrArg Subtype.val he
  have hn := hprod ▸ hq0
  have hunit := hu
  rw [he, map_mul, IsUnit.mul_iff] at hunit
  have hadd (i : I) : order (v i) (a : K) + order (v i) (b : K) = if i ∈ C then 1 else 0 :=
    (order_mul _ (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn)).symm.trans (hprod ▸ hq i)
  have ho (i : I) := order_nonneg_on_ring B v a i
  have hp (i : I) := order_nonneg_on_ring B v b i
  specialize hpar a hunit.1
  by_cases hz : order (v j) (a : K) = 0
  · left
    apply poleUnit_isUnit_of_orders_zero B v a hunit.1
    intro i
    have hi := hadd i
    have ha₀ := ho i
    have hb₀ := hp i
    by_cases hc : i ∈ C
    · simp only [hc, ↓reduceIte] at hi
      have hmod := hpar i hc j hj
      rw [hz] at hmod
      omega
    · simp only [hc, ↓reduceIte] at hi
      omega
  · right
    apply poleUnit_isUnit_of_orders_zero B v b hunit.2
    intro i
    have hi := hadd i
    have hn₁ := ho i
    have hn₂ := hp i
    by_cases hc : i ∈ C
    · simp only [hc, ↓reduceIte] at hi
      have hj' := hadd j
      simp only [hj, ↓reduceIte] at hj'
      have hm := hpar i hc j hj
      have := ho j
      have := hp j
      omega
    · simp only [hc, ↓reduceIte] at hi
      omega

/-- A pole unit whose orders fit below those of an element divides it
in the intersection, since its inverse is already available in the pole ring. -/
theorem poleUnit_dvd_of_order_le (u x : R) (hu : IsUnit (inclusion B v u))
    (hx : x ≠ 0) (hle : ∀ i, order (v i) (u : K) ≤ order (v i) (x : K)) : u ∣ x := by
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have he : (u : K) * (b : K) = 1 := congrArg Subtype.val hb
  have hu0 := left_ne_zero_of_mul (he.trans_ne one_ne_zero)
  have hx0 : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  apply (subring_dvd_iff_div_mem R u x (fun h => hu0 (congrArg Subtype.val h))).mpr
  apply (mem_intersection _ _ _).mpr
  refine ⟨?_, fun i => (order_nonneg_iff _ (div_ne_zero hx0 hu0)).mp ?_⟩
  · have hb' : (u : K)⁻¹ = b := inv_eq_of_mul_eq_one_right he
    rw [div_eq_mul_inv, hb']
    exact B.mul_mem (intersection_le B v x.property) b.property
  · rw [order_div _ hx0 hu0]
    exact sub_nonneg.mpr (hle i)

/-- A proper split of the orders by a pole unit rules out irreducibility. -/
theorem not_irreducible_of_split (x u : R) (hx : x ≠ 0) (hu : IsUnit (inclusion B v u))
    (hle : ∀ i, order (v i) (u : K) ≤ order (v i) (x : K))
    (ha : ∃ i, 0 < order (v i) (u : K))
    (hb : ∃ i, order (v i) (u : K) < order (v i) (x : K)) : ¬ Irreducible x := by
  obtain ⟨c,hc⟩ := poleUnit_dvd_of_order_le B v u x hu hx hle
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hx0 : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  have he : (x : K) = (u : K) * (c : K) := congrArg Subtype.val hc
  have hn := he ▸ hx0
  intro hirr
  rcases hirr.isUnit_or_isUnit hc with h | h
  · exact (ne_of_gt hi) (order_unit_on_ring B v u h i)
  · rw [he, order_mul _ (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn),
      order_unit_on_ring B v c h j, add_zero] at hj
    exact lt_irrefl _ hj

end UnconditionalCounterexample.Hierarchy.Weighted
