import UnconditionalCounterexample.LocalEvaluation
import UnconditionalCounterexample.SeparationExclusions
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Permanent geometric reservations and finite tests

Fix an actual enumeration of the algebraic closure of the rationals before the
simultaneous construction. At zero-based stage n, inspect its first n+1 points
and retain those where all prior raws are nonzero. The finite list depends only
on this prior prefix. Current point nonvanishing makes reservations permanent.

The concrete finite Test list includes point preservation and every listed
word's pair and tangent constraints. Products of previous raw powers are
nonzero at reserved points, making those tests valid. Every final retained
point and pair occurs eventually, producing the eventual tests used in curve recognition.
The actual stage inequalities remain an explicit output of the finite successor.
-/

namespace UnconditionalCounterexample.GeometricReservations

open Polynomial Filter SeparationExclusions

/-- Fix a countable enumeration of the actual algebraic closure before recursion. -/
theorem exists_geometric_enumeration :
    ∃ a : ℕ → AlgebraicClosure ℚ, Function.Surjective a := by
  have hcount := LocalEvaluation.algebraic_countable (L := AlgebraicClosure ℚ)
  have heq : Set.ofPred (IsAlgebraic ℚ : AlgebraicClosure ℚ → Prop) = Set.univ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact Algebra.IsAlgebraic.isAlgebraic a
  have : Countable (AlgebraicClosure ℚ) := Set.countable_univ_iff.mp (heq ▸ hcount)
  exact exists_surjective_nat (AlgebraicClosure ℚ)

noncomputable def geometricEnumeration : ℕ → AlgebraicClosure ℚ :=
  exists_geometric_enumeration.choose

theorem geometricEnumeration_surjective : Function.Surjective geometricEnumeration :=
  exists_geometric_enumeration.choose_spec

section Reservations

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The earlier raw factors do not vanish at this point. -/
def RetainedBefore (F : ℕ → ℚ[X]) (n : ℕ) (a : K) : Prop :=
  ∀ h < n, (F h).eval₂ (algebraMap ℚ K) a ≠ 0

/-- The actual finite list at zero-based stage n, corresponding to the first
n+1 points at manuscript stage i=n+1. -/
noncomputable def reservedPoints (a : ℕ → K) (F : ℕ → ℚ[X]) (n : ℕ) : Finset K := by
  classical
  exact ((Finset.range (n + 1)).image a).filter (RetainedBefore F n)

theorem mem_reservedPoints (a : ℕ → K) (F : ℕ → ℚ[X]) (n : ℕ) (x : K) :
    x ∈ reservedPoints a F n ↔ (∃ j ≤ n, a j = x) ∧ RetainedBefore F n x := by
  classical
  simp only [reservedPoints, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨j, hj, hjeq⟩, hret⟩
    exact ⟨⟨j, by omega, hjeq⟩, hret⟩
  · rintro ⟨⟨j, hj, hjeq⟩, hret⟩
    exact ⟨⟨j, by omega, hjeq⟩, hret⟩

/-- Reservations depend only on the preceding raw factors, never on future
coefficients or on a later subring or factorization top. -/
theorem reservedPoints_congr_prefix (a : ℕ → K) (F G : ℕ → ℚ[X]) (n : ℕ)
    (hFG : ∀ h < n, F h = G h) : reservedPoints a F n = reservedPoints a G n := by
  ext x
  rw [mem_reservedPoints, mem_reservedPoints]
  have heq : RetainedBefore F n x ↔ RetainedBefore G n x := by
    constructor <;> intro h h' hh
    · rw [← hFG h' hh]
      exact h h' hh
    · rw [hFG h' hh]
      exact h h' hh
  exact and_congr_right (fun _ => heq)

/-- The current raw's point tests preserve every already reserved point. -/
theorem reservedPoints_subset_succ (a : ℕ → K) (F : ℕ → ℚ[X]) (n : ℕ)
    (hnew : ∀ x ∈ reservedPoints a F n, (F n).eval₂ (algebraMap ℚ K) x ≠ 0) :
    reservedPoints a F n ⊆ reservedPoints a F (n + 1) := by
  intro x hx
  obtain ⟨⟨j, hj, hjeq⟩, hret⟩ := (mem_reservedPoints a F n x).mp hx
  apply (mem_reservedPoints a F (n + 1) x).mpr
  refine ⟨⟨j, by omega, hjeq⟩, ?_⟩
  intro h hh
  by_cases hlt : h < n
  · exact hret h hlt
  · have heq : h = n := by omega
    simpa only [heq] using hnew x hx

theorem reservedPoints_monotone (a : ℕ → K) (F : ℕ → ℚ[X])
    (hnew : ∀ n x, x ∈ reservedPoints a F n → (F n).eval₂ (algebraMap ℚ K) x ≠ 0) :
    Monotone (reservedPoints a F) :=
  monotone_nat_of_le_succ (fun n => reservedPoints_subset_succ a F n (hnew n))

/-- Once a point is reserved, every raw factor remains nonzero there forever. -/
theorem reserved_point_permanent (a : ℕ → K) (F : ℕ → ℚ[X])
    (hnew : ∀ n x, x ∈ reservedPoints a F n → (F n).eval₂ (algebraMap ℚ K) x ≠ 0)
    (n : ℕ) (x : K) (hx : x ∈ reservedPoints a F n) :
    ∀ h, (F h).eval₂ (algebraMap ℚ K) x ≠ 0 := by
  intro h
  by_cases hlt : h < n
  · exact ((mem_reservedPoints a F n x).mp hx).2 h hlt
  · exact hnew h x (reservedPoints_monotone a F hnew (by omega : n ≤ h) hx)

/-- Every point retained in the final pole algebra occurs in all late lists. -/
theorem eventually_mem_reservedPoints (a : ℕ → K) (ha : Function.Surjective a)
    (F : ℕ → ℚ[X]) (x : K) (hx : ∀ h, (F h).eval₂ (algebraMap ℚ K) x ≠ 0) :
    ∀ᶠ n : ℕ in atTop, x ∈ reservedPoints a F n := by
  obtain ⟨j, hj⟩ := ha x
  filter_upwards [eventually_ge_atTop j] with n hn
  exact (mem_reservedPoints a F n x).mpr ⟨⟨j, hn, hj⟩, fun h _ => hx h⟩

/-- The older denominator products are nonzero at all current reserved points. -/
theorem old_product_eval_ne_zero (F : ℕ → ℚ[X]) (n : ℕ) (x : K)
    (hx : RetainedBefore F n x) (e : Fin n → ℕ) :
    (∏ h : Fin n, (F h.val) ^ e h).eval₂ (algebraMap ℚ K) x ≠ 0 := by
  rw [eval₂_finsetProd]
  apply Finset.prod_ne_zero_iff.mpr
  intro h _
  rw [eval₂_pow]
  exact pow_ne_zero _ (hx h.val h.isLt)

/-- The actual finite geometric test list: point preservation, every listed
word's tangent at each point, and every listed word's separation of distinct pairs. -/
noncomputable def finiteTests {W : Type*} [Fintype W]
    (A : Finset K) (m : W → ℕ) (H : W → K[X]) : Finset (Test K) := by
  classical
  exact (A.image Test.point ∪ A.biUnion (fun a => Finset.univ.image (fun w => Test.tangent a (m w) (H w)))) ∪
    A.biUnion (fun a => A.biUnion (fun b =>
      if a = b then ∅ else Finset.univ.image (fun w => Test.pair a b (m w) (H w))))

omit [Algebra ℚ K] in
theorem point_mem_finiteTests {W : Type*} [Fintype W]
    (A : Finset K) (m : W → ℕ) (H : W → K[X]) (a : K) (ha : a ∈ A) :
    Test.point a ∈ finiteTests A m H := by
  classical
  apply Finset.mem_union.mpr
  exact Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨a, ha, rfl⟩)))

omit [Algebra ℚ K] in
theorem tangent_mem_finiteTests {W : Type*} [Fintype W]
    (A : Finset K) (m : W → ℕ) (H : W → K[X]) (a : K) (ha : a ∈ A) (w : W) :
    Test.tangent a (m w) (H w) ∈ finiteTests A m H := by
  classical
  apply Finset.mem_union.mpr
  apply Or.inl
  apply Finset.mem_union.mpr
  exact Or.inr (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩⟩)

omit [Algebra ℚ K] in
theorem pair_mem_finiteTests {W : Type*} [Fintype W]
    (A : Finset K) (m : W → ℕ) (H : W → K[X]) (a b : K)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (w : W) :
    Test.pair a b (m w) (H w) ∈ finiteTests A m H := by
  classical
  apply Finset.mem_union.mpr
  apply Or.inr
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, Finset.mem_biUnion.mpr ⟨b, hb, ?_⟩⟩
  simp only [ite_eq_right hab]
  exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩

omit [Algebra ℚ K] in
/-- Positivity of the latest exponent and nonvanishing old denominators make
every generated test valid for the proper-exclusion theorem. -/
theorem finiteTests_valid {W : Type*} [Fintype W]
    (A : Finset K) (m : W → ℕ) (H : W → K[X])
    (hm : ∀ w, 0 < m w) (hH : ∀ a ∈ A, ∀ w, (H w).eval a ≠ 0) :
    ∀ t ∈ finiteTests A m H, t.Valid := by
  classical
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ht
      trivial
    · obtain ⟨a, ha, ht⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨hm w, hH a ha w⟩
  · obtain ⟨a, ha, ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨b, hb, ht⟩ := Finset.mem_biUnion.mp ht
    by_cases hab : a = b
    · simp only [ite_eq_left hab, Finset.notMem_empty] at ht
    · simp only [ite_eq_right hab] at ht
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨hab, hm w, hH a ha w, hH b hb w⟩

/-- For the actual denominators, products of prior raw powers, validity of
every scheduled test follows from the reservation definition itself. -/
theorem finiteTests_valid_old_products {W : Type*} [Fintype W]
    (a : ℕ → K) (F : ℕ → ℚ[X]) (n : ℕ) (m : W → ℕ) (e : W → Fin n → ℕ)
    (hm : ∀ w, 0 < m w) :
    ∀ t ∈ finiteTests (reservedPoints a F n) m
      (fun w => (∏ h : Fin n, (F h.val) ^ e w h).map (algebraMap ℚ K)), t.Valid := by
  apply finiteTests_valid _ _ _ hm
  intro x hx w
  rw [eval_map]
  exact old_product_eval_ne_zero F n x ((mem_reservedPoints a F n x).mp hx).2 (e w)

/-- Meeting the point tests is precisely the one-step permanence condition. -/
theorem nonvanishing_of_finiteTests {W : Type*} [Fintype W]
    (a : ℕ → K) (F : ℕ → ℚ[X]) (n : ℕ) (m : W → ℕ) (H : W → K[X])
    (h : ∀ t ∈ finiteTests (reservedPoints a F n) m H,
      t.Holds ((F n).map (algebraMap ℚ K))) :
    ∀ x ∈ reservedPoints a F n, (F n).eval₂ (algebraMap ℚ K) x ≠ 0 := by
  intro x hx
  simpa only [Test.Holds, eval_map] using
    h (Test.point x) (point_mem_finiteTests _ m H x hx)

/-- Every actual listed word eventually separates each fixed pair of retained
points, because that pair is eventually in the concrete finite test list. -/
theorem eventually_pair_tests
    (a : ℕ → K) (ha : Function.Surjective a) (F : ℕ → ℚ[X])
    (W : ℕ → Type*) [∀ n, Fintype (W n)]
    (m : ∀ n, W n → ℕ) (H : ∀ n, W n → K[X])
    (hstage : ∀ n t, t ∈ finiteTests (reservedPoints a F n) (m n) (H n) →
      t.Holds ((F n).map (algebraMap ℚ K)))
    (x y : K) (hxy : x ≠ y)
    (hx : ∀ h, (F h).eval₂ (algebraMap ℚ K) x ≠ 0)
    (hy : ∀ h, (F h).eval₂ (algebraMap ℚ K) y ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∀ w : W n,
      (Test.pair x y (m n w) (H n w)).Holds ((F n).map (algebraMap ℚ K)) := by
  filter_upwards [eventually_mem_reservedPoints a ha F x hx,
    eventually_mem_reservedPoints a ha F y hy] with n hxn hyn
  intro w
  exact hstage n _ (pair_mem_finiteTests _ _ _ x y hxn hyn hxy w)

/-- Every actual listed word eventually has nonzero tangent at each fixed
retained point. -/
theorem eventually_tangent_tests
    (a : ℕ → K) (ha : Function.Surjective a) (F : ℕ → ℚ[X])
    (W : ℕ → Type*) [∀ n, Fintype (W n)]
    (m : ∀ n, W n → ℕ) (H : ∀ n, W n → K[X])
    (hstage : ∀ n t, t ∈ finiteTests (reservedPoints a F n) (m n) (H n) →
      t.Holds ((F n).map (algebraMap ℚ K)))
    (x : K) (hx : ∀ h, (F h).eval₂ (algebraMap ℚ K) x ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∀ w : W n,
      (Test.tangent x (m n w) (H n w)).Holds ((F n).map (algebraMap ℚ K)) := by
  filter_upwards [eventually_mem_reservedPoints a ha F x hx] with n hxn
  intro w
  exact hstage n _ (tangent_mem_finiteTests _ _ _ x hxn w)

end Reservations

end UnconditionalCounterexample.GeometricReservations
