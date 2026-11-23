import UnconditionalCounterexample.Hierarchy.PrescribedGenerators
import UnconditionalCounterexample.Hierarchy.PoleUnits

/-!
# Normalized row profiles of the actual pole units

The scalar in a Laurent word has the same order everywhere over the
distinguished rational prime. Grouping the remaining finitely many terms
by row gives an integral sum of single-coordinate functions.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Prescribed

open GuardSupport DiscreteOrders

variable {m : ℕ → ℕ} {p : PrimeIndex}

/-- A nonnegative integer combination of finitely many slices, with a
constant term and signed coefficients, has a normalized profile. -/
theorem Profile.exists_of_slice_sum {ι : Type*} (s : Finset ι) (c : ℤ)
    (row : ι → ℕ) (col : (k : ι) → Fin (m (row k) + 2)) (w : ι → ℤ)
    (hn : ∀ x : RowPoint m, 0 ≤ c + ∑ k ∈ s, w k * sliceAt (row k) (col k) x) :
    ∃ P : Profile m, ∀ x, (P.eval x : ℤ) = c + ∑ k ∈ s, w k * sliceAt (row k) (col k) x := by
  classical
  let rows := s.image row
  let v (i : ℕ) (j : Fin (m i + 2)) : ℤ := ∑ k ∈ s,
    if row k = i then w k * sliceAt (row k) (col k) (Function.update (fun _ => 0) i j) else 0
  have group (x : RowPoint m) :
      ∑ i ∈ rows, v i (x i) = ∑ k ∈ s, w k * sliceAt (row k) (col k) x := by
    unfold v
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : row k ∈ rows := Finset.mem_image_of_mem row hk
    rw [Finset.sum_eq_single_of_mem (row k) hk']
    · simp [sliceAt]
    · intro i _ hi
      simp [Ne.symm hi]
  obtain ⟨P, hP⟩ := Profile.exists_of_integer_rows rows c v fun x => group x ▸ hn x
  exact ⟨P, fun x => (hP x).trans (congrArg (c + ·) (group x))⟩

private theorem scalar_order_same (x y : RowPoint m) (q : ℚ) :
    order (rowVal m p x) (RatFunc.C q) = order (rowVal m p y) (RatFunc.C q) := by
  rw [show RatFunc.C q = (q : RatFunc ℚ) from map_ratCast RatFunc.C q]
  change -WithZero.log (Padic.mulValuation (EvaluationDVR.evaluationHom _ _ _ (q : RatFunc ℚ))) =
    -WithZero.log (Padic.mulValuation (EvaluationDVR.evaluationHom _ _ _ (q : RatFunc ℚ)))
  simp only [map_ratCast]

namespace Generators

variable (G : Generators m p)

/-- A pole-algebra unit lying in the actual intersection has a nonnegative
normalized profile on the whole distinguished fiber. -/
theorem profile_exists (a : G.domain) (hu : IsUnit (ringSubtype m p G.poles a)) :
    ∃ Q : Profile m, ∀ x, (Q.eval x : ℤ) = order (rowVal m p x) (a : RatFunc ℚ) := by
  classical
  obtain ⟨c, _, e, he⟩ := PoleUnits.exists_orders G.poly G.irreducible _ hu
  let x0 : RowPoint m := fun _ => 0
  have heq (x : RowPoint m) :
      order (rowVal m p x) (a : RatFunc ℚ) = order (rowVal m p x0) (RatFunc.C c) +
        ∑ k ∈ e.support, e k * (sliceAt k.1 k.2.castSucc x : ℤ) := by
    have hcoe : ((ringSubtype m p G.poles a) : RatFunc ℚ) = (a : RatFunc ℚ) := rfl
    simpa only [hcoe, PoleUnits.raw, G.row_order, scalar_order_same (p := p) x x0 c] using he (rowVal m p x)
  have ha : (a : RatFunc ℚ) ≠ 0 := fun hz => hu.ne_zero (Subtype.ext hz)
  have hn (x : RowPoint m) := (order_nonneg_iff (rowVal m p x) ha).mpr
    (((mem_ring_iff ..).mp a.property).2.1 x)
  obtain ⟨Q, hQ⟩ := Profile.exists_of_slice_sum e.support _ (fun k => k.1)
    (fun k => k.2.castSucc) e fun x => (heq x) ▸ hn x
  exact ⟨Q, fun x => (hQ x).trans (heq x).symm⟩

theorem natProfile_exists (a : G.domain) (hu : IsUnit (ringSubtype m p G.poles a)) :
    ∃ Q : Profile m, ∀ x, Q.eval x = natOrder (rowVal m p x) (a : RatFunc ℚ) := by
  obtain ⟨Q, hQ⟩ := G.profile_exists a hu
  exact ⟨Q, fun x => by rw [natOrder, ← hQ]; simp⟩

/-- For a pole unit in the intersection, zero orders on the distinguished
fiber and on every other guard make its inverse integral everywhere. -/
theorem unit_of_orders_zero (a : G.domain) (hu : IsUnit (ringSubtype m p G.poles a))
    (hr : ∀ x, order (rowVal m p x) (a : RatFunc ℚ) = 0)
    (hg : ∀ q, q ≠ p → order (guardVal q) (a : RatFunc ℚ) = 0) : IsUnit a := by
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hab : (a : RatFunc ℚ) * (b : RatFunc ℚ) = 1 := congrArg Subtype.val hb
  have ha := left_ne_zero_of_mul_eq_one hab
  have hinv := eq_inv_of_mul_eq_one_right hab
  have hmem : (b : RatFunc ℚ) ∈ G.domain := by
    refine (mem_ring_iff ..).mpr ⟨b.property, ?_, ?_⟩
    · intro x
      rw [hinv, map_inv₀, (order_eq_zero_iff _ ha).mp (hr x), inv_one]
    · intro q hq
      rw [hinv, map_inv₀, (order_eq_zero_iff _ ha).mp (hg q hq), inv_one]
  exact isUnit_iff_exists_inv.mpr ⟨⟨b, hmem⟩, Subtype.ext hab⟩

end Generators
end UnconditionalCounterexample.Hierarchy.Prescribed
