import UnconditionalCounterexample.Hierarchy.PrescribedGenerators
import UnconditionalCounterexample.Hierarchy.CompactSelection

/-! # Realization of all selected slice generators in the rational function field -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Prescribed

open Polynomial GuardSupport DiscreteOrders Set WithZero

variable (m : ℕ → ℕ) (p : PrimeIndex)

private def rowHomeomorph : RowPoint m ≃ₜ range (point m p) :=
  (point_embedding m p).isEmbedding.toHomeomorph

private def target (s : Slot m) : LocallyConstant (range (point m p)) ℚ_[p.val] :=
  LocallyConstant.comap ⟨(rowHomeomorph m p).symm, (rowHomeomorph m p).symm.continuous⟩
    (LocallyConstant.map (fun j => if j = s.2.castSucc then (p.val : ℚ_[p.val]) else 1)
      (LocallyConstant.eval (X := fun i => Fin (m i + 2)) s.1))

private theorem target_point (s : Slot m) (x : RowPoint m) :
    target m p s ((rowHomeomorph m p) x) =
      if x s.1 = s.2.castSucc then (p.val : ℚ_[p.val]) else 1 := by
  change (if ((rowHomeomorph m p).symm (rowHomeomorph m p x)) s.1 = _ then _ else _) = _
  rw [Homeomorph.symm_apply_apply]

private theorem mulValuation_eq_of_norm_eq {q : ℕ} [Fact q.Prime] {x y : ℚ_[q]}
    (h : ‖x‖ = ‖y‖) : Padic.mulValuation x = Padic.mulValuation y := by
  apply le_antisymm <;> apply le_of_not_gt <;> intro he
  · exact (ne_of_lt (Padic.norm_lt_norm_iff_mulValuation_lt.mpr he)) h.symm
  · exact (ne_of_lt (Padic.norm_lt_norm_iff_mulValuation_lt.mpr he)) h

private theorem row_order_of_approx (s : Slot m) (F : ℚ[X])
    (ha : ∀ z : range (point m p),
      ‖aeval (z.val : ℚ_[p.val]) F - target m p s z‖ < ‖(p.val : ℚ_[p.val])‖)
    (x : RowPoint m) :
    order (rowVal m p x) (algebraMap ℚ[X] (RatFunc ℚ) F) = (sliceAt s.1 s.2.castSucc x : ℤ) := by
  let a := (point m p x).val
  have he := ha ((rowHomeomorph m p) x)
  rw [target_point] at he
  change ‖aeval a F - (if x s.1 = _ then _ else _)‖ < _ at he
  change -log (Padic.mulValuation (LocalEvaluation.evalAt a _ (algebraMap ℚ[X] (RatFunc ℚ) F))) = _
  rw [LocalEvaluation.evalAt_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, map_one, div_one]
  by_cases h : x s.1 = s.2.castSucc
  · simp only [h, ↓reduceIte] at he
    rw [mulValuation_eq_of_norm_eq (Padic.norm_eq_of_norm_sub_lt_right he)]
    have hp : Padic.mulValuation (p.val : ℚ_[p.val]) = exp (-1) :=
      EvaluationDVR.valuation_prime p.val (RingHom.id _)
    simp [hp, sliceAt, h]
  · simp only [h, ↓reduceIte] at he
    have hu : ‖aeval a F - 1‖ < ‖(1 : ℚ_[p.val])‖ := by
      rw [norm_one]
      exact he.trans Padic.norm_p_lt_one
    rw [mulValuation_eq_of_norm_eq (Padic.norm_eq_of_norm_sub_lt_right hu)]
    simp [sliceAt, h]

/-- Each selected slot has an actual irreducible polynomial of any requested
minimum degree, with its indicator at the row points and zero order off p. -/
theorem exists_generator (s : Slot m) (floor : ℕ) :
    ∃ F : ℚ[X], Irreducible F ∧ floor ≤ F.natDegree ∧
      (∀ x, order (rowVal m p x) (algebraMap ℚ[X] (RatFunc ℚ) F) =
        (sliceAt s.1 s.2.castSucc x : ℤ)) ∧
      ∀ q : PrimeIndex, q ≠ p → order (guardVal q) (algebraMap ℚ[X] (RatFunc ℚ) F) = 0 := by
  have hp0 : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  obtain ⟨F, _, hF, hdeg, ha⟩ := exists_monic_irreducible_approx_one p (range (point m p))
    (isCompact_range (point_embedding m p).continuous) (target m p s) _ (norm_pos_iff.mpr hp0) floor
  have hF0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hF.ne_zero
  obtain ⟨c, hc, hcRow, hcGuard⟩ := exists_guard_normalization p _ hF0
  refine ⟨C c * F, (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hc).map C)).mpr hF, ?_, ?_, ?_⟩
  · simpa only [natDegree_C_mul hc] using hdeg
  · intro x
    rw [map_mul, RatFunc.algebraMap_C, order_mul _ ((_root_.map_ne_zero RatFunc.C).mpr hc) hF0,
      show order (rowVal m p x) (RatFunc.C c) = 0 from hcRow _, zero_add]
    exact row_order_of_approx m p s F ha x
  · intro q hq
    simpa only [map_mul, RatFunc.algebraMap_C] using hcGuard q hq

/-- One simultaneous family of normalized generators, using the same p-adic
points for every finite slot. -/
def generators : Generators m p where
  poly s := (exists_generator m p s 1).choose
  irreducible s := (exists_generator m p s 1).choose_spec.1
  row_order s := (exists_generator m p s 1).choose_spec.2.2.1
  guard_order s := (exists_generator m p s 1).choose_spec.2.2.2

/-- The rational prime whose factorizations distinguish the two witnesses. -/
abbrev distinguishedPrime : PrimeIndex := ⟨2, Nat.prime_two⟩

/-- Infinitely many binary rows at the prime two. -/
abbrev binaryRing := (generators (fun _ => 0) distinguishedPrime).domain

/-- The rows at the prime two have respective lengths 2, 3, 4, ... . -/
abbrev unboundedRing := (generators id distinguishedPrime).domain

end UnconditionalCounterexample.Hierarchy.Prescribed
