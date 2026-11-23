import UnconditionalCounterexample.Hierarchy.CompactSelection
import UnconditionalCounterexample.Hierarchy.WeightedPlace

/-! # Realizing integer orders on finitely many compact p-adic fibers -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy

open Polynomial GuardSupport

private theorem positive_lower_norm {X K : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedField K] (f : LocallyConstant X K) (hf : ∀ x, f x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ ‖f x‖ := by
  classical
  by_cases h : Nonempty X
  · obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMinOn ⟨h.some, Set.mem_univ _⟩
      f.continuous.norm.continuousOn
    exact ⟨‖f a‖, norm_pos_iff.mpr (hf a), fun x ↦ ha (Set.mem_univ x)⟩
  · exact ⟨1, one_pos, fun x ↦ (h ⟨x⟩).elim⟩

theorem exists_monic_irreducible_profile {ι : Type*} [Fintype ι] (p : ι → PrimeIndex)
    (hinj : Function.Injective p) (E : ∀ i, Set ℤ_[(p i).val]) (hE : ∀ i, IsCompact (E i))
    (v : ∀ i, LocallyConstant (E i) ℤ) (floor : ℕ) :
    ∃ F : ℚ[X], F.Monic ∧ Irreducible F ∧ floor ≤ F.natDegree ∧
      ∀ i (x : E i), ‖aeval (x.val : ℚ_[(p i).val]) F‖ = ‖((p i).val : ℚ_[(p i).val]) ^ v i x‖ := by
  let f (i : ι) : LocallyConstant (E i) ℚ_[(p i).val] :=
    LocallyConstant.map (fun z : ℤ ↦ ((p i).val : ℚ_[(p i).val]) ^ z) (v i)
  have hf (i : ι) (x : E i) : f i x ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast (p i).property.ne_zero)
  let (i : ι) : CompactSpace (E i) := isCompact_iff_compactSpace.mp (hE i)
  choose ε hε hlower using fun i ↦ positive_lower_norm (f i) (hf i)
  obtain ⟨F, hF, hi, hd, ha⟩ := exists_monic_irreducible_approx p hinj E hE f ε hε floor
  exact ⟨F, hF, hi, hd, fun i x ↦ Padic.norm_eq_of_norm_sub_lt_right
    ((ha i x).trans_le (hlower i x))⟩

namespace Weighted

theorem exists_profile_polynomial {I : Type*} [Fintype I] (F : I → FiberPlace)
    (hi : Function.Injective fun i ↦ (F i).prime) (g : I → LocallyConstant Fiber ℤ) (floor : ℕ) :
    ∃ f : ℚ[X], f.Monic ∧ Irreducible f ∧ floor ≤ f.natDegree ∧
      ∀ i x, (F i).polynomialOrder f x = g i x := by
  let v (i : I) := (g i).comap ⟨(F i).homeomorph.symm, (F i).homeomorph.symm.continuous⟩
  obtain ⟨f, hm, hirr, hd, hv⟩ := exists_monic_irreducible_profile (fun i ↦ (F i).prime)
    hi (fun i ↦ Set.range (F i).emb) (fun i ↦ isCompact_range (F i).continuous) v floor
  refine ⟨f, hm, hirr, hd, fun i x ↦ ?_⟩
  have he := FiberPlace.order_of_norm (hv i ((F i).homeomorph x))
  change (F i).polynomialOrder f x = g i ((F i).homeomorph.symm ((F i).homeomorph x)) at he
  simpa using he

end Weighted
end UnconditionalCounterexample.Hierarchy
