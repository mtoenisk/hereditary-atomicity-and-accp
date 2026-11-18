import HereditaryAtomicity.DVRBase.ModelNearJunk
import HereditaryAtomicity.DVRBase.ModelObstructionNumerics
import HereditaryAtomicity.DVRBase.GaussBounds

/-!
# The actual final coefficient contradiction in Theorem F

A least coefficient of ψ gives a literal nonjunk term of a=Zₙψ. Matching
with Y_D b supplies the coefficient of a literal source term Y_L b at the
forbidden transformed exponent and coefficient order.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}

/-- The partition L ⊔ D of the tail converts the actual translated exponent
of a matched b term to the obstruction exponent of the corresponding a term. -/
theorem obstructionExponent_of_partition (γ : Fin n → ℤ) (L D : Finset (Fin n))
    (hdisj : Disjoint L D)
    (hpartition : L ∪ D = Finset.univ.filter (fun l => 0 < l.val)) :
    obstructionExponent ((fun _ => -1) + γ) L = maskExponent L + (-maskExponent D + γ) := by
  classical
  funext i
  have hmem := congrArg (fun X : Finset (Fin n) => i ∈ X) hpartition
  have htail : (i ∈ L ∨ i ∈ D) ↔ 0 < i.val := by
    simpa only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] using hmem.to_iff
  have hnot : ¬(i ∈ L ∧ i ∈ D) := fun h => Finset.disjoint_left.mp hdisj h.1 h.2
  simp only [obstructionExponent, Pi.add_apply, Pi.neg_apply, maskExponent]
  split_ifs <;> simp_all
  omega

/-- The actual least-term matching of F Step 3 contradicts the numerical
obstruction. The matched coefficients need only have equal order; equality
of their field values is neither assumed nor used. -/
theorem model_obstruction_of_least_term_matching
    (v : Valuation K ℝ≥0) (π : K) (hπ0 : π ≠ 0)
    (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (hn : 0 < n) (Λ L D : Finset (Fin n))
    (hdisj : Disjoint L D)
    (hpartition : L ∪ D = Finset.univ.filter (fun l => 0 < l.val))
    (hbudget : 2 * (∑ i ∈ L, P.weights i) ≤ remainingValue P.weights P.kappa 1)
    (a ψ b : Laurent K n) (haeq : a = terminalMonomial π P.kappa * ψ)
    (hψ : ψ ≠ 0) (ha : a ∈ modelSourceRing v π P Λ)
    (hanj : ∀ β, a.coeff β ≠ 0 →
      AddMonoidAlgebra.single β (a.coeff β) ∉ modelJunk v π P)
    (hLb : maskMonomial L * b ∈ modelSourceRing v π P Λ)
    (hmatch : ∀ γ,
      (ψ.coeff γ ≠ 0 ∧ termOrder v P.weights γ (ψ.coeff γ) = laurentOrder v P.weights ψ) ↔
      ((maskMonomial D * b).coeff γ ≠ 0 ∧
        termOrder v P.weights γ ((maskMonomial D * b).coeff γ) = laurentOrder v P.weights ψ)) :
    False := by
  classical
  obtain ⟨γ, hγ, hγorder⟩ := exists_termOrder_eq_laurentOrder v P.weights ψ hψ
  obtain ⟨hDbγ, hDborder⟩ := (hmatch γ).mp ⟨hγ, hγorder⟩
  let β : Fin n → ℤ := (fun _ => -1) + γ
  let δ : Fin n → ℤ := -maskExponent D + γ
  have hac : a.coeff β = π ^ P.kappa * ψ.coeff γ := by
    rw [haeq]
    exact AddMonoidAlgebra.coeff_single_mul_add ψ (π ^ P.kappa) (fun _ => -1) γ
  have haβ : a.coeff β ≠ 0 := by
    rw [hac]
    exact mul_ne_zero (pow_ne_zero _ hπ0) hγ
  have hbc : (maskMonomial D * b).coeff γ = b.coeff δ := by
    simp [maskMonomial, δ]
  have hbδ : b.coeff δ ≠ 0 := hbc ▸ hDbγ
  have horders : realValuationOrder v (b.coeff δ) = realValuationOrder v (ψ.coeff γ) := by
    rw [hbc] at hDborder
    unfold termOrder at hDborder hγorder
    linarith
  have haorder : realValuationOrder v (a.coeff β) =
      (P.kappa : ℝ) + realValuationOrder v (ψ.coeff γ) := by
    rw [hac, realValuationOrder_mul v (pow_ne_zero _ hπ0) hγ,
      realValuationOrder_pow, hπ, mul_one]
  have horder : realValuationOrder v (b.coeff δ) =
      realValuationOrder v (a.coeff β) - P.kappa := by
    rw [haorder, horders]
    ring
  have hterm : AddMonoidAlgebra.single (maskExponent L + δ) (b.coeff δ) ∈
      modelSourceRing v π P Λ := by
    have hs : maskMonomial L * b ∈ (sourceClass P Λ).supported v := by
      rw [← modelSourceRing_eq_supported v π hπ0 hπ P Λ]
      exact hLb
    have ht := (MonomialClass.mem_supported_iff_single v _ _).mp hs (maskExponent L + δ)
    have hcoeff : (maskMonomial L * b).coeff (maskExponent L + δ) = b.coeff δ := by
      simp [maskMonomial]
    rw [hcoeff, ← modelSourceRing_eq_supported v π hπ0 hπ P Λ] at ht
    exact ht
  have hexp : obstructionExponent β L = maskExponent L + δ :=
    obstructionExponent_of_partition γ L D hdisj hpartition
  rw [← hexp] at hterm
  exact single_not_mem_modelSourceRing_of_obstruction_order v π hπ0 hπ P Λ β L
    (realValuationOrder v (a.coeff β)) hn
    (modelSourceRing_nonjunk_term v π hπ0 hπ P Λ ha β haβ (hanj β haβ)).2.1
    (modelSourceRing_nonjunk_term_not_dead v π hπ0 hπ P Λ ha β haβ (hanj β haβ))
    hbudget (b.coeff δ) hbδ horder hterm

end HereditaryAtomicity.DVRBase
