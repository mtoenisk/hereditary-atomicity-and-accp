import HereditaryAtomicity.DVRBase.ModelSource

/-!
# The final numerical contradiction in the finite model

Replacing a term ℓ by ℓ Y_L² / Z₁ subtracts κ from the coefficient order. The exponent
increases by twice the indicator of L and once at the first variable. The zero-level
coefficient has negative order. At positive levels the bound 2 u_L ≤ s₁ prevents the
increase needed for membership in S₀.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal

variable {n : ℕ}

/-- The actual exponent of ℓ Y_L² / Z₁, using zero-based coordinates. -/
def obstructionExponent (β : Fin n → ℤ) (L : Finset (Fin n)) (i : Fin n) : ℤ :=
  β i + (if i ∈ L then 2 else 0) + (if i.val = 0 then 1 else 0)

theorem obstructionExponent_nonneg (β : Fin n → ℤ) (L : Finset (Fin n))
    (hβ : ∀ i, 0 ≤ β i) : ∀ i, 0 ≤ obstructionExponent β L i := by
  intro i
  have := hβ i
  unfold obstructionExponent
  split_ifs <;> omega

/-- Excluding the first variable from L leaves exactly one added first exponent. -/
theorem obstructionExponent_first (β : Fin n → ℤ) (L : Finset (Fin n))
    (hn : 0 < n) (hL : (⟨0, hn⟩ : Fin n) ∉ L) :
    obstructionExponent β L ⟨0, hn⟩ = β ⟨0, hn⟩ + 1 := by
  simp [obstructionExponent, hL]

theorem prefixSum_selected (u : Fin n → ℝ) (L : Finset (Fin n)) (k : ℕ) :
    prefixSum (fun i => if i ∈ L then u i else 0) k =
      ∑ i ∈ L.filter (fun i => i.val < k), u i := by
  classical
  unfold prefixSum
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp [and_comm]

theorem prefixSum_first (u : Fin n → ℝ) (hn : 0 < n) {k : ℕ} (hk : 0 < k) :
    prefixSum (fun i => if i.val = 0 then u i else 0) k = u ⟨0, hn⟩ := by
  classical
  unfold prefixSum
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp
  · intro i _ hi
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [hi0]
  · intro hi
    exact (hi (by simp [hk])).elim

/-- At each positive cut, the transformed partial order has the exact shift
−s₁ + 2 u_{L before the cut}. -/
theorem partialValue_obstructionExponent (u : Fin n → ℝ) (κ e : ℝ)
    (β : Fin n → ℤ) (L : Finset (Fin n)) (hn : 0 < n)
    {k : ℕ} (hk : 0 < k) :
    partialValue u (e - κ) (obstructionExponent β L) k =
      partialValue u e β k - (κ - u ⟨0, hn⟩) +
        2 * ∑ i ∈ L.filter (fun i => i.val < k), u i := by
  have heq : (fun i => (obstructionExponent β L i : ℝ) * u i) =
      (fun i => (β i : ℝ) * u i +
        ((if i ∈ L then u i else 0) + (if i ∈ L then u i else 0)) +
        (if i.val = 0 then u i else 0)) := by
    funext i
    simp only [obstructionExponent, Int.cast_add]
    split_ifs <;> push_cast <;> ring
  simp only [partialValue, heq, prefixSum_add, prefixSum_selected, prefixSum_first u hn hk]
  ring

/-- The selected prefix has no larger weight than the full selected set. -/
theorem selectedPrefixWeight_le (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i)
    (L : Finset (Fin n)) (k : ℕ) :
    (∑ i ∈ L.filter (fun i => i.val < k), u i) ≤ ∑ i ∈ L, u i := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => hu i)

/-- The F Step 3 budget makes every positive partial order weakly decrease. -/
theorem partialValue_obstructionExponent_le (u : Fin n → ℝ) (κ e : ℝ)
    (hu : ∀ i, 0 ≤ u i) (β : Fin n → ℤ) (L : Finset (Fin n)) (hn : 0 < n)
    (hbudget : 2 * (∑ i ∈ L, u i) ≤ κ - u ⟨0, hn⟩)
    {k : ℕ} (hk : 0 < k) :
    partialValue u (e - κ) (obstructionExponent β L) k ≤ partialValue u e β k := by
  rw [partialValue_obstructionExponent u κ e β L hn hk]
  have hprefix := selectedPrefixWeight_le u hu L k
  linarith

/-- The first endpoint order is κ minus the first variable weight. -/
theorem remainingValue_one (u : Fin n → ℝ) (κ : ℝ) (hn : 0 < n) :
    remainingValue u κ 1 = κ - u ⟨0, hn⟩ := by
  simpa using (remainingValue_succ u κ (k := 0) hn)

/-- Nondeadness at cut zero makes the transformed coefficient order negative. -/
theorem ModelParameters.obstruction_coefficient_neg (P : ModelParameters n)
    (β : Fin n → ℤ) (e : ℝ)
    (hdead : ∀ k ≤ n, partialValue P.weights e β k <
      P.thresholds k + remainingValue P.weights P.kappa k) :
    e - P.kappa < 0 := by
  have h := hdead 0 (Nat.zero_le _)
  simp only [partialValue_zero, P.threshold_zero, remainingValue_zero, zero_add] at h
  exact sub_neg.mpr h

/-- No cut becomes dead after the F Step 3 transform. -/
theorem ModelParameters.obstruction_not_dead (P : ModelParameters n)
    (β : Fin n → ℤ) (L : Finset (Fin n)) (e : ℝ) (hn : 0 < n)
    (hdead : ∀ k ≤ n, partialValue P.weights e β k <
      P.thresholds k + remainingValue P.weights P.kappa k)
    (hbudget : 2 * (∑ i ∈ L, P.weights i) ≤ remainingValue P.weights P.kappa 1) :
    ∀ k ≤ n, partialValue P.weights (e - P.kappa) (obstructionExponent β L) k <
      P.thresholds k + remainingValue P.weights P.kappa k := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    have h := hdead 0 (Nat.zero_le _)
    have hκ : 0 < (P.kappa : ℝ) := by exact_mod_cast P.kappa_pos
    simp only [partialValue_zero] at h ⊢
    linarith
  · have hbudget' : 2 * (∑ i ∈ L, P.weights i) ≤
        (P.kappa : ℝ) - P.weights ⟨0, hn⟩ := by
      rwa [remainingValue_one P.weights P.kappa hn] at hbudget
    exact (partialValue_obstructionExponent_le P.weights P.kappa e
      (fun i => (P.weights_pos i).le) β L hn hbudget' (Nat.pos_of_ne_zero hk0)).trans_lt
        (hdead k hk)

/-- The final numerical contradiction: the transformed exponent/order pair
belongs to neither the polynomial class nor the endpoint-ideal class of S₀.
The shape hypotheses L ⊆ Λ and first ∉ L are not needed after the budget is known. -/
theorem not_sourceClass_obstructionExponent (P : ModelParameters n)
    (Λ : Finset (Fin n)) (β : Fin n → ℤ) (L : Finset (Fin n)) (e : ℝ)
    (hn : 0 < n) (hβ : ∀ i, 0 ≤ β i)
    (hdead : ∀ k ≤ n, partialValue P.weights e β k <
      P.thresholds k + remainingValue P.weights P.kappa k)
    (hbudget : 2 * (∑ i ∈ L, P.weights i) ≤ remainingValue P.weights P.kappa 1) :
    ¬ (sourceClass P Λ).contains (obstructionExponent β L) (e - P.kappa) := by
  have hneg := P.obstruction_coefficient_neg β e hdead
  have hnonneg := obstructionExponent_nonneg β L hβ
  have hnotdead := P.obstruction_not_dead β L e hn hdead hbudget
  intro h
  rcases h with hpoly | hjunk
  · exact hneg.not_ge hpoly.1
  · change MeetsLevel P.weights P.kappa P.thresholds
        (-(fun _ : Fin n => (-1 : ℤ)) + obstructionExponent β L)
        ((e - P.kappa) - P.kappa) at hjunk
    have he : -(fun _ : Fin n => (-1 : ℤ)) + obstructionExponent β L =
        (fun i => obstructionExponent β L i + 1) := by
      funext i
      simp [add_comm]
    rw [he, meetsLevel_endpoint_quotient_iff P.weights P.kappa (e - P.kappa)
      P.thresholds (obstructionExponent β L) hnonneg] at hjunk
    obtain ⟨k, hk, hcross⟩ := hjunk
    exact (hnotdead k hk).not_ge hcross

variable {K : Type*} [Field K]

/-- The selected-variable product is the literal indicator monomial. -/
theorem prod_variableMonomial_eq_single (L : Finset (Fin n)) :
    (∏ i ∈ L, (variableMonomial i : Laurent K n)) =
      AddMonoidAlgebra.single (fun i => if i ∈ L then 1 else 0) 1 := by
  classical
  simp only [variableMonomial, AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

/-- Multiplication by Z₁ verifies that the transformed single monomial is
exactly ℓ Y_L² / Z₁, without introducing division on the Laurent ring. -/
theorem endpointMonomial_one_mul_obstruction_single (π : K) (κ : ℕ)
    (hπ0 : π ≠ 0) (β : Fin n → ℤ) (L : Finset (Fin n)) (c : K) :
    endpointMonomial π κ 1 *
        AddMonoidAlgebra.single (obstructionExponent β L) (c / π ^ κ) =
      AddMonoidAlgebra.single β c * (∏ i ∈ L, (variableMonomial i : Laurent K n)) ^ 2 := by
  classical
  have hcoeff : π ^ κ * (c / π ^ κ) = c := by
    field_simp
  rw [prod_variableMonomial_eq_single]
  simp only [endpointMonomial, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single, hcoeff, one_pow, mul_one]
  congr 1
  funext i
  simp only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, obstructionExponent]
  have hfirst : i.val < 1 ↔ i.val = 0 := by omega
  simp only [hfirst]
  split_ifs <;> omega

/-- The contradiction depends on the actual coefficient order, not equality
with the quotient coefficient. This is the interface for coefficient matching. -/
theorem single_not_mem_modelSourceRing_of_obstruction_order
    (v : Valuation K ℝ≥0) (π : K) (hπ0 : π ≠ 0)
    (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ : Finset (Fin n)) (β : Fin n → ℤ) (L : Finset (Fin n)) (e : ℝ)
    (hn : 0 < n) (hβ : ∀ i, 0 ≤ β i)
    (hdead : ∀ k ≤ n, partialValue P.weights e β k <
      P.thresholds k + remainingValue P.weights P.kappa k)
    (hbudget : 2 * (∑ i ∈ L, P.weights i) ≤ remainingValue P.weights P.kappa 1)
    (d : K) (hd : d ≠ 0) (horder : realValuationOrder v d = e - P.kappa) :
    AddMonoidAlgebra.single (obstructionExponent β L) d ∉ modelSourceRing v π P Λ := by
  intro hmem
  have hs : AddMonoidAlgebra.single (obstructionExponent β L) d ∈
      (sourceClass P Λ).supported v := by
    rw [← modelSourceRing_eq_supported v π hπ0 hπ P Λ]
    exact hmem
  have h := ((MonomialClass.single_mem_supported v (sourceClass P Λ) _ d).mp hs).resolve_left hd
  rw [horder] at h
  exact not_sourceClass_obstructionExponent P Λ β L e hn hβ hdead hbudget h

/-- The literal coefficient c/π^κ realizes the required order drop. -/
theorem single_div_not_mem_modelSourceRing_of_not_dead
    (v : Valuation K ℝ≥0) (π : K) (hπ0 : π ≠ 0)
    (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ : Finset (Fin n)) (β : Fin n → ℤ) (L : Finset (Fin n))
    (c : K) (hc : c ≠ 0) (hn : 0 < n) (hβ : ∀ i, 0 ≤ β i)
    (hdead : ∀ k ≤ n, partialValue P.weights (realValuationOrder v c) β k <
      P.thresholds k + remainingValue P.weights P.kappa k)
    (hbudget : 2 * (∑ i ∈ L, P.weights i) ≤ remainingValue P.weights P.kappa 1) :
    AddMonoidAlgebra.single (obstructionExponent β L) (c / π ^ P.kappa) ∉
      modelSourceRing v π P Λ := by
  apply single_not_mem_modelSourceRing_of_obstruction_order v π hπ0 hπ P Λ β L
    (realValuationOrder v c) hn hβ hdead hbudget (c / π ^ P.kappa)
    (div_ne_zero hc (pow_ne_zero _ hπ0))
  simp [realValuationOrder_div v hc (pow_ne_zero _ hπ0), realValuationOrder_pow, hπ]

/-- The nonjunk-term hypotheses of F Step 3 supply every nondead cut and the
nonnegative exponent used by the numerical contradiction. -/
theorem modelSourceRing_nonjunk_term_obstruction
    (v : Valuation K ℝ≥0) (π : K) (hπ0 : π ≠ 0)
    (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ : Finset (Fin n)) {f : Laurent K n} (hf : f ∈ modelSourceRing v π P Λ)
    (β : Fin n → ℤ) (hβ : f.coeff β ≠ 0)
    (hj : AddMonoidAlgebra.single β (f.coeff β) ∉ modelJunk v π P)
    (L : Finset (Fin n)) (hn : 0 < n)
    (hbudget : 2 * (∑ i ∈ L, P.weights i) ≤ remainingValue P.weights P.kappa 1) :
    AddMonoidAlgebra.single (obstructionExponent β L) (f.coeff β / π ^ P.kappa) ∉
      modelSourceRing v π P Λ := by
  exact single_div_not_mem_modelSourceRing_of_not_dead v π hπ0 hπ P Λ β L
    (f.coeff β) hβ hn (modelSourceRing_nonjunk_term v π hπ0 hπ P Λ hf β hβ hj).2.1
    (modelSourceRing_nonjunk_term_not_dead v π hπ0 hπ P Λ hf β hβ hj) hbudget

end HereditaryAtomicity.DVRBase
