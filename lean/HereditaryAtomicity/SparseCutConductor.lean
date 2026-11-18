import HereditaryAtomicity.SparseCutLocality
import HereditaryAtomicity.ConductorBranches

/-!
# Actual DVR and field conductor cuts in finite-branch Prüfer domains

The exponent in the given conductor hypothesis is retained exactly. The common
ideal in the conclusion is the literal product of that principal ideal with the
Jacobson radical of the overring.
-/

open scoped NNReal
noncomputable section
namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- A nonzero Jacobson element is positive at every actual maximal branch. -/
theorem pruefer_jacobson_real_order_pos
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    {x : B} (hx0 : x ≠ 0) (hx : x ∈ Ideal.jacobson (⊥ : Ideal B))
    (P : MaximalSpectrum B) :
    0 < realValuationOrder (prueferMaximalRealValuation B hB hfield P) x := by
  apply (realValuationOrder_pos_iff _ (Subtype.coe_ne_coe.mpr hx0)).mpr
  apply (prueferMaximalRealValuation_lt_one_iff B hB hfield P x).mpr
  exact (show Ideal.jacobson (⊥ : Ideal B) ≤ P.asIdeal from sInf_le ⟨bot_le, P.isMaximal⟩) hx

/-- Actual maximal branches normalized at a specified nonzero Jacobson element. -/
def normalizedPrueferValuation
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (π : B) (hπ0 : π ≠ 0) (hπJ : π ∈ Ideal.jacobson (⊥ : Ideal B))
    (P : MaximalSpectrum B) : Valuation K ℝ≥0 :=
  normalizeRealValuation (prueferMaximalRealValuation B hB hfield P) π
    (pruefer_jacobson_real_order_pos B hB hfield hπ0 hπJ P)

private theorem exists_pruefer_coefficient_cut
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    [Finite (MaximalSpectrum B)] (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (C A : Subring B) [IsLocalRing A] (hAC : A ≤ C)
    (π : B) (hπ0 : π ≠ 0) (hπJ : π ∈ Ideal.jacobson (⊥ : Ideal B))
    (hcoeff : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ∀ P,
      realValuationOrder (normalizedPrueferValuation B hB hfield π hπ0 hπJ P)
        ((a : B) : K) = n)
    (c : ℕ) (hc : 0 < c) (hconductor : ∀ b : B, π^c * b ∈ C)
    (hbranch : ∀ P : MaximalSpectrum B, ∀ ε : ℝ, 0 < ε →
      ∃ x : B, x ∈ C ∧ x ≠ 0 ∧ x ∈ Ideal.jacobson (⊥ : Ideal B) ∧
        realValuationOrder (prueferMaximalRealValuation B hB hfield P) x < ε) :
    ∃ S : Subring B, S ≤ C ∧ IsLocalRing S ∧ ¬ Factorization.IsAtomicDomain S ∧
      ((Ideal.span ({π^c} : Set B) * Ideal.jacobson (⊥ : Ideal B) : Ideal B) : Set B) ⊆ S ∧
      Ideal.span ({π^c} : Set B) * Ideal.jacobson (⊥ : Ideal B) ≠ ⊥ ∧ IsFractionRing S K := by
  classical
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let v := prueferMaximalRealValuation B hB hfield
  let w := normalizedPrueferValuation B hB hfield π hπ0 hπJ
  have hw : ∀ P x, w P x ≤ 1 ↔ v P x ≤ 1 :=
    fun P x => normalizeRealValuation_le_one_iff _ _ _ _
  have hwmem : ∀ x : K, x ∈ B ↔ ∀ P, w P x ≤ 1 := by
    intro x
    simp only [hw, v, ← mem_pruefer_iff_realValuations_le_one B hB hfield x]
  have hwnonneg : ∀ x : B, x ≠ 0 → ∀ P, 0 ≤ realValuationOrder (w P) x := by
    intro x hx P
    exact (realValuationOrder_nonneg_iff _ (Subtype.coe_ne_coe.mpr hx)).mpr ((hwmem _).mp x.property P)
  have hnorm : ∀ P, realValuationOrder (w P) π = 1 := fun P =>
    realValuationOrder_normalize_self _ _ _
  let I := realValuationTail w B hwnonneg c
  have hIC : (I : Set B) ⊆ C := by
    intro x hx
    rcases hx with hx | hx
    · simp [hx]
    · have hx0 : x ≠ 0 := by
        intro hz
        have hh := hx (Classical.choice (inferInstance : Nonempty (MaximalSpectrum B)))
        simp only [hz, Subring.coe_zero, realValuationOrder_zero] at hh
        exact (not_lt_of_ge (Nat.cast_nonneg c)) hh
      have hq0 : (x : K) / (π : K)^c ≠ 0 :=
        div_ne_zero (Subtype.coe_ne_coe.mpr hx0) (pow_ne_zero _ (Subtype.coe_ne_coe.mpr hπ0))
      have hqB : (x : K) / (π : K)^c ∈ B := by
        apply (hwmem _).mpr
        intro P
        apply (realValuationOrder_nonneg_iff _ hq0).mp
        rw [realValuationOrder_div _ (Subtype.coe_ne_coe.mpr hx0)
          (pow_ne_zero _ (Subtype.coe_ne_coe.mpr hπ0)), realValuationOrder_pow, hnorm P, mul_one]
        exact (sub_pos.mpr (hx P)).le
      have h := hconductor ⟨_, hqB⟩
      have heq : π ^ c * (⟨(x : K) / (π : K)^c, hqB⟩ : B) = x := by
        apply Subtype.ext
        exact mul_div_cancel₀ (x : K) (pow_ne_zero _ (Subtype.coe_ne_coe.mpr hπ0))
      exact heq ▸ h
  have hsmall : ∀ P : MaximalSpectrum B, ∀ ε : ℝ, 0 < ε →
      ∃ x : B, x ∈ C ∧ x ≠ 0 ∧ (∀ Q, 0 < realValuationOrder (w Q) x) ∧
        realValuationOrder (w P) x < ε := by
    intro P ε hε
    have hπpos := pruefer_jacobson_real_order_pos B hB hfield hπ0 hπJ P
    obtain ⟨x, hxC, hx0, hxJ, hx⟩ := hbranch P
      (ε * realValuationOrder (v P) π) (mul_pos hε hπpos)
    refine ⟨x, hxC, hx0, ?_, ?_⟩
    · intro Q
      exact (realValuationOrder_normalize_pos_iff _ _ _ _).mpr
        (pruefer_jacobson_real_order_pos B hB hfield hx0 hxJ Q)
    · change realValuationOrder (normalizeRealValuation (v P) π hπpos) x < ε
      rw [normalizeRealValuation, realValuationOrder_scale, ← div_eq_inv_mul]
      exact (div_lt_iff₀ hπpos).mpr hx
  obtain ⟨S, hSC, hSloc, hSnot, hIS, _, hSfrac⟩ :=
    exists_local_nonatomic_cut_of_branchwise_coinitial w B hwnonneg
      (fun x hx => (hwmem x).mpr hx) C A hAC hcoeff π hπ0 hnorm c hc hIC hsmall
  have hJI : Ideal.span ({π ^ c} : Set B) * Ideal.jacobson (⊥ : Ideal B) ≤ I := by
    apply Ideal.mul_le.mpr
    intro x hx y hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hx
    by_cases hzy : z*y = 0
    · left
      simpa only [mul_assoc, mul_zero] using congrArg (π^c * ·) hzy
    · right
      intro P
      have hzyJ : z*y ∈ Ideal.jacobson (⊥ : Ideal B) := Ideal.mul_mem_left _ z hy
      have hzypos : 0 < realValuationOrder (w P) (z*y) :=
        (realValuationOrder_normalize_pos_iff _ _ _ _).mpr
          (pruefer_jacobson_real_order_pos B hB hfield hzy hzyJ P)
      change (c : ℝ) < realValuationOrder (w P) (((π : K)^c*(z:K))*(y:K))
      have hzyK : (z : K) * (y : K) ≠ 0 := Subtype.coe_ne_coe.mpr hzy
      rw [mul_assoc, realValuationOrder_mul _
        (pow_ne_zero _ (Subtype.coe_ne_coe.mpr hπ0)) hzyK,
        realValuationOrder_pow, hnorm P, mul_one]
      exact lt_add_of_pos_right _ hzypos
  refine ⟨S, hSC, hSloc, hSnot, fun x hx => hIS (hJI hx), ?_, hSfrac⟩
  intro hz
  have hmem : π^c*π ∈ Ideal.span ({π^c} : Set B) * Ideal.jacobson (⊥ : Ideal B) :=
    Ideal.mul_mem_mul (Ideal.subset_span rfl) hπJ
  exact mul_ne_zero (pow_ne_zero _ hπ0) hπ0 (Ideal.mem_bot.mp (hz ▸ hmem))

/-- The witness over the prescribed coefficient DVR is local and nonatomic, has full
fraction field, and contains the specified conductor power times the Jacobson radical. -/
theorem exists_local_nonatomic_subring_of_dvr_conductor
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    [Finite (MaximalSpectrum B)] (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (C A : Subring B) [IsDiscreteValuationRing A] (hAC : A ≤ C)
    (π : A) (hπ : Irreducible π) (hπJ : (π : B) ∈ Ideal.jacobson (⊥ : Ideal B))
    (c : ℕ) (hc : 0 < c) (hconductor : ∀ b : B, (π : B)^c * b ∈ C)
    (hbranch : ∀ P : MaximalSpectrum B, ∀ ε : ℝ, 0 < ε →
      ∃ x : B, x ∈ C ∧ x ≠ 0 ∧ x ∈ Ideal.jacobson (⊥ : Ideal B) ∧
        realValuationOrder (prueferMaximalRealValuation B hB hfield P) x < ε) :
    ∃ S : Subring B, S ≤ C ∧ IsLocalRing S ∧ ¬ Factorization.IsAtomicDomain S ∧
      ((Ideal.span ({(π : B)^c} : Set B) * Ideal.jacobson (⊥ : Ideal B) : Ideal B) : Set B) ⊆ S ∧
      Ideal.span ({(π : B)^c} : Set B) * Ideal.jacobson (⊥ : Ideal B) ≠ ⊥ ∧ IsFractionRing S K := by
  let w := normalizedPrueferValuation B hB hfield (π : B)
    (Subtype.coe_ne_coe.mpr hπ.ne_zero) hπJ
  apply exists_pruefer_coefficient_cut B hB hfield C A hAC (π : B)
    (Subtype.coe_ne_coe.mpr hπ.ne_zero) hπJ _ c hc hconductor hbranch
  intro a ha
  let f : A →+* K := B.subtype.comp A.subtype
  apply normalized_dvr_coefficient_orders f w _ hπ _ ha
  · intro P x
    apply (normalizeRealValuation_le_one_iff _ _ _ _).mpr
    exact (mem_pruefer_iff_realValuations_le_one B hB hfield _).mp (x : B).property P
  · intro P
    exact realValuationOrder_normalize_self _ _ _

/-- The field-coefficient conductor cut, with its fixed literal ideal d·Jac(B). -/
theorem exists_local_nonatomic_subring_of_field_conductor
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    [Finite (MaximalSpectrum B)] (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (C k : Subring B) (hk : IsField k) (hkC : k ≤ C)
    (d : B) (hd0 : d ≠ 0) (hdJ : d ∈ Ideal.jacobson (⊥ : Ideal B))
    (hconductor : ∀ b : B, d*b ∈ C)
    (hbranch : ∀ P : MaximalSpectrum B, ∀ ε : ℝ, 0 < ε →
      ∃ x : B, x ∈ C ∧ x ≠ 0 ∧ x ∈ Ideal.jacobson (⊥ : Ideal B) ∧
        realValuationOrder (prueferMaximalRealValuation B hB hfield P) x < ε) :
    ∃ S : Subring B, S ≤ C ∧ IsLocalRing S ∧ ¬ Factorization.IsAtomicDomain S ∧
      ((Ideal.span ({d} : Set B) * Ideal.jacobson (⊥ : Ideal B) : Ideal B) : Set B) ⊆ S ∧
      Ideal.span ({d} : Set B) * Ideal.jacobson (⊥ : Ideal B) ≠ ⊥ ∧ IsFractionRing S K := by
  let : Field k := hk.toField
  let w := normalizedPrueferValuation B hB hfield d hd0 hdJ
  have hcoeff : ∀ a : k, a ≠ 0 → ∃ n : ℕ, ∀ P,
      realValuationOrder (w P) ((a : B) : K) = n := by
    intro a ha
    refine ⟨0, fun P => ?_⟩
    let f : k →+* K := B.subtype.comp k.subtype
    have hv : ∀ x : k, w P (f x) ≤ 1 := by
      intro x
      apply (normalizeRealValuation_le_one_iff _ _ _ _).mpr
      exact (mem_pruefer_iff_realValuations_le_one B hB hfield _).mp (x : B).property P
    simpa only [Nat.cast_zero, f, RingHom.comp_apply, Subring.subtype_apply] using
      field_coefficient_order f (w P) hv ha
  simpa only [pow_one] using exists_pruefer_coefficient_cut B hB hfield C k hkC d hd0 hdJ
    hcoeff 1 zero_lt_one (by simpa only [pow_one] using hconductor) hbranch

end HereditaryAtomicity
