import HereditaryAtomicity.DVRBase.ModelObstruction
import HereditaryAtomicity.DVRBase.SourceLaurent
import HereditaryAtomicity.SparseAtomicFactors

/-!
# Actual source factorization certificates

The reusable finite transfer keeps the original evaluation and the formal
coefficient realization separate. Source-side certificates below use the
literal source ideal and selected source subring.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}

/-- The exact kernel inclusion transfers the finite model obstruction
through two actual evaluation maps. Kernel control is explicit only in this
reusable intermediate theorem. -/
theorem finite_obstruction_of_exact_kernel
    {E A : Type*} [CommRing E] [CommRing A]
    (ev : E →+* A) (formal : E →+* Laurent K n)
    (v : Valuation K ℝ≥0) (π : K) (hπ0 : π ≠ 0)
    (hπ : realValuationOrder v π = 1) (P : ModelParameters n) (hn : 0 < n)
    (Λ : Finset (Fin n))
    (hΛ : 2 * ∑ l ∈ Λ.filter (fun l => 0 < l.val), P.weights l ≤
      remainingValue P.weights P.kappa 1)
    (z : E) (hz : formal z = endpointMonomial π P.kappa 1)
    (hkernel : ∀ x : E, ev x = 0 → ∃ j ∈ modelJunk v π P,
      formal x = endpointMonomial π P.kappa 1 * j)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, formal (f i) ∈ modelSourceRing v π P Λ)
    (hnj : ∀ i ∈ s, formal (f i) ∉ modelJunk v π P) :
    (∏ i ∈ s, ev (f i)) ≠ ev z := by
  intro heq
  have hzero : ev ((∏ i ∈ s, f i) - z) = 0 := by simp [heq]
  obtain ⟨j, hj, he⟩ := hkernel _ hzero
  have hprod : (∏ i ∈ s, formal (f i)) = endpointMonomial π P.kappa 1 * (1 + j) := by
    simp only [map_sub, map_prod, hz] at he
    linear_combination he
  exact model_factorization_obstruction v π hπ0 hπ P hn Λ hΛ s
    (fun i => formal (f i)) hf hnj hj hprod

namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

/-- The actual chain ideal viewed as an additive subgroup of the ambient
field. Taking an ideal image in the field would lose the intended set. -/
def sourceJunk (O : Subring K) : AddSubgroup K :=
  (D.sourceIdeal O).toAddSubgroup.map (D.sourceRing O).subtype.toAddMonoidHom

@[simp] theorem mem_sourceJunk (O : Subring K) (x : K) :
    x ∈ D.sourceJunk O ↔ ∃ q : D.sourceRing O, q ∈ D.sourceIdeal O ∧ (q : K) = x := Iff.rfl

theorem sourceJunk_le_sourceSubring (O : Subring K) (Λ : Set ℕ) :
    D.sourceJunk O ≤ (D.sourceSubring O Λ).toAddSubgroup := by
  rintro x ⟨q, hq, rfl⟩
  exact ⟨q, ideal_subset_idealThickening _ _ hq, rfl⟩

theorem endpoint_mem_sourceJunk (O : Subring K) (m : ℕ) :
    (D.endpoint m : K) ∈ D.sourceJunk O :=
  ⟨D.ringEndpoint O m, endpoint_mem_chainIdeal (D.ringEndpoint O) m, rfl⟩

theorem sourceJunk_order_pos (O : Subring K)
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) {x : K}
    (hx : x ∈ D.sourceJunk O) (hx0 : x ≠ 0) :
    0 < realValuationOrder D.valuation x := by
  obtain ⟨q, hq, rfl⟩ := hx
  exact chainIdeal_order_pos (D.ringEndpoint O) (D.ringRatio O) (D.ring_step O)
    (D.sourceRing O).subtype Subtype.val_injective D.valuation (D.sourceRing_bounded O hO)
    (fun m => lt_of_lt_of_le zero_lt_one (D.endpoint_order_ge_one m)) hq
    (Subtype.coe_ne_coe.mp hx0)

/-- Every nonzero actual junk element admits an arbitrarily fresh selected
ratio factor; the quotient remains in the same junk set and has positive
order. The retained ratio index is used in the semilocal intersection. -/
theorem sourceJunk_fresh_split (O : Subring K)
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ)
    (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    {g : K} (hg : g ∈ D.sourceJunk O) (hg0 : g ≠ 0) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ m ∈ Λ ∧ ∃ q : K,
      q ∈ D.sourceJunk O ∧ g = (D.ratio m : K) * q ∧
      (D.ratio m : K) ∈ D.sourceSubring O Λ ∧
      0 < realValuationOrder D.valuation (D.ratio m : K) ∧
      0 < realValuationOrder D.valuation q := by
  obtain ⟨gR, hgR, rfl⟩ := hg
  obtain ⟨m, hm, hmΛ, q, hq, heq⟩ := exists_fresh_chainIdeal_factor
    (D.ringEndpoint O) (D.ringRatio O) (D.ring_step O) Λ hcofinal hgR N
  have hq0 : (q : K) ≠ 0 := by
    intro hz
    apply hg0
    have h := congrArg (D.sourceRing O).subtype heq
    simpa [hz] using h
  refine ⟨m, hm, hmΛ, q, ⟨q, hq, rfl⟩, congrArg (D.sourceRing O).subtype heq, ?_,
    D.ratio_order_pos m, D.sourceJunk_order_pos O hO ⟨q, hq, rfl⟩ hq0⟩
  exact ⟨D.ringRatio O m,
    base_le_idealThickening _ _ (D.selectedRatio_mem O Λ hmΛ), rfl⟩

/-- The factorization obstruction includes unit factors and the empty finite product. -/
def NoOutsideJunkFactorization (O : Subring K) (Λ : Set ℕ) : Prop :=
  ∀ n : ℕ, ∀ f : Fin n → K,
    (∀ i, f i ∈ D.sourceSubring O Λ) →
    (∀ i, f i ∉ D.sourceJunk O) →
    (∏ i, f i) ≠ (D.endpoint 1 : K)

theorem sourceSubring_bounded (O : Subring K)
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ)
    (x : D.sourceSubring O Λ) : D.valuation (x : K) ≤ 1 :=
  D.sourceRing_bounded O hO ⟨x, D.sourceSubring_le_sourceRing O Λ x.property⟩

theorem sourceSubring_unit_not_mem_junk (O : Subring K)
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ)
    (x : D.sourceSubring O Λ) (hx : IsUnit x) : (x : K) ∉ D.sourceJunk O := by
  intro hj
  have hp := D.sourceJunk_order_pos O hO hj (Subtype.coe_ne_coe.mpr hx.ne_zero)
  exact not_isUnit_of_mapped_order_pos (D.sourceSubring O Λ).subtype D.valuation
    (D.sourceSubring_bounded O hO Λ) hp hx

theorem sourceSubring_irreducible_not_mem_junk (O : Subring K)
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ)
    (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (x : D.sourceSubring O Λ) (hx : Irreducible x) : (x : K) ∉ D.sourceJunk O := by
  intro hj
  obtain ⟨m, _, _, q, hq, heq, hm, hmp, hqp⟩ :=
    D.sourceJunk_fresh_split O hO Λ hcofinal hj (Subtype.coe_ne_coe.mpr hx.ne_zero) 0
  let b : D.sourceSubring O Λ := ⟨D.ratio m, hm⟩
  let c : D.sourceSubring O Λ := ⟨q, D.sourceJunk_le_sourceSubring O Λ hq⟩
  have he : x = b * c := Subtype.ext heq
  rcases hx.isUnit_or_isUnit he with hb | hc
  · exact not_isUnit_of_mapped_order_pos (D.sourceSubring O Λ).subtype D.valuation
      (D.sourceSubring_bounded O hO Λ) (r := b) hmp hb
  · exact not_isUnit_of_mapped_order_pos (D.sourceSubring O Λ).subtype D.valuation
      (D.sourceSubring_bounded O hO Λ) (r := c) hqp hc

/-- Once exact finite transfer excludes outside-junk products, the literal
source subring is not atomic. The unit in an associated atomic product is
retained as an additional factor, so there is no unit-removal assumption. -/
theorem sourceSubring_not_atomic_of_no_factorization (O : Subring K)
    (hO : ∀ a : O, D.valuation (a : K) ≤ 1) (Λ : Set ℕ)
    (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hno : D.NoOutsideJunkFactorization O Λ) :
    ¬ Factorization.IsAtomicDomain (D.sourceSubring O Λ) := by
  classical
  intro hatomic
  let z : D.sourceSubring O Λ := ⟨D.endpoint 1, D.endpoint_mem_sourceSubring O Λ 1⟩
  have hz : z ≠ 0 := by
    intro he
    apply D.endpoint_ne_zero 1
    apply Subtype.ext
    exact congrArg (D.sourceSubring O Λ).subtype he
  obtain ⟨n, f, hf, u, hu⟩ := exists_fin_atomic_factorization hatomic z hz
  let g : Fin (n + 1) → D.sourceSubring O Λ := Fin.cons (u : D.sourceSubring O Λ) f
  have hprod : (∏ i, g i) = z := by
    simpa [g, Fin.prod_univ_succ, mul_comm] using hu
  apply hno (n + 1) (fun i => (g i : K)) (fun i => (g i).property)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact D.sourceSubring_unit_not_mem_junk O hO Λ (u : D.sourceSubring O Λ) u.isUnit
    · exact D.sourceSubring_irreducible_not_mem_junk O hO Λ hcofinal (f j) (hf j)
  · change (∏ i, (g i : K)) = (z : K)
    exact_mod_cast hprod

end SourceBlockData
end HereditaryAtomicity.DVRBase
