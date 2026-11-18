import HereditaryAtomicity.ValuationApproximation
import HereditaryAtomicity.JacobsonUnits
import HereditaryAtomicity.OutsideDiscrete
import HereditaryAtomicity.OutsideFinite
import HereditaryAtomicity.FieldValuations
import HereditaryAtomicity.ValuationRank
import Mathlib.RingTheory.KrullDimension.PID

/-!
# Finite outside approximation by actual ambient units

Weak approximation first realizes a uniformizer value at one outside DVR and
value one at the other prescribed outside rings. Jacobson-unit realization
returns that finite pattern to the source unit group. Rings containing the
source already see every source unit as a unit.
-/

namespace HereditaryAtomicity

variable {K : Type*} [Field K]

private theorem outside_ne_top {D : Subring K} {V : ValuationSubring K}
    (hV : ¬ D ≤ V.toSubring) : V ≠ ⊤ := by
  intro h
  apply hV
  rw [h]
  exact le_top

private theorem approximation_of_dvr_and_unit_realization (D : Subring K)
    (hdvr : ∀ V : ValuationSubring K, ¬ D ≤ V.toSubring → IsDiscreteValuationRing V)
    (hrealize : ∀ s : Finset (ValuationSubring K),
      (∀ V ∈ s, ¬ D ≤ V.toSubring) → ∀ x : K, x ≠ 0 →
      ∃ u : Dˣ, ∀ V ∈ s, V.valuation ((u : D) : K) = V.valuation x) :
    HasFiniteOutsideUnitApproximation D := by
  classical
  intro A hA T hAT
  let s := insert A (T.filter fun B => ¬ D ≤ B.toSubring)
  have hout : ∀ B ∈ s, ¬ D ≤ B.toSubring := by
    intro B hB
    rcases Finset.mem_insert.mp hB with hBA | hB
    · exact hBA ▸ hA
    · exact (Finset.mem_filter.mp hB).2
  let : IsDiscreteValuationRing A := hdvr A hA
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hp0 : (p : K) ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
  let val (B : s) := B.val.valuation
  let (B : s) : (val B).RankOne := by
    let : IsDiscreteValuationRing B.val := hdvr B (hout B B.property)
    exact Classical.choice (valuationSubring_nonempty_rankOne B.val
      (outside_ne_top (hout B B.property)))
  have hdistinct : Function.Injective fun B : s => (val B).valuationSubring := by
    intro B C h
    apply Subtype.ext
    simpa only [val, ValuationSubring.valuationSubring_valuation] using h
  let target (B : s) : K := if B.val = A then p else 1
  have ht0 : ∀ B : s, target B ≠ 0 := by
    intro B
    dsimp [target]
    split_ifs
    · exact hp0
    · exact one_ne_zero
  obtain ⟨x, hx0, hx⟩ := ValuationApproximation.exists_same_values_rankOne val
    hdistinct target ht0
  obtain ⟨u, hu⟩ := hrealize s hout x hx0
  have hAmem : A ∈ s := Finset.mem_insert_self ..
  have huA : A.valuation ((u : D) : K) = A.valuation (p : K) := by
    calc
      _ = A.valuation x := hu A hAmem
      _ = A.valuation (target ⟨A, hAmem⟩) := hx ⟨A, hAmem⟩
      _ = _ := by simp [target]
  have hule : A.valuation ((u : D) : K) ≤ 1 := by
    rw [huA]
    exact A.valuation_le_one p
  let uA : A := ⟨((u : D) : K), (A.valuation_le_one_iff _).mp hule⟩
  have hassoc : Associated p uA := by
    obtain ⟨e, he⟩ := (A.valuation_eq_iff ((u : D) : K) (p : K)).mp huA
    refine ⟨e, Subtype.ext ?_⟩
    change (p : K) * ((e : A) : K) = ((u : D) : K)
    simpa only [mul_comm] using he
  have huirr : Irreducible uA := hassoc.irreducible hp
  refine ⟨u, ?_, ?_, ?_⟩
  · exact A.mem_nonunits_iff.mpr (lt_of_le_of_ne hule (fun heq =>
      huirr.not_isUnit ((A.valuation_eq_one_iff uA).mpr heq)))
  · intro y hy
    exact div_mem_of_irreducible A huirr hy
  · intro B hBT
    by_cases hBD : D ≤ B.toSubring
    · let e : D →+* B := Subring.inclusion hBD
      exact B.valuation_unit (Units.map e.toMonoidHom u)
    · have hBs : B ∈ s := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hBT, hBD⟩)
      have hBA : B ≠ A := by intro h; exact hAT (h ▸ hBT)
      calc
        _ = B.valuation x := hu B hBs
        _ = B.valuation (target ⟨B, hBs⟩) := hx ⟨B, hBs⟩
        _ = 1 := by simp [target, hBA]

/-- A nonzero Jacobson element, hereditary atomicity, and rank one for the
outside valuation rings supply actual finite outside-unit approximation. -/
theorem hasFiniteOutsideUnitApproximation_of_jacobson (D : Subring K)
    [IsFractionRing D K] (hD : Factorization.IsHereditarilyAtomic D)
    {j : D} (hj : j ∈ Ideal.jacobson (⊥ : Ideal D)) (hj0 : j ≠ 0)
    (hrank : ∀ V : ValuationSubring K, ¬ D ≤ V.toSubring → Nonempty V.valuation.RankOne) :
    HasFiniteOutsideUnitApproximation D := by
  classical
  apply approximation_of_dvr_and_unit_realization D
  · intro V hV
    let : V.valuation.RankOne := Classical.choice (hrank V hV)
    apply outside_valuationSubring_isDiscreteValuationRing hD V hj hj0
    obtain ⟨d, hd, hdV⟩ := SetLike.not_le_iff_exists.mp hV
    exact ⟨⟨d, hd⟩, hdV⟩
  · intro s hs x hx
    let val (V : s) := V.val.valuation
    let (V : s) : (val V).RankOne := Classical.choice (hrank V (hs V V.property))
    have hout : ∀ V : s, ∃ d : D, 1 < val V (algebraMap D K d) := by
      intro V
      obtain ⟨d, hd, hdV⟩ := SetLike.not_le_iff_exists.mp (hs V V.property)
      refine ⟨⟨d, hd⟩, lt_of_not_ge ?_⟩
      intro h
      exact hdV ((V.val.valuation_le_one_iff d).mp h)
    obtain ⟨u, hu⟩ := exists_unit_same_values val hj hj0 hout x hx
    exact ⟨u, fun V hV => hu ⟨V, hV⟩⟩

/-- For an HA field, weak approximation itself gives source units. There is no
nonzero-Jacobson hypothesis in this field case. -/
theorem field_hasFiniteOutsideUnitApproximation
    (hK : Factorization.IsHereditarilyAtomic K) :
    HasFiniteOutsideUnitApproximation (⊤ : Subring K) := by
  classical
  apply approximation_of_dvr_and_unit_realization (⊤ : Subring K)
  · intro V hV
    exact field_valuationSubring_isDiscreteValuationRing hK V (outside_ne_top hV)
  · intro s _ x hx
    refine ⟨Units.map (Subring.topEquiv.symm.toMonoidHom) (Units.mk0 x hx), ?_⟩
    intro V _
    rfl

end HereditaryAtomicity
