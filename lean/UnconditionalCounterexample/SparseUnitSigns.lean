import UnconditionalCounterexample.SparseProfiles
import UnconditionalCounterexample.UnitSigns

/-!
# Units in sparse-primary intersections

The exact complete profile forces the finite normalized word of a unit to
vanish. The common zero-word lemma is reused from UnitSigns; no primary
surjectivity is needed.
-/

noncomputable section

namespace UnconditionalCounterexample.SparseUnitSigns
open SparseProfiles DiscreteOrders NormalizedWords PrincipalProfiles

/-- A nonzero fraction whose complete actual order profile vanishes is a sign. -/
theorem eq_one_or_neg_one_of_orders_zero (F : ℕ → Polynomial ℚ)
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (E : ℕ → ℕ) (d : SparsePrimaryDomain.Places) (hG : GeneratorProfiles F E d)
    (x : RatFunc ℚ) (hx : x ≠ 0)
    (hzero : ∀ p, order (valuations (Set.range F) d p) x = 0) :
    x = 1 ∨ x = -1 := by
  obtain ⟨e, he, hrep⟩ := exists_signed_word F hF hinj E d hG x hx
    (hzero .limit) (fun i => hzero (.outside i))
  have he0 := UnitSigns.exponents_eq_zero_of_represents_zero e _ hrep (fun j => hzero (.primary j))
  simpa only [he0, word, Finsupp.prod_zero_index] using he

/-- The literal sparse domain has precisely the two rational signs as units. -/
theorem isUnit_iff_eq_one_or_neg_one (F : ℕ → Polynomial ℚ)
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (hconst : ∀ i, (F i).coeff 0 ≠ 0) (E : ℕ → ℕ)
    (d : SparsePrimaryDomain.Places) (hG : GeneratorProfiles F E d)
    (x : SparsePrimaryDomain.domain (Set.range F) d) : IsUnit x ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    have hx0 : x ≠ 0 := hx.ne_zero
    have hC : ∀ q ∈ Set.range F, q.coeff 0 ≠ 0 := by
      rintro q ⟨i, rfl⟩
      exact hconst i
    have hzero := (SparseProfiles.isUnit_iff_order_zero _ d hC x hx0).mp hx
    have hsign := eq_one_or_neg_one_of_orders_zero F hF hinj E d hG x
      (fun h => hx0 (Subtype.ext h)) hzero
    rcases hsign with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact isUnit_neg_one

theorem actual_subring_reflects_units (F : ℕ → Polynomial ℚ)
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (hconst : ∀ i, (F i).coeff 0 ≠ 0) (E : ℕ → ℕ)
    (d : SparsePrimaryDomain.Places) (hG : GeneratorProfiles F E d)
    (T : Subring (SparsePrimaryDomain.domain (Set.range F) d)) (x : T) :
    IsUnit (x : SparsePrimaryDomain.domain (Set.range F) d) → IsUnit x :=
  UnitSigns.subring_reflects_units (fun y hy =>
    (isUnit_iff_eq_one_or_neg_one F hF hinj hconst E d hG y).mp hy) T x

end UnconditionalCounterexample.SparseUnitSigns
