import UnconditionalCounterexample.CompleteProfiles

/-!
# The units of the actual guarded intersection

A zero primary profile kills every finite signed normalized exponent. Actual
signed factorization therefore identifies the units as precisely 1 and -1.
-/

noncomputable section
namespace UnconditionalCounterexample.UnitSigns
open CompleteProfiles DiscreteOrders NormalizedWords PrincipalProfiles

/-- The overlapping primary rows determine every signed exponent. -/
theorem exponents_eq_zero_of_represents_zero (e : ℕ →₀ ℤ) (g : ℕ → ℤ)
    (h : Represents (StageExponents.bExponents e) (StageExponents.qExponents e) g)
    (hg : ∀ j, g j = 0) : e = 0 := by
  have hbq (n : ℕ) := exponents_zero_of_profile_prefix h n (fun j _ => hg j) n le_rfl
  ext j
  obtain ⟨i, rfl⟩ := StageExponents.stage_surjective j
  cases i with
  | b n => exact (hbq n).1
  | q n => exact (hbq n).2

/-- A nonzero fraction whose complete actual order profile vanishes is a sign. -/
theorem eq_one_or_neg_one_of_orders_zero (F : ℕ → Polynomial ℚ)
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (E : ℕ → ℕ) (d : PairedDomain.Places) (hG : GeneratorProfiles F E d)
    (x : RatFunc ℚ) (hx : x ≠ 0)
    (hzero : ∀ p, order (valuations (Set.range F) d p) x = 0) :
    x = 1 ∨ x = -1 := by
  obtain ⟨e, he, hrep⟩ := exists_signed_word F hF hinj E d hG x hx
    (hzero .limit) (fun i => hzero (.outside i))
  have he0 := exponents_eq_zero_of_represents_zero e _ hrep (fun j => hzero (.primary j))
  simpa only [he0, word, Finsupp.prod_zero_index] using he

/-- The literal paired domain has precisely the two rational signs as units. -/
theorem isUnit_iff_eq_one_or_neg_one (F : ℕ → Polynomial ℚ)
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (hconst : ∀ i, (F i).coeff 0 ≠ 0) (E : ℕ → ℕ)
    (d : PairedDomain.Places) (hG : GeneratorProfiles F E d)
    (x : PairedDomain.domain (Set.range F) d) : IsUnit x ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    have hx0 : x ≠ 0 := hx.ne_zero
    have hC : ∀ q ∈ Set.range F, q.coeff 0 ≠ 0 := by
      rintro q ⟨i, rfl⟩
      exact hconst i
    have hzero := (CompleteProfiles.isUnit_iff_order_zero _ d hC x hx0).mp hx
    have hsign := eq_one_or_neg_one_of_orders_zero F hF hinj E d hG x
      (fun h => hx0 (Subtype.ext h)) hzero
    rcases hsign with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact isUnit_neg_one

/-- Every unital subring reflects units when the ambient units are signs. -/
theorem subring_reflects_units {R : Type*} [CommRing R]
    (hR : ∀ x : R, IsUnit x → x = 1 ∨ x = -1)
    (T : Subring R) (x : T) : IsUnit (x : R) → IsUnit x := by
  intro hx
  rcases hR x hx with h | h
  · have hx1 : x = 1 := Subtype.ext h
    rw [hx1]
    exact isUnit_one
  · have hxm : x = -1 := Subtype.ext h
    rw [hxm]
    exact isUnit_neg_one

theorem actual_subring_reflects_units (F : ℕ → Polynomial ℚ)
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (hconst : ∀ i, (F i).coeff 0 ≠ 0) (E : ℕ → ℕ)
    (d : PairedDomain.Places) (hG : GeneratorProfiles F E d)
    (T : Subring (PairedDomain.domain (Set.range F) d)) (x : T) :
    IsUnit (x : PairedDomain.domain (Set.range F) d) → IsUnit x :=
  subring_reflects_units (fun y hy =>
    (isUnit_iff_eq_one_or_neg_one F hF hinj hconst E d hG y).mp hy) T x

end UnconditionalCounterexample.UnitSigns
