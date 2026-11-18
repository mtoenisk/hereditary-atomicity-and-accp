import UnconditionalCounterexample.ValuationProfiles

/-!
# Bounded nonunit decompositions at horizontal order zero or one

The finite detector set consists of the horizontal order, a primary prefix,
and the outside support of the top. The triple congruences exclude a pure
primary nonunit supported beyond that prefix. No atomicity is assumed.
-/

namespace UnconditionalCounterexample

universe u v

namespace ValuationProfiles

variable {R : Type u} {ι : Type v} [CommRing R] [IsDomain R]

/-- Every nonzero element of horizontal order at most one has bounded
decompositions into arbitrary nonunits in the ambient domain. -/
theorem hasBoundedFactorizations_of_limit_le_one
    (v : ValuationProfiles R ι) {x : R} (hx : x ≠ 0)
    (hlimit : v.value .limit x ≤ 1) : Factorization.HasBoundedFactorizations x := by
  classical
  obtain ⟨N, hN⟩ := v.eventually_primary x hx
  let outside : Finset ι := (v.finite_outside x hx).toFinset
  let indices : Finset (ProfilePlace ι) :=
    insert .limit ((Finset.range (2 * N + 1)).image ProfilePlace.primary ∪
      outside.image ProfilePlace.outside)
  apply Factorization.hasBoundedFactorizations_of_finite_nat_detectors indices v.value
    (fun p _ a ha => v.value_unit p a ha)
    (fun p _ a b ha hb => v.value_mul p a b ha hb) hx
  intro a ha hax hnonunit
  by_contra hnot
  have hzero : ∀ p ∈ indices, v.value p a = 0 := by
    intro p hp
    by_contra hpzero
    exact hnot ⟨p, hp, Nat.pos_of_ne_zero hpzero⟩
  have halimit : v.value .limit a = 0 := hzero .limit (Finset.mem_insert_self _ _)
  have haoutside : ∀ i, v.value (.outside i) a = 0 := by
    intro i
    by_cases hi : i ∈ outside
    · apply hzero
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    · have hix : v.value (.outside i) x = 0 := by
        simpa only [outside, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
      have hle := v.value_le_of_dvd (.outside i) hx hax
      omega
  have haprefix : ∀ i, i < 2 * N + 1 → v.value (.primary i) a = 0 := by
    intro i hi
    apply hzero
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩))
  have haeventually : EventuallyConstantProfile (fun i => (v.value (.primary i) a : ℤ)) 0 := by
    obtain ⟨M, hM⟩ := v.eventually_primary a ha
    refine ⟨M, ?_⟩
    intro i hi
    change (v.value (.primary i) a : ℤ) = 0
    rw [hM i hi, halimit]
    rfl
  have hatriple := v.pure_triple a ha halimit haoutside
  have hatail : ∀ i, 2 * N + 1 ≤ i → v.value (.primary i) a = 0 := by
    intro i hi
    have h := tail_eq_zero_of_triple_congruences
      (fun j => (v.value (.primary j) a : ℤ)) N haeventually
      (fun j hj => by
        have hle := v.value_le_of_dvd (.primary j) hx hax
        have hstable := hN j (by omega)
        constructor
        · exact Int.natCast_nonneg _
        · exact_mod_cast (show v.value (.primary j) a ≤ 1 by omega))
      (fun n _ => hatriple.2 n) i hi
    exact_mod_cast h
  apply hnonunit
  apply v.unit_of_zero a ha
  intro p
  cases p with
  | limit => exact halimit
  | outside i => exact haoutside i
  | primary i =>
      by_cases hi : i < 2 * N + 1
      · exact haprefix i hi
      · exact hatail i (by omega)

end ValuationProfiles
end UnconditionalCounterexample
