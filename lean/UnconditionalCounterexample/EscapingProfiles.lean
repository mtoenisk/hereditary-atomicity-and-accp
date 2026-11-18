import UnconditionalCounterexample.ValuationProfiles
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Extracting divisors with escaping primary support

An arbitrarily long decomposition of one fixed nonzero top contains a factor
undetected by any prescribed finite family of profile coordinates. Finiteness
of the top's outside support then gives a pure primary divisor. The uniform
primary bound comes from eventual stabilization of the top's profile. These
arguments use decompositions into arbitrary nonunits, without atomicity.
-/

namespace UnconditionalCounterexample

universe u v

variable {R : Type u} {ι : Type v} [CommRing R] [IsDomain R]

namespace ValuationProfiles

/-- The primary values of a fixed nonzero element have one positive natural
upper bound, because they are eventually constant. -/
theorem exists_positive_primary_bound (v : ValuationProfiles R ι)
    {x : R} (hx : x ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ j, v.value (.primary j) x ≤ r := by
  obtain ⟨N, hN⟩ := v.eventually_primary x hx
  let r := max (v.value .limit x) ((Finset.range N).sup (fun j => v.value (.primary j) x)) + 1
  refine ⟨r, by dsimp [r]; omega, ?_⟩
  intro j
  by_cases hj : j < N
  · have hjbound := Finset.le_sup (f := fun j => v.value (.primary j) x)
      (Finset.mem_range.mpr hj)
    dsimp [r]
    omega
  · rw [hN j (by omega)]
    dsimp [r]
    omega

/-- A non-BF top in a subring has a nonunit divisor with zero value at every
coordinate in any prescribed finite set. The divisor is selected as an
actual occurrence in a sufficiently long nonunit decomposition. -/
theorem exists_divisor_avoiding_finite_places
    (v : ValuationProfiles R ι) (T : Subring R)
    (hunit : ∀ y : T, IsUnit (y : R) → IsUnit y)
    {x : T} (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x)
    (indices : Finset (ProfilePlace ι)) :
    ∃ y : T, y ≠ 0 ∧ ¬ IsUnit (y : R) ∧ y ∣ x ∧
      ∀ p ∈ indices, v.value p y = 0 := by
  classical
  let weight : ProfilePlace ι → T → ℕ := fun p y => v.value p y
  let bound := ∑ p ∈ indices, weight p x
  obtain ⟨factors, hnonunits, hfac, hlong⟩ :
      ∃ factors : Multiset T, (∀ y ∈ factors, ¬ IsUnit y) ∧
        Associated factors.prod x ∧ bound < factors.card := by
    by_contra h
    apply hunbounded
    refine ⟨bound, ?_⟩
    intro factors hnonunits hfac
    by_contra hnotle
    exact h ⟨factors, hnonunits, hfac, Nat.lt_of_not_ge hnotle⟩
  let detected : T → Prop := fun y => ∃ p ∈ indices, 0 < weight p y
  have hcount := Factorization.filter_card_le_sum_nat_of_finite_detectors
    indices weight
    (fun p _ y hy => v.value_unit p y (hy.map T.subtype.toMonoidHom))
    (fun p _ y z hy hz => v.value_mul p y z
      (fun h => hy (Subtype.ext h)) (fun h => hz (Subtype.ext h)))
    hx factors hfac detected (fun _ _ h => h)
  obtain ⟨y, hyfactor, hyundetected⟩ : ∃ y ∈ factors, ¬ detected y := by
    by_contra h
    have hall : ∀ y ∈ factors, detected y := by
      intro y hy
      by_contra hnot
      exact h ⟨y, hy, hnot⟩
    have hfilter : factors.filter detected = factors := Multiset.filter_eq_self.mpr hall
    rw [hfilter] at hcount
    exact (Nat.not_le_of_gt hlong) hcount
  have hydvd : y ∣ x := (Multiset.dvd_prod hyfactor).trans hfac.dvd
  refine ⟨y, ne_zero_of_dvd_ne_zero hx hydvd,
    fun hyunit => hnonunits y hyfactor (hunit y hyunit), hydvd, ?_⟩
  intro p hp
  exact Nat.eq_zero_of_not_pos (fun hpos => hyundetected ⟨p, hp, hpos⟩)

end ValuationProfiles

/-- A divisor with nonempty finite effective primary support outside a fixed
prefix. It is an element and divisor in the source subring, and an ambient
nonunit. All values are the actual natural-valued profile coordinates. -/
structure IsEscapingPrimaryDivisor (v : ValuationProfiles R ι)
    (T : Subring R) (x y : T) (r N : ℕ) : Prop where
  ne_zero : y ≠ 0
  nonunit : ¬ IsUnit (y : R)
  dvd_top : y ∣ x
  limit_zero : v.value .limit y = 0
  outside_zero : ∀ i, v.value (.outside i) y = 0
  prefix_zero : ∀ j, j < N → v.value (.primary j) y = 0
  primary_bound : ∀ j, v.value (.primary j) y ≤ r
  finite_support : {j | v.value (.primary j) y ≠ 0}.Finite
  nonempty_support : ∃ j, 0 < v.value (.primary j) y

/-- The extracted ambient nonunit is also a nonunit for the source ring's
own unit predicate. -/
theorem IsEscapingPrimaryDivisor.nonunit_source
    {v : ValuationProfiles R ι} {T : Subring R} {x y : T} {r N : ℕ}
    (h : IsEscapingPrimaryDivisor v T x y r N) : ¬ IsUnit y :=
  fun hy => h.nonunit (hy.map T.subtype.toMonoidHom)

namespace ValuationProfiles

/-- Arbitrarily long intrinsic nonunit decompositions of one top provide
pure primary divisors escaping every finite prefix, with one common positive
bound on every primary value. -/
theorem exists_escaping_primary_divisors
    (v : ValuationProfiles R ι) (T : Subring R)
    (hunit : ∀ y : T, IsUnit (y : R) → IsUnit y)
    {x : T} (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ r : ℕ, 0 < r ∧ ∀ N : ℕ,
      ∃ y : T, IsEscapingPrimaryDivisor v T x y r N := by
  classical
  have hxR : (x : R) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨r, hr, hrbound⟩ := v.exists_positive_primary_bound hxR
  refine ⟨r, hr, ?_⟩
  intro N
  let outside : Finset ι := (v.finite_outside x hxR).toFinset
  let indices : Finset (ProfilePlace ι) :=
    insert .limit ((Finset.range N).image ProfilePlace.primary ∪
      outside.image ProfilePlace.outside)
  obtain ⟨y, hy0, hynonunit, hydvd, hyzero⟩ :=
    v.exists_divisor_avoiding_finite_places T hunit hx hunbounded indices
  have hyR : (y : R) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hydvdR : (y : R) ∣ (x : R) := by
    obtain ⟨z, hz⟩ := hydvd
    exact ⟨z, congrArg Subtype.val hz⟩
  have hlimit : v.value .limit y = 0 := hyzero .limit (Finset.mem_insert_self _ _)
  have houtside : ∀ i, v.value (.outside i) y = 0 := by
    intro i
    by_cases hi : i ∈ outside
    · apply hyzero
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    · have hix : v.value (.outside i) x = 0 := by
        simpa only [outside, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
      have hle := v.value_le_of_dvd (.outside i) hxR hydvdR
      omega
  have hprefix : ∀ j, j < N → v.value (.primary j) y = 0 := by
    intro j hj
    apply hyzero
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩))
  have hbound : ∀ j, v.value (.primary j) y ≤ r := by
    intro j
    exact (v.value_le_of_dvd (.primary j) hxR hydvdR).trans (hrbound j)
  have hfinite : {j | v.value (.primary j) y ≠ 0}.Finite := by
    obtain ⟨M, hM⟩ := v.eventually_primary y hyR
    apply (Finset.range M).finite_toSet.subset
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hnot
    exact hj ((hM j (Nat.le_of_not_gt hnot)).trans hlimit)
  have hnonempty : ∃ j, 0 < v.value (.primary j) y := by
    by_contra hnot
    apply hynonunit
    apply v.unit_of_zero y hyR
    intro p
    cases p with
    | limit => exact hlimit
    | outside i => exact houtside i
    | primary j => exact Nat.eq_zero_of_not_pos (fun hj => hnot ⟨j, hj⟩)
  exact ⟨y, ⟨hy0, hynonunit, hydvd, hlimit, houtside, hprefix, hbound, hfinite, hnonempty⟩⟩

end ValuationProfiles
end UnconditionalCounterexample
