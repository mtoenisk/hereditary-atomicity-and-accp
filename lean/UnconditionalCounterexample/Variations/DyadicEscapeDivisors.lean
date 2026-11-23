import UnconditionalCounterexample.Variations.DyadicAxis
import UnconditionalCounterexample.Variations.DyadicEscape

/-!
# Escaping divisors in a subring of the dyadic construction

A sufficiently long intrinsic decomposition supplies a nonunit divisor avoiding
the two centres, every supplementary coordinate, and any given initial segment
of the four regular sequences. All such divisors are bounded by one fixed
regular valuation bound, that of the original element.
-/

namespace UnconditionalCounterexample.DyadicProfiles

namespace Profile

/-- Uniform bound on all four regular sequences, including their constant tails. -/
theorem exists_regular_bound (p : Profile) :
    ∃ h : ℕ, ∀ k n, p.plus k n ≤ h ∧ p.minus k n ≤ h := by
  let coordinates := (Finset.univ : Finset Bool) ×ˢ Finset.range p.cutoff
  let v (i : Bool × ℕ) := max (p.plus i.1 i.2) (p.minus i.1 i.2)
  let h := max (max (p.height false) (p.height true)) (coordinates.sup v)
  refine ⟨h, fun k n => ?_⟩
  by_cases hn : n < p.cutoff
  · have hb : v (k,n) ≤ coordinates.sup v := Finset.le_sup (f := v) (by simp [coordinates, hn])
    exact ⟨(le_max_left ..).trans (hb.trans (le_max_right ..)),
      (le_max_right ..).trans (hb.trans (le_max_right ..))⟩
  · rw [p.plus_stable k n (by omega), p.minus_stable k n (by omega)]
    exact ⟨(le_max_left ..).trans (le_max_left ..), (le_max_right ..).trans (le_max_left ..)⟩

end Profile

namespace Realization

variable {R E : Type*} [CommRing R] [IsDomain R] (D : Realization R E)

/-- A divisor of the original element in its own subring, with nonempty regular
support beyond a prescribed prefix and no other support. -/
structure EscapingDivisor (T : Subring R) (x y : T) (h N : ℕ) : Prop where
  ne_zero : y ≠ 0
  nonunit : ¬ IsUnit (y : R)
  dvd : y ∣ x
  height_zero : ∀ k, (D.regular y).height k = 0
  extra_zero : D.extra y = 0
  regular_bound : ∀ k n, (D.regular y).plus k n ≤ h ∧ (D.regular y).minus k n ≤ h
  regular_avoids : ∀ k n, n ≤ N → (D.regular y).plus k n = 0 ∧ (D.regular y).minus k n = 0
  regular_nonzero : ∃ k n, (D.regular y).plus k n ≠ 0 ∨ (D.regular y).minus k n ≠ 0

private theorem exists_avoiding (T : Subring R) {x : T} (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) (sites : Finset (Site E)) :
    ∃ y : T, y ≠ 0 ∧ ¬ IsUnit y ∧ y ∣ x ∧ ∀ i ∈ sites, D.values y i = 0 := by
  classical
  by_contra hn
  apply hunbounded
  apply Factorization.hasBoundedFactorizations_of_finite_nat_detectors sites
    (fun i (a : T) => D.values a i) _ _ hx
  · intro a ha hd hnu
    by_contra h
    apply hn
    exact ⟨a, ha, hnu, hd, fun i hi => Nat.eq_zero_of_not_pos (fun hp => h ⟨i, hi, hp⟩)⟩
  · intro i _ a ha
    have hu := ha.map T.subtype.toMonoidHom
    have he := (D.dvd_iff (a : R) 1 hu.ne_zero one_ne_zero).mp hu.dvd i
    change D.values a i ≤ D.values 1 i at he
    simpa [D.values_one] using he
  · intro i _ a b ha hb
    have ha' : (a : R) ≠ 0 := fun he => ha (Subtype.ext he)
    have hb' : (b : R) ≠ 0 := fun he => hb (Subtype.ext he)
    exact congrFun (D.mul_values a b ha' hb') i

/-- Unbounded lengths in `T` give an actual bounded divisor in `T` with
nonempty pure regular support past each prefix. The bound depends only on `x`. -/
theorem exists_escaping_divisors (hsign : ∀ u : R, IsUnit u → u = 1 ∨ u = -1)
    (T : Subring R) {x : T} (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x)
    (hfinite : (Function.support (D.extra x)).Finite) :
    ∃ h : ℕ, ∀ N : ℕ, ∃ y : T, D.EscapingDivisor T x y h N := by
  classical
  obtain ⟨h, hh⟩ := (D.regular x).exists_regular_bound
  refine ⟨h, fun N => ?_⟩
  let early := (Finset.univ : Finset Bool) ×ˢ Finset.range (N+1)
  let plusSites := early.image (fun i => (Site.plus i.1 i.2 : Site E))
  let minusSites := early.image (fun i => (Site.minus i.1 i.2 : Site E))
  let centres := (Finset.univ : Finset Bool).image (Site.centre (E := E))
  let others := hfinite.toFinset.image Site.other
  let sites := (plusSites ∪ minusSites) ∪ (centres ∪ others)
  obtain ⟨y, hy, hnu, hd, hz⟩ := D.exists_avoiding T hx hunbounded sites
  have hy' : (y : R) ≠ 0 := fun he => hy (Subtype.ext he)
  have hx' : (x : R) ≠ 0 := fun he => hx (Subtype.ext he)
  have hle := (D.dvd_iff y x hy' hx').mp (map_dvd T.subtype hd)
  have hcentre (k : Bool) : (D.regular y).height k = 0 := hz (.centre k) (by
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have hother : D.extra y = 0 := by
    funext i
    by_cases he : D.extra x i = 0
    · exact Nat.le_zero.mp ((hle (.other i)).trans_eq he)
    · exact hz (.other i) (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, hfinite.mem_toFinset.mpr he, rfl⟩)))
  have hnonunit : ¬ IsUnit (y : R) := fun hu => hnu (subring_isUnit_of_signUnits hsign T y hu)
  refine ⟨y, hy, hnonunit, hd, hcentre, hother, ?_, ?_, ?_⟩
  · intro k n
    exact ⟨(hle (.plus k n)).trans (hh k n).1, (hle (.minus k n)).trans (hh k n).2⟩
  · intro k n hn
    have hpre : (k,n) ∈ early := by simp [early, Nat.lt_succ_of_le hn]
    exact ⟨hz (.plus k n) (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(k,n), hpre, rfl⟩))),
      hz (.minus k n) (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(k,n), hpre, rfl⟩)))⟩
  · by_contra hn
    push Not at hn
    apply hnonunit
    apply isUnit_of_dvd_one
    apply (D.dvd_iff (y : R) 1 hy' one_ne_zero).mpr
    change D.values y ≤ D.values 1
    rw [D.values_one]
    intro i
    cases i with
    | centre k => exact (hcentre k).le
    | other i => exact (congrFun hother i).le
    | plus k n => exact (hn k n).1.le
    | minus k n => exact (hn k n).2.le

/-- Apply the dyadic stage-list extraction to one top of unbounded intrinsic
factorization lengths. Realization is used only to express a pure regular
element as a signed product in the actual stage enumeration. -/
theorem exists_listed_sequence_of_unbounded {K : Type*} [Field K] (f : R →+* K)
    (W : ℕ → K) (s : DyadicEscape.Schedule)
    (hsign : ∀ u : R, IsUnit u → u = 1 ∨ u = -1)
    (realize : ∀ a : R, a ≠ 0 → (∀ k, (D.regular a).height k = 0) → D.extra a = 0 →
      ∃ w : DyadicEscape.Word s,
        (f a = w.exponent.prod (fun j z => W j ^ z) ∨
         f a = -(w.exponent.prod (fun j z => W j ^ z))) ∧
        (∀ k n, w.plus k n = ((D.regular a).plus k n : ℤ)) ∧
        ∀ k n, w.minus k n = ((D.regular a).minus k n : ℤ))
    (T : Subring R) {x : T} (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x)
    (hfinite : (Function.support (D.extra x)).Finite) :
    ∃ h : ℕ, ∃ y : ℕ → T, ∃ stage : ℕ → ℕ,
      ∃ v : ∀ i, RawWords.StageWord (stage i) (stage i+1),
        (∀ i, i < stage i) ∧ Filter.Tendsto stage Filter.atTop Filter.atTop ∧
        (∀ i, (v i).latestExponent ≤ h) ∧ (∀ i j, |(v i).oldExponent j| ≤ h) ∧
        ∀ i, f (y i : R) = W (stage i) ^ (v i).latestExponent *
          ∏ j ∈ Finset.range (stage i), W j ^ (v i).oldExponent j := by
  obtain ⟨h, he⟩ := D.exists_escaping_divisors hsign T hx hunbounded hfinite
  refine ⟨h, DyadicEscape.exists_bounded_escaping_listed_sequence f T W s h ?_⟩
  intro N
  obtain ⟨y, hy⟩ := he N
  obtain ⟨w, hw, ha, hb⟩ := realize y (fun he => hy.ne_zero (Subtype.ext he))
    hy.height_zero hy.extra_zero
  refine ⟨y, w, hw, ?_, ?_, ?_⟩
  · intro k n
    rw [ha, hb]
    refine ⟨⟨Int.natCast_nonneg _, ?_⟩, Int.natCast_nonneg _, ?_⟩
    · exact_mod_cast (hy.regular_bound k n).1
    · exact_mod_cast (hy.regular_bound k n).2
  · intro k n hn
    simp [ha, hb, (hy.regular_avoids k n hn).1, (hy.regular_avoids k n hn).2]
  · obtain ⟨k, n, hn⟩ := hy.regular_nonzero
    refine ⟨k, n, ?_⟩
    simpa [ha, hb] using hn

end Realization
end UnconditionalCounterexample.DyadicProfiles
