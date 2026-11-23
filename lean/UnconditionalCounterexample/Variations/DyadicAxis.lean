import UnconditionalCounterexample.Variations.DyadicPair
import Factorization.Bounds
import Factorization.Transport
import UnconditionalCounterexample.ConductorAtomicity

/-!
# Bounded decomposition lengths on the two axes

A pure effective profile of height zero at both centres and with one regular
colour identically zero vanishes. For an element with either height zero, the
two heights, its supplementary support, and a finite prefix of that colour
therefore detect every nonunit divisor.
-/

namespace UnconditionalCounterexample.DyadicProfiles

/-- Value at a regular site on a chosen colour. -/
def Profile.regular (p : Profile) (colour k : Bool) : ℕ → ℕ :=
  if colour then p.minus k else p.plus k

theorem Profile.regular_stable (p : Profile) (c k : Bool) {n : ℕ} (hn : p.cutoff ≤ n) :
    p.regular c k n = p.height c := by
  cases c <;> simp [Profile.regular, p.minus_stable k n hn, p.plus_stable k n hn]

/-- Equal signed masses at zero heights identify the two unsigned sums. -/
private theorem regular_sum_eq (p : Profile) (hp : p.MassEquations)
    (hh : ∀ k, p.height k = 0) (k : Bool) {N : ℕ} (hN : p.cutoff ≤ N) :
    (∑ n ∈ Finset.range N, weight n * (p.plus k n : ℚ)) =
      ∑ n ∈ Finset.range N, weight n * (p.minus k n : ℚ) := by
  have h := hp k
  rw [p.signedMass_eq_of_le k hN, mass_eq_sum] at h
  simpa [Profile.difference, Profile.tailDifference, hh, mul_sub, Finset.sum_sub_distrib,
    sub_eq_zero] using h

private theorem vanishes_of_sum_eq_zero (v : ℕ → ℕ) (n N : ℕ) (hn : n < N)
    (hv : ∑ i ∈ Finset.range N, weight i * (v i : ℚ) = 0) : v n = 0 := by
  have hw (i : ℕ) : 0 < weight i := pow_pos (by norm_num : 0 < (1/2 : ℚ)) _
  have hnon (i : ℕ) (_ : i ∈ Finset.range N) : 0 ≤ weight i * (v i : ℚ) :=
    mul_nonneg (hw i).le (Nat.cast_nonneg _)
  have hle := Finset.single_le_sum hnon (Finset.mem_range.mpr hn)
  rw [hv] at hle
  have he : weight n * (v n : ℚ) = 0 := le_antisymm hle (hnon n (Finset.mem_range.mpr hn))
  exact_mod_cast (mul_eq_zero.mp he).resolve_left (hw n).ne'

/-- On either axis, a divisor invisible at both centres and at all sites
of the zero-height colour has zero effective regular profile. -/
theorem Profile.regular_eq_zero_of_colour (p : Profile) (hp : p.MassEquations)
    (hh : ∀ k, p.height k = 0) (colour : Bool) (hz : ∀ k n, p.regular colour k n = 0)
    (k : Bool) (n : ℕ) : p.plus k n = 0 ∧ p.minus k n = 0 := by
  let N := max p.cutoff (n + 1)
  have hN : p.cutoff ≤ N := le_max_left ..
  have hn : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right ..)
  have hsum := regular_sum_eq p hp hh k hN
  cases colour with
  | false =>
    have hz' (i : ℕ) : p.plus k i = 0 := hz k i
    refine ⟨hz' n, vanishes_of_sum_eq_zero _ n N hn ?_⟩
    rw [← hsum]
    simp [hz']
  | true =>
    have hz' (i : ℕ) : p.minus k i = 0 := hz k i
    refine ⟨vanishes_of_sum_eq_zero _ n N hn ?_, hz' n⟩
    rw [hsum]
    simp [hz']

private def regularSite {E : Type*} (c k : Bool) (n : ℕ) : Site E :=
  if c then Site.minus k n else Site.plus k n

private theorem values_regularSite {E : Type*} (p : Profile) (e : E → ℕ) (c k : Bool) (n : ℕ) :
    p.values e (regularSite c k n) = p.regular c k n := by
  cases c <;> rfl

namespace Realization

variable {R E : Type*} [CommRing R] [IsDomain R] (D : Realization R E)

/-- An axis element is bounded by a finite family consisting of its two heights,
its supplementary support, and the initial sites of its zero-height colour. -/
theorem bounded_of_axis {x : R} (hx : x ≠ 0)
    (hfinite : (Function.support (D.extra x)).Finite) (c : Bool)
    (hc : (D.regular x).height c = 0) : Factorization.HasBoundedFactorizations x := by
  classical
  let centres : Finset (Site E) := Finset.univ.image Site.centre
  let earlySites : Finset (Site E) :=
    (Finset.univ ×ˢ Finset.range (D.regular x).cutoff).image
      (fun a : Bool × ℕ => regularSite c a.1 a.2)
  let extras : Finset (Site E) := hfinite.toFinset.image Site.other
  let sites := centres ∪ earlySites ∪ extras
  have hcsite (k : Bool) : Site.centre k ∈ sites := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hpre (k : Bool) (n : ℕ) (hn : n < (D.regular x).cutoff) : regularSite c k n ∈ sites := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(k,n), by simp [hn], rfl⟩
  have hsup (i : E) (hi : D.extra x i ≠ 0) : Site.other i ∈ sites := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨i, hfinite.mem_toFinset.mpr hi, rfl⟩
  refine Factorization.hasBoundedFactorizations_of_finite_nat_detectors sites
    (fun i a => D.values a i) ?_ ?_ hx ?_
  · intro i _ u hu
    have he := (D.dvd_iff u 1 hu.ne_zero one_ne_zero).mp hu.dvd i
    change D.values u i ≤ D.values 1 i at he
    simpa [D.values_one] using he
  · intro i _ a b ha hb
    exact congrFun (D.mul_values a b ha hb) i
  intro a ha hdvd hnunit
  by_contra hmissing
  have hz (i : Site E) (hi : i ∈ sites) : D.values a i = 0 :=
    Nat.eq_zero_of_not_pos (fun h => hmissing ⟨i, hi, h⟩)
  have hle := (D.dvd_iff a x ha hx).mp hdvd
  have hheight (k : Bool) : (D.regular a).height k = 0 := hz _ (hcsite k)
  have hextra : D.extra a = 0 := by
    funext i
    by_cases hi : D.extra x i = 0
    · exact Nat.le_zero.mp ((hle (.other i)).trans_eq hi)
    · exact hz _ (hsup i hi)
  have hcolour (k : Bool) (n : ℕ) : (D.regular a).regular c k n = 0 := by
    by_cases hi : n < (D.regular x).cutoff
    · exact (values_regularSite _ _ c k n).symm.trans (hz _ (hpre k n hi))
    · have h := hle (regularSite c k n)
      rw [values_regularSite, values_regularSite, Profile.regular_stable (D.regular x) c k (Nat.le_of_not_gt hi), hc] at h
      exact Nat.le_zero.mp h
  have hreg := (D.regular a).regular_eq_zero_of_colour (D.mass_of_pure a ha hextra)
    hheight c hcolour
  have hzero : D.values a = 0 := by
    funext i
    cases i with
    | centre k => exact hheight k
    | other i => exact congrFun hextra i
    | plus k n => exact (hreg k n).1
    | minus k n => exact (hreg k n).2
  apply hnunit
  apply isUnit_of_dvd_one
  apply (D.dvd_iff a 1 ha one_ne_zero).mpr
  change D.values a ≤ D.values 1
  rw [hzero, D.values_one]

/-- In a ring with sign units the axis bound holds intrinsically in each
unital subring. -/
theorem subring_bounded_of_axis (hsign : ∀ u : R, IsUnit u → u = 1 ∨ u = -1)
    (T : Subring R) (x : T) (hx : x ≠ 0)
    (hfinite : (Function.support (D.extra x)).Finite)
    (haxis : (D.regular x).height false = 0 ∨ (D.regular x).height true = 0) :
    Factorization.HasBoundedFactorizations x := by
  apply Factorization.hasBoundedFactorizations_of_unitReflectingMap T.subtype.toMonoidHom
    (subring_isUnit_of_signUnits hsign T)
  have hR : (x : R) ≠ 0 := fun h => hx (Subtype.ext h)
  rcases haxis with h | h
  · exact D.bounded_of_axis hR hfinite false h
  · exact D.bounded_of_axis hR hfinite true h

end Realization

end UnconditionalCounterexample.DyadicProfiles
