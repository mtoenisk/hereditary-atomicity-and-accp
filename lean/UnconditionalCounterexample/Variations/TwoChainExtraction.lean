import UnconditionalCounterexample.Variations.TwoChainBox
import UnconditionalCounterexample.Variations.TwoChainSchedule

/-!
# Extracting listed mixed words from unbounded lengths

Fix one nonzero element with unbounded intrinsic factorization lengths in a
subring. Two endpoints, the finite outside support of that element and both
finite primary prefixes give a finite family of additive detectors. Arbitrarily
long decompositions supply a divisor on which they all vanish.
-/

namespace UnconditionalCounterexample.Variations.TwoChainExtraction

open TwoChainBox TwoChainSchedule Filter PrincipalProfiles WithZero

variable {R ι : Type*} [CommRing R] [IsDomain R]

/-- Endpoints, primary tails, and all remaining defining places. -/
inductive Place (ι : Type*)
  | endpoint (c : Bool)
  | primary (c : Bool) (n : ℕ)
  | outside (i : ι)
  deriving DecidableEq

def order (v : Orders R ι) : Place ι → R → ℕ
  | .endpoint c, x => v.endpoint x c
  | .primary c n, x => v.primary x c n
  | .outside i, x => v.outside x i

private theorem primary_bound (v : Orders R ι) (x : R) (hx : x ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ c j, v.primary x c j ≤ r := by
  classical
  choose N hN using v.eventually_primary x hx
  let b (c : Bool) := max (v.endpoint x c) ((Finset.range (N c)).sup (v.primary x c))
  refine ⟨Finset.univ.sup b + 1, Nat.succ_pos _, fun c j => ?_⟩
  apply le_trans _ (le_trans (Finset.le_sup (f := b) (Finset.mem_univ c)) (Nat.le_succ _))
  by_cases hj : j < N c
  · exact (Finset.le_sup (f := v.primary x c) (Finset.mem_range.mpr hj)).trans (le_max_right _ _)
  · exact (hN c j (by omega)).le.trans (le_max_left _ _)

/-- Nonunit divisors escaping both tails' prescribed prefixes, with one bound
on every primary order independent of the prefix. The ambient unit criterion
is required to reflect units into the given subring. -/
theorem exists_escaping_divisors (v : Orders R ι)
    (hunit : ∀ p x, IsUnit x → order v p x = 0)
    (hmul : ∀ p a b, a ≠ 0 → b ≠ 0 → order v p (a*b) = order v p a + order v p b)
    (T : Subring R) (hreflect : ∀ y : T, IsUnit (y : R) → IsUnit y)
    {x : T} (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ r : ℕ, 0 < r ∧ ∀ N : ℕ, ∃ y : T, y ≠ 0 ∧ y ∣ x ∧
      (∀ c, v.endpoint y c = 0) ∧ (∀ i, v.outside y i = 0) ∧
      (∀ c j, j < N → v.primary y c j = 0) ∧
      (∀ c j, v.primary y c j ≤ r) ∧ ∃ c j, v.primary y c j ≠ 0 := by
  classical
  have hxR : (x : R) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨r, hr, hbound⟩ := primary_bound v x hxR
  refine ⟨r, hr, fun N => ?_⟩
  let outside := (v.finite_outside x hxR).toFinset
  let initial := (Finset.univ : Finset Bool).biUnion
    (fun c => (Finset.range N).image (Place.primary (ι := ι) c))
  let indices : Finset (Place ι) := (Finset.univ.image Place.endpoint ∪ initial) ∪ outside.image Place.outside
  obtain ⟨y, hy, hdiv, hnu, hzero⟩ :
      ∃ y : T, y ≠ 0 ∧ y ∣ x ∧ ¬ IsUnit y ∧ ∀ p ∈ indices, order v p (y : R) = 0 := by
    by_contra! h
    apply hunbounded
    apply Factorization.hasBoundedFactorizations_of_finite_nat_detectors indices
      (fun p (z : T) => order v p z) _ _ hx
    · intro y hy hd hu
      obtain ⟨p, hp, hpos⟩ := h y hy hd hu
      exact ⟨p, hp, Nat.pos_of_ne_zero hpos⟩
    · intro p _ z hz
      exact hunit p z (hz.map T.subtype)
    · intro p _ z w hz hw
      exact hmul p z w (fun h => hz (Subtype.ext h)) (fun h => hw (Subtype.ext h))
  have he (c) : v.endpoint y c = 0 := hzero (.endpoint c) (by cases c <;> simp [indices])
  have hle := v.le_of_dvd hxR (map_dvd T.subtype hdiv)
  have ho (i) : v.outside y i = 0 := by
    by_cases hi : i ∈ outside
    · exact hzero (.outside i) (by simp [indices, hi])
    · have hxi : v.outside x i = 0 := by simpa [outside] using hi
      exact Nat.eq_zero_of_le_zero ((hle.2.2 i).trans hxi.le)
  refine ⟨y, hy, hdiv, he, ho, ?_, fun c j => (hle.2.1 c j).trans (hbound c j), ?_⟩
  · intro c j hj
    exact hzero (.primary c j) (by simp [indices, initial, hj])
  · by_contra! h
    apply hnu
    apply hreflect
    apply associated_one_iff_isUnit.mp
    apply v.associated_of_eq (y : R) 1 (fun h => hy (Subtype.ext h)) one_ne_zero
    · funext c
      exact (he c).trans (hunit (.endpoint c) 1 isUnit_one).symm
    · funext i
      exact (ho i).trans (hunit (.outside i) 1 isUnit_one).symm
    · funext c j
      exact (h c j).trans (hunit (.primary c j) 1 isUnit_one).symm

/-- Non-BF in an actual subring supplies a single sequence of signed divisors
in that subring which evaluate to listed mixed words at escaping stages.
The representation of pure fractions and the realized generator valuations
are the remaining construction inputs. -/
theorem exists_listed_sequence {K : Type*} [Field K] (v : Orders R ι)
    (hunit : ∀ p x, IsUnit x → order v p x = 0)
    (hmul : ∀ p a b, a ≠ 0 → b ≠ 0 → order v p (a*b) = order v p a + order v p b)
    (f : R →+* K) (W : ℕ → K) (V : Bool → ℕ → Valuation K ℤᵐ⁰)
    (hw : ∀ c j i, V c j (W i) = exp (-weight i c j))
    (hval : ∀ y, y ≠ 0 → ∀ c j, V c j (f y) = exp (-(v.primary y c j : ℤ)))
    (hpure : ∀ y : R, y ≠ 0 → (∀ c, v.endpoint y c = 0) → (∀ i, v.outside y i = 0) →
      ∃ e : ℕ →₀ ℤ, f y = word W e ∨ f y = -word W e)
    (T : Subring R) (hreflect : ∀ y : T, IsUnit (y : R) → IsUnit y)
    {x : T} (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ r : ℕ, 0 < r ∧ ∃ y : ℕ → T, ∃ k : ℕ → ℕ, ∃ w : ∀ n, RawWords.StageWord (k n) (k n+1),
      Tendsto k atTop atTop ∧ ∀ n, y n ∣ x ∧ (w n).latestExponent ≤ 2*r ∧
      (∀ j, |(w n).oldExponent j| ≤ (2*r : ℕ)) ∧
      f (y n : R) = W (k n) ^ (w n).latestExponent * ∏ j ∈ Finset.range (k n), W j ^ (w n).oldExponent j := by
  obtain ⟨r, hr, hy⟩ := exists_escaping_divisors v hunit hmul T hreflect hx hunbounded
  have H (n : ℕ) : ∃ z : T, ∃ k > n, ∃ w : RawWords.StageWord k (k+1),
      z ∣ x ∧ w.latestExponent ≤ 2*r ∧ (∀ j, |w.oldExponent j| ≤ (2*r : ℕ)) ∧
      f (z : R) = W k ^ w.latestExponent * ∏ j ∈ Finset.range k, W j ^ w.oldExponent j := by
    obtain ⟨z, hz0, hd, he, ho, hprefix, hb, hne⟩ := hy (2*max n (2*r)+2)
    have hzR : (z : R) ≠ 0 := fun h => hz0 (Subtype.ext h)
    obtain ⟨e, hprod⟩ := hpure z hzR he ho
    let g (c : Bool) (j : ℕ) : ℤ := v.primary z c j
    have hrep := represents_signed_word V W hw e (f z) hprod g (hval _ hzR)
    obtain ⟨k, hk, w, hlatest, hold, hw'⟩ := exists_listed_word_beyond W e g hrep r n
      (fun c j => ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (hb c j)⟩) (by
        obtain ⟨c,j,hj⟩ := hne
        exact ⟨c, j, Int.natCast_ne_zero.mpr hj⟩) (fun c j hj => by simp [g, hprefix c j hj])
    rcases hprod with hp | hp
    · exact ⟨z, k, hk, w, hd, hlatest, hold, hp.trans hw'⟩
    · refine ⟨-z, k, hk, w, (neg_dvd.mpr hd), hlatest, hold, ?_⟩
      change f (-(z : R)) = _
      rw [map_neg, hp, neg_neg, hw']
  choose y k hk w h using H
  refine ⟨r, hr, y, k, w, tendsto_atTop_atTop.mpr (fun n => ⟨n, fun i hi => hi.trans (hk i).le⟩), h⟩

end UnconditionalCounterexample.Variations.TwoChainExtraction
