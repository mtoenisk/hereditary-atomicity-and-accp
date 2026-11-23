import UnconditionalCounterexample.Variations.SplitWeights

/-!
# Effective divisor profiles for splitting the two heights

The splitting construction puts all old channel-zero fibres into a prospective factor,
and leaves the old channel-one fibres to the cofactor. A balanced column
at the reserved index and binary tail corrections then give the required
masses without exceeding the available valuations.
-/

namespace UnconditionalCounterexample.DyadicSplit

open DyadicProfiles

/-- Value of a single unit correction at a selected index. -/
private def digit (s : Finset ℕ) (i : ℕ) : ℕ := if i ∈ s then 1 else 0

/-- The regular part of the factor with heights `(r,0)`. -/
def splitProfile (p : Profile) (M N : ℕ) : Profile where
  height k := if k then 0 else p.height false
  cutoff := N
  plus k i := if i < N then
      if k then digit {M} i
      else p.plus false i - digit (correctionSites N (p.height true)) i
    else p.height false
  minus k i := if i < N then
      if k then digit {M} i + digit (correctionSites N (p.height false)) i
      else p.minus false i
    else 0
  plus_stable _ _ hi := by simp [Nat.not_lt.mpr hi]
  minus_stable _ _ hi := by simp [Nat.not_lt.mpr hi]

private theorem digit_le_one (s : Finset ℕ) (i : ℕ) : digit s i ≤ 1 := by
  unfold digit
  split <;> omega

private theorem sum_digits {s : Finset ℕ} {N : ℕ} (hs : ∀ i ∈ s, i < N) :
    (∑ i ∈ Finset.range N, weight i * (digit s i : ℚ)) = ∑ i ∈ s, weight i := by
  classical
  calc
    _ = ∑ i ∈ s, weight i * (digit s i : ℚ) := by
      symm
      apply Finset.sum_subset (fun i hi => Finset.mem_range.mpr (hs i hi))
      intro i _ hi
      simp [digit, hi]
    _ = _ := Finset.sum_congr rfl (fun i hi => by simp [digit, hi])

private theorem leftDigit_le (p : Profile) {M N : ℕ} (hM : p.cutoff ≤ M)
    (hN : M + 1 + p.height true ≤ N) (hr : 0 < p.height false) (i : ℕ) :
    digit (correctionSites N (p.height true)) i ≤ p.plus false i := by
  by_cases hi : i ∈ correctionSites N (p.height true)
  · have h := correctionSites_bounds hN hi
    rw [p.plus_stable false i (by omega)]
    exact (digit_le_one _ _).trans hr
  · simp [digit, hi]

/-- All four regular sequences fit below the dividend. In particular the
reserved balanced column and the binary corrections never compete for the
same unit of the minus sequence. -/
theorem splitProfile_below (p : Profile) {M N : ℕ} (hM : p.cutoff ≤ M)
    (hN : M + 1 + max (p.height false) (p.height true) ≤ N)
    (hr : 0 < p.height false) (hs : 0 < p.height true) :
    (splitProfile p M N).Below p := by
  have hcut : p.cutoff ≤ N := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro k
    cases k <;> simp [splitProfile]
  · intro k i
    by_cases hi : i < N
    · cases k
      · simp [splitProfile, hi]
      · by_cases heq : i = M
        · subst i
          simpa [splitProfile, hi, digit, p.plus_stable true M hM] using (show 1 ≤ p.height false by omega)
        · simp [splitProfile, hi, digit, heq]
    · simp [splitProfile, hi, p.plus_stable k i (by omega)]
  · intro k i
    by_cases hi : i < N
    · cases k
      · simp [splitProfile, hi]
      · by_cases hc : i ∈ correctionSites N (p.height false)
        · have hb := correctionSites_bounds (show M + 1 + p.height false ≤ N by omega) hc
          have hne : i ≠ M := by omega
          simpa [splitProfile, hi, digit, hc, hne, p.minus_stable true i (by omega)] using (show 1 ≤ p.height true by omega)
        · by_cases heq : i = M
          · subst i
            simpa [splitProfile, hi, digit, hc, p.minus_stable true M hM] using (show 1 ≤ p.height true by omega)
          · simp [splitProfile, hi, digit, hc, heq]
    · simp [splitProfile, hi]

/-- Previously frozen regular sites are assigned by their whole channel. -/
theorem splitProfile_before (p : Profile) {M N i : ℕ}
    (hN : M + 1 + max (p.height false) (p.height true) ≤ N) (hi : i < M) :
    let u := splitProfile p M N
    u.plus false i = p.plus false i ∧ u.minus false i = p.minus false i ∧
      u.plus true i = 0 ∧ u.minus true i = 0 := by
  have outside (k : Bool) : i ∉ correctionSites N (p.height k) := by
    intro hc
    have hb : M + 1 + p.height k ≤ N := by cases k <;> omega
    have := correctionSites_bounds hb hc
    omega
  simp [splitProfile, digit, show i < N by omega, outside, ne_of_lt hi]

/-- The channel-one balanced column has coefficient one in the reserved slot. -/
theorem splitProfile_reserved (p : Profile) {M N : ℕ}
    (hN : M + 1 + max (p.height false) (p.height true) ≤ N) :
    (splitProfile p M N).plus true M = 1 ∧ (splitProfile p M N).minus true M = 1 := by
  have h : M ∉ correctionSites N (p.height false) := by
    intro hc
    have := correctionSites_bounds (show M + 1 + p.height false ≤ N by omega) hc
    omega
  simp [splitProfile, digit, h, show M < N by omega]

/-- Channel zero retains its entire original signed mass. Channel one's
signed mass vanishes. Supplementary fibres can therefore be assigned in
the same way as in the initial whole-channel partition. -/
theorem splitProfile_masses (p : Profile) {M N : ℕ} (hM : p.cutoff ≤ M)
    (hN : M + 1 + max (p.height false) (p.height true) ≤ N)
    (hr : 0 < p.height false) :
    (splitProfile p M N).signedMass false = p.signedMass false ∧
    (splitProfile p M N).signedMass true = 0 := by
  have hR : M + 1 + p.height false ≤ N := by omega
  have hS : M + 1 + p.height true ≤ N := by omega
  have corr (k : Bool) :
      (∑ i ∈ Finset.range N, weight i * (digit (correctionSites N (p.height k)) i : ℚ)) =
        tailWeight N * p.height k := by
    have hk : M + 1 + p.height k ≤ N := by cases k <;> omega
    rw [sum_digits (fun _ hi => (correctionSites_bounds hk hi).2),
      sum_correctionSites _ _ (by omega)]
  have diff0 (i : ℕ) (hi : i < N) :
      (splitProfile p M N).difference false i =
        p.difference false i - digit (correctionSites N (p.height true)) i := by
    simp only [Profile.difference, splitProfile, hi, ite_true, Bool.false_eq_true,
      ite_false, Nat.cast_sub (leftDigit_le p hM hS hr i)]
    ring
  have diff1 (i : ℕ) (hi : i < N) :
      (splitProfile p M N).difference true i =
        -(digit (correctionSites N (p.height false)) i : ℚ) := by
    simp [Profile.difference, splitProfile, hi]
  have hs0 :
      (∑ i ∈ Finset.range N, weight i * (splitProfile p M N).difference false i) =
        (∑ i ∈ Finset.range N, weight i * p.difference false i) -
          tailWeight N * p.height true := by
    rw [← corr true, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [diff0 i (Finset.mem_range.mp hi), mul_sub]
  have hs1 :
      (∑ i ∈ Finset.range N, weight i * (splitProfile p M N).difference true i) =
          -(tailWeight N * p.height false) := by
    rw [← corr false, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [diff1 i (Finset.mem_range.mp hi), mul_neg]
  have htail : (splitProfile p M N).tailDifference = p.height false := by
    simp [Profile.tailDifference, splitProfile]
  constructor
  · rw [p.signedMass_eq_of_le false (show p.cutoff ≤ N by omega)]
    change mass N _ _ = _
    rw [mass_eq_sum, mass_eq_sum, hs0, htail, Profile.tailDifference]
    ring
  · change mass N _ _ = _
    rw [mass_eq_sum, hs1, htail]
    ring

/-- The other factor inherits the unused valuations on every regular site. -/
def complement (p u : Profile) : Profile where
  height k := p.height k - u.height k
  plus k n := p.plus k n - u.plus k n
  minus k n := p.minus k n - u.minus k n
  cutoff := max p.cutoff u.cutoff
  plus_stable k n hn := by rw [p.plus_stable k n (by omega), u.plus_stable k n (by omega)]
  minus_stable k n hn := by rw [p.minus_stable k n (by omega), u.minus_stable k n (by omega)]

theorem complement_signedMass (p u : Profile) (hu : u.Below p) (k : Bool) :
    (complement p u).signedMass k = p.signedMass k - u.signedMass k := by
  let N := max p.cutoff u.cutoff
  have hd (i : ℕ) : (complement p u).difference k i = p.difference k i - u.difference k i := by
    simp only [Profile.difference, complement, Nat.cast_sub (hu.2.1 k i), Nat.cast_sub (hu.2.2 k i)]
    ring
  have ht : (complement p u).tailDifference = p.tailDifference - u.tailDifference := by
    simp only [Profile.tailDifference, complement, Nat.cast_sub (hu.1 false), Nat.cast_sub (hu.1 true)]
    ring
  rw [p.signedMass_eq_of_le k (le_max_left p.cutoff u.cutoff),
    u.signedMass_eq_of_le k (le_max_right p.cutoff u.cutoff)]
  change mass N _ _ = mass N _ _ - mass N _ _
  simp only [mass_eq_sum, hd, ht, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The two effective regular profiles required by a split task. The masses
and heights refer to the same partition of the dividend, also at every
frozen fibre and at the reserved balanced column. -/
theorem exists_split_profiles (p : Profile) (M : ℕ) (hM : p.cutoff ≤ M)
    (hr : 0 < p.height false) (hs : 0 < p.height true) :
    ∃ u v : Profile, u.Below p ∧
      u.height false = p.height false ∧ u.height true = 0 ∧
      v.height false = 0 ∧ v.height true = p.height true ∧
      (∀ k i, u.plus k i + v.plus k i = p.plus k i ∧
        u.minus k i + v.minus k i = p.minus k i) ∧
      u.signedMass false = p.signedMass false ∧ u.signedMass true = 0 ∧
      v.signedMass false = 0 ∧ v.signedMass true = p.signedMass true ∧
      (∀ i < M, u.plus false i = p.plus false i ∧ u.minus false i = p.minus false i ∧
        u.plus true i = 0 ∧ u.minus true i = 0) ∧
      u.plus true M = 1 ∧ u.minus true M = 1 := by
  let N := M + 1 + max (p.height false) (p.height true)
  let u := splitProfile p M N
  have hle : u.Below p := splitProfile_below p hM (by rfl) hr hs
  obtain ⟨h0, h1⟩ := splitProfile_masses p hM (N := N) (by rfl) hr
  refine ⟨u, complement p u, hle, rfl, rfl, ?_, ?_, ?_, h0, h1, ?_, ?_,
    fun _ hi => splitProfile_before p (by rfl) hi, splitProfile_reserved p (by rfl)⟩
  · simp [complement, u, splitProfile]
  · simp [complement, u, splitProfile]
  · intro k i
    exact ⟨Nat.add_sub_of_le (hle.2.1 k i), Nat.add_sub_of_le (hle.2.2 k i)⟩
  · rw [complement_signedMass _ _ hle, h0, sub_self]
  · rw [complement_signedMass _ _ hle, h1, sub_zero]

end UnconditionalCounterexample.DyadicSplit
