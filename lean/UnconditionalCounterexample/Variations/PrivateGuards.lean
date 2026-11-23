import UnconditionalCounterexample.DiscreteOrders
import UnconditionalCounterexample.RationalSigns

/-!
# Detecting auxiliary inverted factors at their private places

The ordinary and private evaluations above an auxiliary prime agree on constants.
Every normalized main generator is a unit at both places. At the largest index
occurring in an auxiliary word, all its earlier factors are units, so the
difference of the two additive orders reads off that last exponent.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.PrivateGuards

open DiscreteOrders PrincipalProfiles WithZero

variable {K I : Type*} [Field K]

/-- The ordinary and private valuation above each puncture's prime, and their
orders on its auxiliary factor and all previously chosen auxiliary factors. -/
structure Places (G : ℕ → K) where
  ordinary : ℕ → Valuation K ℤᵐ⁰
  auxiliary : ℕ → Valuation K ℤᵐ⁰
  private_self : ∀ j, order (auxiliary j) (G j) = 1
  ordinary_self : ∀ j, ordinary j (G j) = 1
  private_earlier : ∀ j k, k < j → auxiliary j (G k) = 1
  ordinary_earlier : ∀ j k, k < j → ordinary j (G k) = 1

variable {G : ℕ → K} (v : Places G)

private theorem value_word_at_last (w : Valuation K ℤᵐ⁰) (e : ℕ →₀ ℤ) {m : ℕ}
    (hm : ∀ k ∈ e.support, k ≤ m) (h : ∀ k, k < m → w (G k) = 1) :
    w (word G e) = w (G m) ^ e m := by
  classical
  rw [word, map_finsuppProd, Finsupp.prod]
  have hp : (∏ k ∈ e.support, w (G k ^ e k)) = w (G m ^ e m) := by
    apply Finset.prod_eq_single m
    · intro k hk hne
      rw [map_zpow₀, h k (lt_of_le_of_ne (hm k hk) hne), one_zpow]
    · intro hm'
      rw [Finsupp.notMem_support_iff.mp hm', zpow_zero, map_one]
  simpa only [Function.comp_apply, map_zpow₀] using hp

/-- At the last auxiliary factor occurring in a signed product, the actual
private-minus-ordinary order equals its exponent. Later factors are unrestricted. -/
theorem last_exponent (W : I → K) (a : I →₀ ℤ) (e : ℕ →₀ ℤ)
    {m : ℕ} (hm : ∀ k ∈ e.support, k ≤ m)
    {s : K} (hs : s ≠ 0) (hsame : v.auxiliary m s = v.ordinary m s)
    (hWpr : ∀ i, v.auxiliary m (W i) = 1) (hWord : ∀ i, v.ordinary m (W i) = 1) :
    order (v.auxiliary m) (s * word W a * word G e) -
      order (v.ordinary m) (s * word W a * word G e) = e m := by
  have hG : G m ≠ 0 := by
    intro hzero
    simpa [hzero] using v.ordinary_self m
  have hpr := value_word_at_last (v.auxiliary m) e hm (v.private_earlier m)
  have hor := value_word_at_last (v.ordinary m) e hm (v.ordinary_earlier m)
  have hval (w : Valuation K ℤᵐ⁰) (hw : ∀ i, w (W i) = 1)
      (hz : w (word G e) = w (G m) ^ e m) :
      order w (s * word W a * word G e) = order w s + e m * order w (G m) := by
    have hwv := RationalSigns.valuation_finsupp_prod_eq_one w W a hw
    have h :
        w (s * word W a * word G e) = w (s * G m ^ e m) := by
      rw [map_mul, map_mul, show w (word W a) = 1 from hwv, mul_one, hz, map_mul, map_zpow₀]
    calc
      _ = order w (s * G m ^ e m) := congrArg (fun t => -WithZero.log t) h
      _ = _ := by rw [order_mul w hs (zpow_ne_zero _ hG), order_zpow]
  rw [hval _ hWpr hpr, hval _ hWord hor, v.private_self,
    (order_eq_zero_iff _ hG).mpr (v.ordinary_self m)]
  have hs' : order (v.auxiliary m) s = order (v.ordinary m) s :=
    congrArg (fun x => -WithZero.log x) hsame
  rw [hs']
  ring

/-- Matching guard orders at every auxiliary prime eliminates the whole
finite signed auxiliary word. The main exponents can have either sign. -/
theorem eliminate (W : I → K) (a : I →₀ ℤ) (e : ℕ →₀ ℤ) {s x : K}
    (hs : s ≠ 0) (hx : x = s * word W a * word G e)
    (hsame : ∀ j, v.auxiliary j s = v.ordinary j s)
    (hWpr : ∀ j i, v.auxiliary j (W i) = 1) (hWord : ∀ j i, v.ordinary j (W i) = 1)
    (hguards : ∀ j, order (v.auxiliary j) x = order (v.ordinary j) x) :
    e = 0 ∧ x = s * word W a := by
  classical
  have he : e = 0 := by
    by_contra h
    have hn := Finsupp.support_nonempty_iff.mpr h
    let m := e.support.max' hn
    have hm : m ∈ e.support := Finset.max'_mem _ _
    have hlast := last_exponent v W a e (m := m) (fun _ hk => Finset.le_max' _ _ hk)
      hs (hsame m) (hWpr m) (hWord m)
    rw [← hx, hguards, sub_self] at hlast
    exact (Finsupp.mem_support_iff.mp hm) hlast.symm
  exact ⟨he, by simpa [he, word] using hx⟩

/-- When every ordinary guard is the ordinary rational valuation on constants,
the residual coefficient is a sign. These valuations can come from local
extensions of different degrees. -/
theorem signed_word [CharZero K] (W : I → K) (a : I →₀ ℤ) (e : ℕ →₀ ℤ)
    {c : ℚ} {x : K} (hc : c ≠ 0) (hx : x = (c : K) * word W a * word G e)
    (hsame : ∀ j, v.auxiliary j (c : K) = v.ordinary j (c : K))
    (hWpr : ∀ j i, v.auxiliary j (W i) = 1) (hWord : ∀ j i, v.ordinary j (W i) = 1)
    (hguards : ∀ j, order (v.auxiliary j) x = order (v.ordinary j) x)
    (ordinary : {p : ℕ // p.Prime} → Valuation K ℤᵐ⁰)
    (hscalar : ∀ p, ordinary p (c : K) = @Rat.padicValuation p.val ⟨p.property⟩ c)
    (hmain : ∀ p i, ordinary p (W i) = 1) (hunit : ∀ p, ordinary p x = 1) :
    e = 0 ∧ (x = word W a ∨ x = -word W a) := by
  obtain ⟨he, hred⟩ := eliminate v W a e (Rat.cast_ne_zero.mpr hc) hx hsame hWpr hWord hguards
  have hsign := RationalSigns.eq_one_or_neg_one_of_padic_eq_one c fun p => by
    have h := hunit p
    rw [hred, map_mul, show ordinary p (word W a) = 1 from
      RationalSigns.valuation_finsupp_prod_eq_one _ _ _ (hmain p), mul_one, hscalar] at h
    exact h
  refine ⟨he, ?_⟩
  rcases hsign with rfl | rfl
  · exact Or.inl (by simpa using hred)
  · exact Or.inr (by simpa using hred)

/-- Testing a growing enumeration of nonzero elements in a domain gives finite
private support for every nonzero element of its fraction field. -/
theorem finite_private_support (A : Type*) [CommRing A] [IsDomain A] [Algebra A K]
    [IsFractionRing A K] (w : ℕ → Valuation K ℤᵐ⁰) (test : ℕ → A)
    (hcovers : ∀ f : A, f ≠ 0 → ∃ i, test i = f)
    (hunit : ∀ j i, i ≤ j → w j (algebraMap A K (test i)) = 1)
    {x : K} (hx : x ≠ 0) : {j | w j x ≠ 1}.Finite := by
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective A x
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨i, hi⟩ := hcovers f hf
  obtain ⟨k, hk⟩ := hcovers g (nonZeroDivisors.ne_zero hg)
  refine (Finset.range (max i k) : Finset ℕ).finite_toSet.subset ?_
  intro j hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra! hle
  apply hj
  rw [map_div₀, ← hi, ← hk, hunit _ _ ((le_max_left _ _).trans hle),
    hunit _ _ ((le_max_right _ _).trans hle), div_one]

end UnconditionalCounterexample.Variations.PrivateGuards
