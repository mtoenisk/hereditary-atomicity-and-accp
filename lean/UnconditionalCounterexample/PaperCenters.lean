import UnconditionalCounterexample.PaperAtoms
import UnconditionalCounterexample.PaperSpectrum
import UnconditionalCounterexample.HorizontalPrimes
import UnconditionalCounterexample.ProfileBounds

/-!
# Centers of the actual primary, guard and retained horizontal valuations

The horizontal centers are proved nonzero and maximal using actual integer
clearing and the isolator separation theorem. Distinctness uses actual elements
of D, not a postulated list of maximal ideals.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperMaximalSpectrum
open Polynomial WithZero GuardSupport CompleteProfiles
open PaperConstruction IntersectionDomain IntersectionStalks

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

abbrev Vertical := ℕ ⊕ PrimeIndex
abbrev Horizontal := {p : PrincipalProfiles.MonicIrreducible ℚ // HorizontalOrders.Retained poles p}
abbrev Point := Vertical ⊕ Horizontal
abbrev Label := ProfilePlace (Outside poles)

private theorem retained_X : HorizontalOrders.Retained poles HorizontalOrders.xPoint :=
  HorizontalOrders.retained_xPoint_of_constantCoeff_ne_zero poles (fun _ => raw_constant)

/-- Relabel the complete actual profiles by vertical or horizontal places. -/
def label : Point → Label
  | .inl (.inl n) => .primary n
  | .inl (.inr p) => .outside (.inl p)
  | .inr p => if h : p.val = HorizontalOrders.xPoint then .limit
      else .outside (.inr ⟨p.val, p.property, h⟩)

def valuation (p : Point) : Valuation (RatFunc ℚ) ℤᵐ⁰ := valuations poles places (label p)

@[simp] theorem valuation_vertical (i : Vertical) : valuation (.inl i) = PairedDomain.vertical places i := by
  cases i <;> rfl

@[simp] theorem valuation_horizontal (p : Horizontal) : valuation (.inr p) = HorizontalOrders.valuation p.val := by
  simp only [valuation, label]
  split_ifs with hp
  · change HorizontalOrders.valuation HorizontalOrders.xPoint = _
    rw [hp]
  · rfl

/-- Inclusion of the actual domain into each actual valuation ring. -/
def inclusion (p : Point) : domain →+* (valuation p).valuationSubring where
  toFun x := ⟨x, CompleteProfiles.integral poles places (fun _ => raw_constant) x (label p)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The actual positive-value ideal at a named place. -/
def center (p : Point) : Ideal domain :=
  Ideal.comap (inclusion p) (IsLocalRing.maximalIdeal (valuation p).valuationSubring)

@[simp] theorem mem_center (p : Point) (x : domain) : x ∈ center p ↔ valuation p (x : RatFunc ℚ) < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

instance center_isPrime (p : Point) : (center p).IsPrime := by
  unfold center
  infer_instance

theorem center_vertical (i : Vertical) : center (.inl i) =
    IntersectionStalks.center (PoleAlgebra.generated poles).toSubring (PairedDomain.vertical places) i := by
  ext x
  rw [mem_center, IntersectionStalks.mem_center, valuation_vertical]

theorem vertical_isMaximal (i : Vertical) : (center (.inl i)).IsMaximal := by
  rw [center_vertical]
  exact PairedSpectrum.center_isMaximal poles places i

/-- An actual positive integer clears every fixed pole-algebra element into D. -/
theorem exists_nat_mul_mem (x : RatFunc ℚ) (hx : x ∈ PoleAlgebra.generated poles) :
    ∃ n : ℕ, 0 < n ∧ (n : RatFunc ℚ) * x ∈ domain := by
  apply IntersectionDomain.exists_nat_mul_mem_intersection _ (PairedDomain.vertical places)
    (Sum.elim (fun n => (places.primes n).val) Subtype.val)
  · rintro (n | p)
    · exact (places.primes n).property.pos
    · exact p.property.pos
  · rintro (n | p)
    · exact EvaluationDVR.valuation_prime _ _
    · exact EvaluationDVR.valuation_prime _ _
  · exact hx
  · exact PairedDomain.finite_nonintegral_of_guard_support places
      (fun _ => raw_constant) guardSupport x hx

/-- Integer clearing of the actual polynomial gives a nonzero horizontal center. -/
theorem horizontal_ne_bot (p : Horizontal) : center (.inr p) ≠ ⊥ := by
  obtain ⟨n, hn, hmem⟩ := exists_nat_mul_mem (PrincipalProfiles.factor p.val)
    (PoleAlgebra.polynomial_mem poles p.val.val)
  let x : domain := ⟨(n : RatFunc ℚ) * PrincipalProfiles.factor p.val, hmem⟩
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hval : valuation (.inr p) (x : RatFunc ℚ) = exp (-1 : ℤ) := by
    rw [valuation_horizontal]
    change HorizontalOrders.valuation p.val ((n : RatFunc ℚ) * PrincipalProfiles.factor p.val) = _
    rw [map_mul, HorizontalOrders.valuation_factor_self]
    have hc : (n : RatFunc ℚ) = RatFunc.C (n : ℚ) := by simp
    rw [hc, HorizontalOrders.valuation_constant p.val _ hn0, one_mul]
  have hx : x ∈ center (.inr p) := by
    rw [mem_center, hval, exp_lt_one_iff]
    norm_num
  have hx0 : x ≠ 0 := by
    intro hz
    have he : valuation (.inr p) (x : RatFunc ℚ) = 0 := by simp [hz]
    rw [hval] at he
    exact exp_ne_zero he
  intro hbot
  exact hx0 (by simpa [hbot] using hx)

/-- A horizontal center contains no nonzero integer denominator. -/
theorem horizontal_disjoint_integers (p : Horizontal) :
    Disjoint (integerDenominators domain : Set domain) (center (.inr p) : Set domain) := by
  apply Set.disjoint_left.mpr
  intro x hx hxc
  obtain ⟨z, hz, rfl⟩ := hx
  have hz0 : z ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hz
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast hz0
  have h : valuation (.inr p) (z : RatFunc ℚ) < 1 := (mem_center _ _).mp hxc
  rw [valuation_horizontal] at h
  have hc : (z : RatFunc ℚ) = RatFunc.C (z : ℚ) := by simp
  rw [hc, HorizontalOrders.valuation_constant _ _ hzQ] at h
  exact lt_irrefl _ h

/-- Every retained polynomial has a genuinely maximal horizontal center in D. -/
theorem horizontal_isMaximal (p : Horizontal) : (center (.inr p)).IsMaximal := by
  let := PaperConstruction.integerLocalization
  have hn : ∀ q ∈ poles, q ≠ 0 := by
    intro q hq hz
    exact raw_constant hq (by simp [hz])
  let := IntersectionSpectrum.poleAlgebra_isDedekindDomain poles hn
  apply IntersectionSpectrum.horizontal_isMaximal (PoleAlgebra.generated poles).toSubring
    (PairedDomain.vertical places)
    (fun p => .inl (places.primes.symm p)) (fun p => .inr p)
    (PairedSpectrum.center_isMaximal poles places)
    (PairedSpectrum.paired_radicals raw exponent places generatorProfiles.b generatorProfiles.q generatorProfiles.guard)
    ?_ (center (.inr p)) (horizontal_ne_bot p) (horizontal_disjoint_integers p)
  intro i
  obtain ⟨f, hi, hf, ho⟩ := PairedSpectrum.vertical_isolators raw exponent places
    generatorProfiles.b generatorProfiles.q generatorProfiles.guard i
  exact ⟨f, 3, by decide, hi, hf, ho⟩

theorem center_isMaximal (p : Point) : (center p).IsMaximal := by
  cases p with
  | inl i => exact vertical_isMaximal i
  | inr p => exact horizontal_isMaximal p

/-- Every vertical center is separated from every other by an actual singleton isolator. -/
theorem vertical_center_injective : Function.Injective (fun i : Vertical => center (.inl i)) := by
  intro i j hij
  dsimp only at hij
  by_contra hne
  obtain ⟨f, _, hfi, hfother⟩ := PairedSpectrum.vertical_isolators raw exponent places
    generatorProfiles.b generatorProfiles.q generatorProfiles.guard i
  have hfin : f ∈ center (.inl i) := by
    rw [mem_center, valuation_vertical, hfi, exp_lt_one_iff]
    norm_num
  rw [hij, mem_center, valuation_vertical, hfother j (Ne.symm hne)] at hfin
  exact lt_irrefl _ hfin

/-- A nonzero rational prime lies in each vertical center, excluding every horizontal center. -/
theorem vertical_ne_horizontal (i : Vertical) (p : Horizontal) : center (.inl i) ≠ center (.inr p) := by
  let q : PrimeIndex := Sum.elim places.primes id i
  have hq : PairedDomain.vertical places i (q.val : RatFunc ℚ) = exp (-1 : ℤ) := by
    cases i with
    | inl n => exact EvaluationDVR.valuation_prime _ _
    | inr q => exact EvaluationDVR.valuation_prime _ _
  have hmem : (q.val : domain) ∈ center (.inl i) := by
    rw [mem_center, valuation_vertical]
    change PairedDomain.vertical places i (q.val : RatFunc ℚ) < 1
    rw [hq, exp_lt_one_iff]
    norm_num
  have hden : (q.val : domain) ∈ integerDenominators domain := by
    refine ⟨(q.val : ℤ), ?_, ?_⟩
    · exact mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast q.property.ne_zero)
    · simp
  intro heq
  rw [heq] at hmem
  exact Set.disjoint_left.mp (horizontal_disjoint_integers p) hden hmem

/-- Clearing one defining polynomial separates distinct horizontal centers inside D. -/
theorem horizontal_center_injective : Function.Injective (fun p : Horizontal => center (.inr p)) := by
  intro p q heq
  dsimp only at heq
  by_contra hpq
  have hqp : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  obtain ⟨n, hn, hmem⟩ := exists_nat_mul_mem (PrincipalProfiles.factor p.val)
    (PoleAlgebra.polynomial_mem poles p.val.val)
  let x : domain := ⟨(n : RatFunc ℚ) * PrincipalProfiles.factor p.val, hmem⟩
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (n : RatFunc ℚ) = RatFunc.C (n : ℚ) := by simp
  have hxmem : x ∈ center (.inr p) := by
    rw [mem_center, valuation_horizontal]
    change HorizontalOrders.valuation p.val ((n : RatFunc ℚ) * PrincipalProfiles.factor p.val) < 1
    rw [map_mul, hc, HorizontalOrders.valuation_constant _ _ hn0,
      HorizontalOrders.valuation_factor_self, one_mul, exp_lt_one_iff]
    norm_num
  rw [heq, mem_center, valuation_horizontal] at hxmem
  change HorizontalOrders.valuation q.val ((n : RatFunc ℚ) * PrincipalProfiles.factor p.val) < 1 at hxmem
  rw [map_mul, hc, HorizontalOrders.valuation_constant _ _ hn0,
    HorizontalOrders.valuation_factor_of_ne q.val p.val hqp, one_mul] at hxmem
  exact lt_irrefl _ hxmem

theorem center_injective : Function.Injective center := by
  intro p q heq
  cases p with
  | inl i =>
    cases q with
    | inl j => exact congrArg Sum.inl (vertical_center_injective heq)
    | inr q => exact False.elim (vertical_ne_horizontal i q heq)
  | inr p =>
    cases q with
    | inl j => exact False.elim (vertical_ne_horizontal j p heq.symm)
    | inr q => exact congrArg Sum.inr (horizontal_center_injective heq)

/-- Inverse relabeling, with the X prime singled out as the limit coordinate. -/
def pointOfLabel : Label → Point
  | .limit => .inr ⟨HorizontalOrders.xPoint, retained_X⟩
  | .primary n => .inl (.inl n)
  | .outside (.inl p) => .inl (.inr p)
  | .outside (.inr p) => .inr ⟨p.val, p.property.1⟩

@[simp] theorem pointOfLabel_label (p : Point) : pointOfLabel (label p) = p := by
  rcases p with (n | q) | p
  · rfl
  · rfl
  · simp only [label]
    split_ifs with hp
    · change Sum.inr _ = Sum.inr p
      congr 1
      exact Subtype.ext hp.symm
    · rfl

@[simp] theorem label_pointOfLabel (p : Label) : label (pointOfLabel p) = p := by
  cases p with
  | limit => simp [pointOfLabel, label]
  | primary n => rfl
  | outside i =>
    cases i with
    | inl p => rfl
    | inr p => simp only [pointOfLabel, label, dite_eq_right p.property.2]

/-- Exact identification of the ideal-place index with the existing actual profile index. -/
def pointEquivLabel : Point ≃ Label where
  toFun := label
  invFun := pointOfLabel
  left_inv := pointOfLabel_label
  right_inv := label_pointOfLabel

private theorem poles_ne_zero : ∀ q ∈ poles, q ≠ 0 := by
  intro q hq hz
  exact raw_constant hq (by simp [hz])

/-- A named horizontal center is exactly the contraction of its actual center in B. -/
theorem horizontal_center_under (p : Horizontal) :
    (HorizontalPrimes.center poles poles_ne_zero p.val p.property).under domain = center (.inr p) := by
  ext x
  rw [Ideal.mem_under, HorizontalPrimes.mem_center, mem_center, valuation_horizontal]
  rfl

/-- Every maximal ideal of D has exactly one vertical or retained horizontal name. -/
theorem exists_center_of_maximal (M : Ideal domain) [M.IsMaximal] : ∃ p : Point, center p = M := by
  let := PaperConstruction.integerLocalization
  obtain ⟨f, _, hfi, _⟩ := PairedSpectrum.vertical_isolators raw exponent places
    generatorProfiles.b generatorProfiles.q generatorProfiles.guard (.inl 0)
  have hM0 : M ≠ ⊥ := IntersectionSpectrum.maximal_ne_bot_of_isolator
    (PoleAlgebra.generated poles).toSubring (PairedDomain.vertical places) (.inl 0)
    f 3 (by decide) hfi M
  rcases IntersectionSpectrum.prime_vertical_or_disjoint
      (PoleAlgebra.generated poles).toSubring (PairedDomain.vertical places)
      (fun p => .inl (places.primes.symm p)) (fun p => .inr p)
      (PairedSpectrum.center_isMaximal poles places)
      (PairedSpectrum.paired_radicals raw exponent places
        generatorProfiles.b generatorProfiles.q generatorProfiles.guard) M with ⟨i, hi⟩ | hdis
  · exact ⟨.inl i, (center_vertical i).trans hi.symm⟩
  · have hQ := IntersectionSpectrum.horizontal_extension
      (PoleAlgebra.generated poles).toSubring (PairedDomain.vertical places) M hdis
    let := hQ.1
    have hQ0 := IntersectionSpectrum.horizontal_extension_ne_bot
      (PoleAlgebra.generated poles).toSubring (PairedDomain.vertical places) M hM0
    obtain ⟨p, hp, hQp⟩ := HorizontalPrimes.exists_center_of_prime poles poles_ne_zero
      (M.map (algebraMap domain (PoleAlgebra.generated poles))) hQ0
    refine ⟨.inr ⟨p, hp⟩, ?_⟩
    rw [← horizontal_center_under, ← hQp]
    exact hQ.2

abbrev Maximal := {M : Ideal domain // M.IsMaximal}

/-- The exact bijection with all maximal ideals, not merely a covering list. -/
def pointEquivMaximal : Point ≃ Maximal := Equiv.ofBijective
  (fun p => ⟨center p, center_isMaximal p⟩) (by
    constructor
    · intro p q hpq
      exact center_injective (congrArg Subtype.val hpq)
    · intro M
      let := M.property
      obtain ⟨p, hp⟩ := exists_center_of_maximal M.val
      exact ⟨p, Subtype.ext hp⟩)

@[simp] theorem pointEquivMaximal_val (p : Point) : (pointEquivMaximal p).val = center p := rfl

/-- The existing complete profile labels identify bijectively with the actual maximal ideals. -/
def labelEquivMaximal : Label ≃ Maximal := pointEquivLabel.symm.trans pointEquivMaximal

/-- Actual principal order, now indexed by every maximal ideal. -/
def order (M : Maximal) (x : domain) : ℕ :=
  PaperConstruction.valuationProfiles.value (labelEquivMaximal.symm M) x

@[simp] theorem order_label (p : Label) (x : domain) :
    order (labelEquivMaximal p) x = PaperConstruction.valuationProfiles.value p x := by
  simp [order]

theorem order_bounded (x : domain) (hx : x ≠ 0) : ∃ N : ℕ, ∀ M : Maximal, order M x ≤ N := by
  obtain ⟨N, hN⟩ := PaperConstruction.valuationProfiles.exists_all_coordinate_bound x hx
  exact ⟨N, fun M => hN (labelEquivMaximal.symm M)⟩

end UnconditionalCounterexample.PaperMaximalSpectrum
