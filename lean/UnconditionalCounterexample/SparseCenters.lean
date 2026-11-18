import UnconditionalCounterexample.SparseProfileData
import UnconditionalCounterexample.SparseSpectrum
import UnconditionalCounterexample.HorizontalPrimes
import UnconditionalCounterexample.ProfileBounds

/-!
# Centers of the actual primary, guard and retained horizontal valuations

The horizontal centers are proved nonzero and maximal using actual integer
clearing and the isolator separation theorem. Distinctness uses actual elements
of D, not a postulated list of maximal ideals.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseMaximalSpectrum
open Polynomial WithZero GuardSupport SparseProfiles SparseProfileData
open IntersectionDomain IntersectionStalks

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (A : Data)

abbrev realizedProfiles := A.profiles

abbrev Vertical := ℕ ⊕ PrimeIndex
abbrev Horizontal := {p : PrincipalProfiles.MonicIrreducible ℚ // HorizontalOrders.Retained A.poles p}
abbrev Point := Vertical ⊕ (Horizontal A)
abbrev Label := ProfilePlace (Outside A.poles)

private theorem retained_X : HorizontalOrders.Retained A.poles HorizontalOrders.xPoint :=
  HorizontalOrders.retained_xPoint_of_constantCoeff_ne_zero A.poles A.constant_nonzero

/-- Relabel the complete actual profiles by vertical or horizontal A.places. -/
def label : (Point A) → (Label A)
  | .inl (.inl n) => .primary n
  | .inl (.inr p) => .outside (.inl p)
  | .inr p => if h : p.val = HorizontalOrders.xPoint then .limit
      else .outside (.inr ⟨p.val, p.property, h⟩)

def valuation (p : (Point A)) : Valuation (RatFunc ℚ) ℤᵐ⁰ := valuations A.poles A.places ((label A) p)

@[simp] theorem valuation_vertical (i : Vertical) : (valuation A) (.inl i) = SparsePrimaryDomain.vertical A.places i := by
  cases i <;> rfl

@[simp] theorem valuation_horizontal (p : (Horizontal A)) : (valuation A) (.inr p) = HorizontalOrders.valuation p.val := by
  simp only [valuation, label]
  split_ifs with hp
  · change HorizontalOrders.valuation HorizontalOrders.xPoint = _
    rw [hp]
  · rfl

/-- Inclusion of the actual A.domain into each actual (valuation A) ring. -/
def inclusion (p : (Point A)) : A.domain →+* ((valuation A) p).valuationSubring where
  toFun x := ⟨x, SparseProfiles.integral A.poles A.places A.constant_nonzero x ((label A) p)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The actual positive-value ideal at a named place. -/
def center (p : (Point A)) : Ideal A.domain :=
  Ideal.comap ((inclusion A) p) (IsLocalRing.maximalIdeal ((valuation A) p).valuationSubring)

@[simp] theorem mem_center (p : (Point A)) (x : A.domain) : x ∈ (center A) p ↔ (valuation A) p (x : RatFunc ℚ) < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

instance center_isPrime (p : (Point A)) : ((center A) p).IsPrime := by
  unfold center
  infer_instance

theorem center_vertical (i : Vertical) : (center A) (.inl i) =
    IntersectionStalks.center (PoleAlgebra.generated A.poles).toSubring (SparsePrimaryDomain.vertical A.places) i := by
  ext x
  rw [(mem_center A), IntersectionStalks.mem_center, (valuation_vertical A)]

theorem vertical_isMaximal (i : Vertical) : ((center A) (.inl i)).IsMaximal := by
  rw [(center_vertical A)]
  exact SparseSpectrum.center_isMaximal A.poles A.places i

/-- An actual positive integer clears every fixed pole-algebra element into D. -/
theorem exists_nat_mul_mem (x : RatFunc ℚ) (hx : x ∈ PoleAlgebra.generated A.poles) :
    ∃ n : ℕ, 0 < n ∧ (n : RatFunc ℚ) * x ∈ A.domain := by
  apply IntersectionDomain.exists_nat_mul_mem_intersection _ (SparsePrimaryDomain.vertical A.places)
    (Sum.elim (fun n => (A.places.primes n).val) Subtype.val)
  · rintro (n | p)
    · exact (A.places.primes n).property.pos
    · exact p.property.pos
  · rintro (n | p)
    · exact EvaluationDVR.valuation_prime _ _
    · exact EvaluationDVR.valuation_prime _ _
  · exact hx
  · exact SparsePrimaryDomain.finite_nonintegral_of_guard_support A.places
      A.constant_nonzero A.guardSupport x hx

/-- Integer clearing of the actual polynomial gives a nonzero horizontal (center A). -/
theorem horizontal_ne_bot (p : (Horizontal A)) : (center A) (.inr p) ≠ ⊥ := by
  obtain ⟨n, hn, hmem⟩ := (exists_nat_mul_mem A) (PrincipalProfiles.factor p.val)
    (PoleAlgebra.polynomial_mem A.poles p.val.val)
  let x : A.domain := ⟨(n : RatFunc ℚ) * PrincipalProfiles.factor p.val, hmem⟩
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hval : (valuation A) (.inr p) (x : RatFunc ℚ) = exp (-1 : ℤ) := by
    rw [(valuation_horizontal A)]
    change HorizontalOrders.valuation p.val ((n : RatFunc ℚ) * PrincipalProfiles.factor p.val) = _
    rw [map_mul, HorizontalOrders.valuation_factor_self]
    have hc : (n : RatFunc ℚ) = RatFunc.C (n : ℚ) := by simp
    rw [hc, HorizontalOrders.valuation_constant p.val _ hn0, one_mul]
  have hx : x ∈ (center A) (.inr p) := by
    rw [(mem_center A), hval, exp_lt_one_iff]
    norm_num
  have hx0 : x ≠ 0 := by
    intro hz
    have he : (valuation A) (.inr p) (x : RatFunc ℚ) = 0 := by simp [hz]
    rw [hval] at he
    exact exp_ne_zero he
  intro hbot
  exact hx0 (by simpa [hbot] using hx)

/-- A horizontal (center A) contains no nonzero integer denominator. -/
theorem horizontal_disjoint_integers (p : (Horizontal A)) :
    Disjoint (integerDenominators A.domain : Set A.domain) ((center A) (.inr p) : Set A.domain) := by
  apply Set.disjoint_left.mpr
  intro x hx hxc
  obtain ⟨z, hz, rfl⟩ := hx
  have hz0 : z ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hz
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast hz0
  have h : (valuation A) (.inr p) (z : RatFunc ℚ) < 1 := ((mem_center A) _ _).mp hxc
  rw [(valuation_horizontal A)] at h
  have hc : (z : RatFunc ℚ) = RatFunc.C (z : ℚ) := by simp
  rw [hc, HorizontalOrders.valuation_constant _ _ hzQ] at h
  exact lt_irrefl _ h

/-- Every retained polynomial has a genuinely maximal horizontal (center A) in D. -/
theorem horizontal_isMaximal (p : (Horizontal A)) : ((center A) (.inr p)).IsMaximal := by
  let := (SparsePrimaryDomain.integerLocalization_of_guard_support A.places A.constant_nonzero A.guardSupport)
  have hn : ∀ q ∈ A.poles, q ≠ 0 := by
    intro q hq hz
    exact A.constant_nonzero q hq (by simp [hz])
  let := IntersectionSpectrum.poleAlgebra_isDedekindDomain A.poles hn
  apply IntersectionSpectrum.horizontal_isMaximal (PoleAlgebra.generated A.poles).toSubring
    (SparsePrimaryDomain.vertical A.places)
    (SparseSpectrum.firstCenter A.places) (fun p => .inr p)
    (SparseSpectrum.center_isMaximal A.poles A.places)
    (SparseSpectrum.paired_radicals A.raw A.exponent A.places A.columns.b A.columns.q A.columns.guard)
    ?_ ((center A) (.inr p)) ((horizontal_ne_bot A) p) ((horizontal_disjoint_integers A) p)
  intro i
  obtain ⟨f, k, hk, hi, hf, ho⟩ := SparseSpectrum.vertical_isolators A.raw A.exponent A.places
    A.columns.b A.columns.q A.columns.guard i
  exact ⟨f, k, hk, hi, hf, ho⟩

theorem center_isMaximal (p : (Point A)) : ((center A) p).IsMaximal := by
  cases p with
  | inl i => exact (vertical_isMaximal A) i
  | inr p => exact (horizontal_isMaximal A) p

/-- Every vertical (center A) is separated from every other by an actual singleton isolator. -/
theorem vertical_center_injective : Function.Injective (fun i : Vertical => (center A) (.inl i)) := by
  intro i j hij
  dsimp only at hij
  by_contra hne
  obtain ⟨f, k, hk, _, hfi, hfother⟩ := SparseSpectrum.vertical_isolators A.raw A.exponent A.places
    A.columns.b A.columns.q A.columns.guard i
  have hfin : f ∈ (center A) (.inl i) := by
    rw [(mem_center A), (valuation_vertical A), hfi, exp_lt_one_iff]
    exact neg_neg_of_pos (by exact_mod_cast hk)
  rw [hij, (mem_center A), (valuation_vertical A), hfother j (Ne.symm hne)] at hfin
  exact lt_irrefl _ hfin

/-- A nonzero rational prime lies in each vertical (center A), excluding every horizontal (center A). -/
theorem vertical_ne_horizontal (i : Vertical) (p : (Horizontal A)) : (center A) (.inl i) ≠ (center A) (.inr p) := by
  let q : PrimeIndex := Sum.elim A.places.primes id i
  have hq : SparsePrimaryDomain.vertical A.places i (q.val : RatFunc ℚ) = exp (-1 : ℤ) := by
    cases i with
    | inl n => exact EvaluationDVR.valuation_prime _ _
    | inr q => exact EvaluationDVR.valuation_prime _ _
  have hmem : (q.val : A.domain) ∈ (center A) (.inl i) := by
    rw [(mem_center A), (valuation_vertical A)]
    change SparsePrimaryDomain.vertical A.places i (q.val : RatFunc ℚ) < 1
    rw [hq, exp_lt_one_iff]
    norm_num
  have hden : (q.val : A.domain) ∈ integerDenominators A.domain := by
    refine ⟨(q.val : ℤ), ?_, ?_⟩
    · exact mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast q.property.ne_zero)
    · simp
  intro heq
  rw [heq] at hmem
  exact Set.disjoint_left.mp ((horizontal_disjoint_integers A) p) hden hmem

/-- Clearing one defining polynomial separates distinct horizontal centers inside D. -/
theorem horizontal_center_injective : Function.Injective (fun p : (Horizontal A) => (center A) (.inr p)) := by
  intro p q heq
  dsimp only at heq
  by_contra hpq
  have hqp : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  obtain ⟨n, hn, hmem⟩ := (exists_nat_mul_mem A) (PrincipalProfiles.factor p.val)
    (PoleAlgebra.polynomial_mem A.poles p.val.val)
  let x : A.domain := ⟨(n : RatFunc ℚ) * PrincipalProfiles.factor p.val, hmem⟩
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (n : RatFunc ℚ) = RatFunc.C (n : ℚ) := by simp
  have hxmem : x ∈ (center A) (.inr p) := by
    rw [(mem_center A), (valuation_horizontal A)]
    change HorizontalOrders.valuation p.val ((n : RatFunc ℚ) * PrincipalProfiles.factor p.val) < 1
    rw [map_mul, hc, HorizontalOrders.valuation_constant _ _ hn0,
      HorizontalOrders.valuation_factor_self, one_mul, exp_lt_one_iff]
    norm_num
  rw [heq, (mem_center A), (valuation_horizontal A)] at hxmem
  change HorizontalOrders.valuation q.val ((n : RatFunc ℚ) * PrincipalProfiles.factor p.val) < 1 at hxmem
  rw [map_mul, hc, HorizontalOrders.valuation_constant _ _ hn0,
    HorizontalOrders.valuation_factor_of_ne q.val p.val hqp, one_mul] at hxmem
  exact lt_irrefl _ hxmem

theorem center_injective : Function.Injective (center A) := by
  intro p q heq
  cases p with
  | inl i =>
    cases q with
    | inl j => exact congrArg Sum.inl ((vertical_center_injective A) heq)
    | inr q => exact False.elim ((vertical_ne_horizontal A) i q heq)
  | inr p =>
    cases q with
    | inl j => exact False.elim ((vertical_ne_horizontal A) j p heq.symm)
    | inr q => exact congrArg Sum.inr ((horizontal_center_injective A) heq)

/-- Inverse relabeling, with the X prime singled out as the limit coordinate. -/
def pointOfLabel : (Label A) → (Point A)
  | .limit => .inr ⟨HorizontalOrders.xPoint, (retained_X A)⟩
  | .primary n => .inl (.inl n)
  | .outside (.inl p) => .inl (.inr p)
  | .outside (.inr p) => .inr ⟨p.val, p.property.1⟩

@[simp] theorem pointOfLabel_label (p : (Point A)) : (pointOfLabel A) ((label A) p) = p := by
  rcases p with (n | q) | p
  · rfl
  · rfl
  · simp only [label]
    split_ifs with hp
    · change Sum.inr _ = Sum.inr p
      congr 1
      exact Subtype.ext hp.symm
    · rfl

@[simp] theorem label_pointOfLabel (p : (Label A)) : (label A) ((pointOfLabel A) p) = p := by
  cases p with
  | limit => simp [pointOfLabel, label]
  | primary n => rfl
  | outside i =>
    cases i with
    | inl p => rfl
    | inr p => simp only [pointOfLabel, label, dite_eq_right p.property.2]

/-- Exact identification of the ideal-place index with the existing actual profile index. -/
def pointEquivLabel : (Point A) ≃ (Label A) where
  toFun := (label A)
  invFun := (pointOfLabel A)
  left_inv := (pointOfLabel_label A)
  right_inv := (label_pointOfLabel A)

private theorem poles_ne_zero : ∀ q ∈ A.poles, q ≠ 0 := by
  intro q hq hz
  exact A.constant_nonzero q hq (by simp [hz])

/-- A named horizontal (center A) is exactly the contraction of its actual (center A) in B. -/
theorem horizontal_center_under (p : (Horizontal A)) :
    (HorizontalPrimes.center A.poles (poles_ne_zero A) p.val p.property).under A.domain = (center A) (.inr p) := by
  ext x
  rw [Ideal.mem_under, HorizontalPrimes.mem_center, (mem_center A), (valuation_horizontal A)]
  rfl

/-- Every maximal ideal of D has exactly one vertical or retained horizontal name. -/
theorem exists_center_of_maximal (M : Ideal A.domain) [M.IsMaximal] : ∃ p : (Point A), (center A) p = M := by
  let := (SparsePrimaryDomain.integerLocalization_of_guard_support A.places A.constant_nonzero A.guardSupport)
  obtain ⟨f, k, hk, _, hfi, _⟩ := SparseSpectrum.vertical_isolators A.raw A.exponent A.places
    A.columns.b A.columns.q A.columns.guard (.inl 0)
  have hM0 : M ≠ ⊥ := IntersectionSpectrum.maximal_ne_bot_of_isolator
    (PoleAlgebra.generated A.poles).toSubring (SparsePrimaryDomain.vertical A.places) (.inl 0)
    f k hk hfi M
  rcases IntersectionSpectrum.prime_vertical_or_disjoint
      (PoleAlgebra.generated A.poles).toSubring (SparsePrimaryDomain.vertical A.places)
      (SparseSpectrum.firstCenter A.places) (fun p => .inr p)
      (SparseSpectrum.center_isMaximal A.poles A.places)
      (SparseSpectrum.paired_radicals A.raw A.exponent A.places
        A.columns.b A.columns.q A.columns.guard) M with ⟨i, hi⟩ | hdis
  · exact ⟨.inl i, ((center_vertical A) i).trans hi.symm⟩
  · have hQ := IntersectionSpectrum.horizontal_extension
      (PoleAlgebra.generated A.poles).toSubring (SparsePrimaryDomain.vertical A.places) M hdis
    let := hQ.1
    have hQ0 := IntersectionSpectrum.horizontal_extension_ne_bot
      (PoleAlgebra.generated A.poles).toSubring (SparsePrimaryDomain.vertical A.places) M hM0
    obtain ⟨p, hp, hQp⟩ := HorizontalPrimes.exists_center_of_prime A.poles (poles_ne_zero A)
      (M.map (algebraMap A.domain (PoleAlgebra.generated A.poles))) hQ0
    refine ⟨.inr ⟨p, hp⟩, ?_⟩
    rw [← (horizontal_center_under A), ← hQp]
    exact hQ.2

abbrev Maximal := {M : Ideal A.domain // M.IsMaximal}

/-- The exact bijection with all maximal ideals, not merely a covering list. -/
def pointEquivMaximal : (Point A) ≃ (Maximal A) := Equiv.ofBijective
  (fun p => ⟨(center A) p, (center_isMaximal A) p⟩) (by
    constructor
    · intro p q hpq
      exact (center_injective A) (congrArg Subtype.val hpq)
    · intro M
      let := M.property
      obtain ⟨p, hp⟩ := (exists_center_of_maximal A) M.val
      exact ⟨p, Subtype.ext hp⟩)

@[simp] theorem pointEquivMaximal_val (p : (Point A)) : ((pointEquivMaximal A) p).val = (center A) p := rfl

/-- The existing complete profile labels identify bijectively with the actual maximal ideals. -/
def labelEquivMaximal : (Label A) ≃ (Maximal A) := (pointEquivLabel A).symm.trans (pointEquivMaximal A)

/-- Actual principal (order A), now indexed by every maximal ideal. -/
def order (M : (Maximal A)) (x : A.domain) : ℕ :=
  (realizedProfiles A).value ((labelEquivMaximal A).symm M) x

@[simp] theorem order_label (p : (Label A)) (x : A.domain) :
    (order A) ((labelEquivMaximal A) p) x = (realizedProfiles A).value p x := by
  simp [order]

theorem order_bounded (x : A.domain) (hx : x ≠ 0) : ∃ N : ℕ, ∀ M : (Maximal A), (order A) M x ≤ N := by
  obtain ⟨N, hN⟩ := (realizedProfiles A).exists_all_coordinate_bound x hx
  exact ⟨N, fun M => hN ((labelEquivMaximal A).symm M)⟩

end UnconditionalCounterexample.SparseMaximalSpectrum
