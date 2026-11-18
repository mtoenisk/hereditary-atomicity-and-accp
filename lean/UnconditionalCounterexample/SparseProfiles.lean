import UnconditionalCounterexample.CompleteProfiles
import UnconditionalCounterexample.SparsePrimaryDomain
import UnconditionalCounterexample.DiscreteOrders
import UnconditionalCounterexample.HorizontalOrders
import UnconditionalCounterexample.PrimaryWordProfiles
import UnconditionalCounterexample.RationalSigns
import UnconditionalCounterexample.LowOrderDivisors
import UnconditionalCounterexample.PairedDomain

/-!
# Complete profiles for an injective primary enumeration

Corollary 8.2 uses complete profiles over each selected set of primes.
Only injectivity of the primary prime sequence is used; a guard remains over
every rational prime. The index types and normalized generators reuse the
paired module literally, as do all discrete-order, horizontal factorization,
signed-word and low-order divisor results. The actual sparse intersection and
its complete profile are identified without adding omitted primaries.

The mixed selector must still supply the elementary b/q and guard generator
columns; no profile, principal-representation or congruence output is assumed.
-/

noncomputable section

namespace UnconditionalCounterexample.SparsePrimaryDomain

/-- The general injective-primary data also contains every earlier paired family. -/
def Places.ofPaired (d : PairedDomain.Places) : Places where
  primes := d.primes.toEmbedding
  primary := d.primary
  primary_trans := d.primary_trans
  primary_late := d.primary_late
  guard := d.guard
  guard_trans := d.guard_trans

@[simp] theorem vertical_ofPaired (d : PairedDomain.Places) :
    vertical (Places.ofPaired d) = PairedDomain.vertical d := rfl

@[simp] theorem domain_ofPaired (S : Set (Polynomial ℚ)) (d : PairedDomain.Places) :
    domain S (Places.ofPaired d) = PairedDomain.domain S d := rfl

end UnconditionalCounterexample.SparsePrimaryDomain

namespace UnconditionalCounterexample.SparseProfiles

open Polynomial WithZero DiscreteOrders GuardSupport PrincipalProfiles
open PrimaryWordProfiles NormalizedWords

/-- All retained horizontal places other than the distinguished X-coordinate. -/
abbrev OtherHorizontal (S : Set ℚ[X]) :=
  CompleteProfiles.OtherHorizontal S

abbrev Outside (S : Set ℚ[X]) := CompleteProfiles.Outside S

def valuations (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places) :
    ProfilePlace (Outside S) → Valuation (RatFunc ℚ) ℤᵐ⁰
  | .limit => HorizontalOrders.valuation HorizontalOrders.xPoint
  | .primary n => SparsePrimaryDomain.vertical d (.inl n)
  | .outside (.inl p) => SparsePrimaryDomain.vertical d (.inr p)
  | .outside (.inr p) => HorizontalOrders.valuation p.val

theorem domain_eq_fullIntersection (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places)
    (hS : ∀ q ∈ S, q.coeff 0 ≠ 0) :
    SparsePrimaryDomain.domain S d = fullIntersection (valuations S d) := by
  have hn : ∀ q ∈ S, q ≠ 0 := fun q hq hz => hS q hq (by simp [hz])
  have hX := HorizontalOrders.retained_xPoint_of_constantCoeff_ne_zero S hS
  ext x
  by_cases hx : x = 0
  · subst x
    simp
  rw [SparsePrimaryDomain.domain, IntersectionDomain.mem_intersection,
    fullIntersection, IntersectionDomain.mem_intersection]
  simp only [Subring.mem_top, true_and]
  constructor
  · rintro ⟨hB, hv⟩ p
    have hh := (HorizontalOrders.mem_iff_retained_valuations_le_one S hn x hx).mp hB
    cases p with
    | limit => exact hh _ hX
    | primary n => exact hv (.inl n)
    | outside i =>
      cases i with
      | inl p => exact hv (.inr p)
      | inr p => exact hh p.val p.property.1
  · intro hv
    refine ⟨(HorizontalOrders.mem_iff_retained_valuations_le_one S hn x hx).mpr ?_, ?_⟩
    · intro p hp
      by_cases hpx : p = HorizontalOrders.xPoint
      · subst p
        exact hv .limit
      · exact hv (.outside (.inr ⟨p, hp, hpx⟩))
    · rintro (n | p)
      · exact hv (.primary n)
      · exact hv (.outside (.inl p))

theorem integral (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places)
    (hS : ∀ q ∈ S, q.coeff 0 ≠ 0) (x : SparsePrimaryDomain.domain S d)
    (p : ProfilePlace (Outside S)) : valuations S d p x ≤ 1 := by
  have hx : (x : RatFunc ℚ) ∈ fullIntersection (valuations S d) := by
    rw [← domain_eq_fullIntersection S d hS]
    exact x.property
  exact DiscreteOrders.integral (valuations S d) ⟨x, hx⟩ p

theorem limit_order (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places)
    (x : RatFunc ℚ) (hx : x ≠ 0) :
    order (valuations S d .limit) x = PrimaryStabilization.tOrder x := by
  change -log (HorizontalOrders.valuation HorizontalOrders.xPoint x) = _
  rw [HorizontalOrders.valuation_xPoint_eq_exp_neg_tOrder x hx, log_exp, neg_neg]

theorem eventually_primary (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places)
    (x : RatFunc ℚ) (hx : x ≠ 0) : ∃ N : ℕ, ∀ j, N ≤ j →
      order (valuations S d (.primary j)) x = order (valuations S d .limit) x := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (PrimaryStabilization.eventually_evaluationValuation_eq_exp_neg_tOrder
      (fun n => (d.primes n).val) (Subtype.val_injective.comp d.primes.injective)
      (fun n => (d.primary n).val) d.primary_trans d.primary_late x hx)
  refine ⟨N, ?_⟩
  intro j hj
  rw [limit_order S d x hx]
  change -log (EvaluationDVR.evaluationValuation _ _ _ x) = _
  rw [hN j hj, log_exp, neg_neg]

theorem finite_outside (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places)
    (hguard : ∀ x : RatFunc ℚ, x ≠ 0 →
      {p : PrimeIndex | SparsePrimaryDomain.vertical d (.inr p) x ≠ 1}.Finite)
    (x : RatFunc ℚ) (hx : x ≠ 0) :
    {i : Outside S | order (valuations S d (.outside i)) x ≠ 0}.Finite := by
  have hg := hguard x hx
  have hh := HorizontalOrders.finite_valuation_support x hx
  have ho : {p : OtherHorizontal S | HorizontalOrders.valuation p.val x ≠ 1}.Finite :=
    hh.preimage Subtype.val_injective.injOn
  apply ((hg.image (Sum.inl (β := OtherHorizontal S))).union
    (ho.image (Sum.inr (α := PrimeIndex)))).subset
  rintro (p | p) hp
  · apply Or.inl
    refine ⟨p, ?_, rfl⟩
    exact mt (order_eq_zero_iff _ hx).mpr hp
  · apply Or.inr
    refine ⟨p, ?_, rfl⟩
    exact mt (order_eq_zero_iff _ hx).mpr hp

/-- All horizontal and guard orders zero gives a genuine unit of the pole
algebra; primary orders may have either sign. -/
theorem pole_unit_of_zero_outside (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places)
    (hS : ∀ q ∈ S, q ≠ 0) (x : RatFunc ℚ) (hx : x ≠ 0)
    (hl : order (valuations S d .limit) x = 0)
    (ho : ∀ i, order (valuations S d (.outside i)) x = 0) :
    x ∈ PoleAlgebra.generated S ∧ x⁻¹ ∈ PoleAlgebra.generated S := by
  apply (HorizontalOrders.mem_and_inv_mem_iff_retained_valuations_eq_one S hS x hx).mpr
  intro p hp
  by_cases hpx : p = HorizontalOrders.xPoint
  · subst p
    exact (order_eq_zero_iff _ hx).mp hl
  · exact (order_eq_zero_iff _ hx).mp (ho (.inr ⟨p, hp, hpx⟩))

abbrev generators (F : ℕ → ℚ[X]) (E : ℕ → ℕ) : ℕ → RatFunc ℚ :=
  CompleteProfiles.generators F E

/-- The elementary generator valuation columns furnished by the schedule. -/
structure GeneratorProfiles (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (d : SparsePrimaryDomain.Places) : Prop where
  guard : ∀ p i, SparsePrimaryDomain.vertical d (.inr p) (generators F E i) = 1
  b : ∀ n j, SparsePrimaryDomain.vertical d (.inl j)
    (generators F E (Generator.b n).stage) = exp (-(bWeight n j))
  q : ∀ n j, SparsePrimaryDomain.vertical d (.inl j)
    (generators F E (Generator.q n).stage) = exp (-(qWeight n j))

/-- An arbitrary nonzero fraction with zero horizontal and guard coordinates
has a literal signed normalized-word expression and its computed primary profile. -/
theorem exists_signed_word (F : ℕ → ℚ[X])
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (E : ℕ → ℕ) (d : SparsePrimaryDomain.Places) (hG : GeneratorProfiles F E d)
    (x : RatFunc ℚ) (hx : x ≠ 0)
    (hl : order (valuations (Set.range F) d .limit) x = 0)
    (ho : ∀ i, order (valuations (Set.range F) d (.outside i)) x = 0) :
    ∃ e : ℕ →₀ ℤ,
      (x = word (generators F E) e ∨ x = -word (generators F E) e) ∧
      Represents (StageExponents.bExponents e) (StageExponents.qExponents e)
        (fun j => order (valuations (Set.range F) d (.primary j)) x) := by
  have hn : ∀ q ∈ Set.range F, q ≠ 0 := by
    rintro q ⟨i, rfl⟩
    exact (hF i).1.ne_zero
  obtain ⟨hxB, hxiB⟩ := pole_unit_of_zero_outside _ d hn x hx hl ho
  obtain ⟨e, he⟩ := RationalSigns.exists_signed_normalized_factorization F hF hinj E x hx
    hxB hxiB (guardEvaluation d.guard d.guard_trans)
    (fun p => (order_eq_zero_iff _ hx).mp (ho (.inl p))) hG.guard
  refine ⟨e, he, ?_⟩
  exact represents_actual_primary_orders (fun j => SparsePrimaryDomain.vertical d (.inl j))
    (generators F E) hG.b hG.q e x hx he

theorem pure_triple (F : ℕ → ℚ[X])
    (hF : ∀ i, (F i).Monic ∧ Irreducible (F i)) (hinj : Function.Injective F)
    (E : ℕ → ℕ) (d : SparsePrimaryDomain.Places) (hG : GeneratorProfiles F E d)
    (x : RatFunc ℚ) (hx : x ≠ 0)
    (hl : order (valuations (Set.range F) d .limit) x = 0)
    (ho : ∀ i, order (valuations (Set.range F) d (.outside i)) x = 0) :
    TripleCongruent (fun j => order (valuations (Set.range F) d (.primary j)) x) := by
  obtain ⟨_, _, h⟩ := exists_signed_word F hF hinj E d hG x hx hl ho
  exact ValuationProfiles.tripleCongruent_of_represents h

theorem mem_domain_iff (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places)
    (hS : ∀ q ∈ S, q.coeff 0 ≠ 0) (x : RatFunc ℚ) :
    x ∈ SparsePrimaryDomain.domain S d ↔ ∀ p, valuations S d p x ≤ 1 := by
  rw [domain_eq_fullIntersection S d hS, fullIntersection, IntersectionDomain.mem_intersection]
  simp only [Subring.mem_top, true_and]

theorem isUnit_iff_order_zero (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places)
    (hS : ∀ q ∈ S, q.coeff 0 ≠ 0) (x : SparsePrimaryDomain.domain S d) (hx : x ≠ 0) :
    IsUnit x ↔ ∀ p, order (valuations S d p) (x : RatFunc ℚ) = 0 := by
  constructor
  · intro hu p
    exact order_eq_zero_of_isUnit (SparsePrimaryDomain.domain S d) (valuations S d p)
      (fun z hz => integral S d hS ⟨z, hz⟩ p) hu
  · intro ho
    have hx0 : (x : RatFunc ℚ) ≠ 0 := fun h => hx (Subtype.ext h)
    have hi : (x : RatFunc ℚ)⁻¹ ∈ SparsePrimaryDomain.domain S d := by
      apply (mem_domain_iff S d hS _).mpr
      intro p
      rw [map_inv₀, (order_eq_zero_iff _ hx0).mp (ho p), inv_one]
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨(x : RatFunc ℚ)⁻¹, hi⟩, ?_⟩
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0

theorem dvd_iff_natOrder_le (S : Set ℚ[X]) (d : SparsePrimaryDomain.Places)
    (hS : ∀ q ∈ S, q.coeff 0 ≠ 0) (x y : SparsePrimaryDomain.domain S d)
    (hx : x ≠ 0) (hy : y ≠ 0) : x ∣ y ↔
      ∀ p, natOrder (valuations S d p) (x : RatFunc ℚ) ≤
        natOrder (valuations S d p) (y : RatFunc ℚ) := by
  have hx0 : (x : RatFunc ℚ) ≠ 0 := fun h => hx (Subtype.ext h)
  have hy0 : (y : RatFunc ℚ) ≠ 0 := fun h => hy (Subtype.ext h)
  rw [IntersectionDomain.subring_dvd_iff_div_mem _ x y hx, mem_domain_iff S d hS]
  apply forall_congr'
  intro p
  rw [← order_nonneg_iff _ (div_ne_zero hy0 hx0), order_div _ hy0 hx0]
  have hc := natOrder_cast (valuations S d p) hx0 (integral S d hS x p)
  have hd := natOrder_cast (valuations S d p) hy0 (integral S d hS y p)
  omega

section Realized

variable (F : ℕ → ℚ[X]) (hF : ∀ i, (F i).Monic ∧ Irreducible (F i))
  (hinj : Function.Injective F) (hconst : ∀ i, (F i).coeff 0 ≠ 0)
  (E : ℕ → ℕ) (d : SparsePrimaryDomain.Places) (hG : GeneratorProfiles F E d)
  (hguard : ∀ x : RatFunc ℚ, x ≠ 0 →
    {p : PrimeIndex | SparsePrimaryDomain.vertical d (.inr p) x ≠ 1}.Finite)

include hconst in
private theorem constant_nonzero : ∀ q ∈ Set.range F, q.coeff 0 ≠ 0 := by
  rintro q ⟨i, rfl⟩
  exact hconst i

/-- Natural orders of the actual paired domain, with every horizontal coordinate
retained. Its principal congruences are derived from actual signed products. -/
def profiles : ValuationProfiles (SparsePrimaryDomain.domain (Set.range F) d) (Outside (Set.range F)) where
  value p x := natOrder (valuations (Set.range F) d p) (x : RatFunc ℚ)
  value_unit p x hx := natOrder_eq_zero_of_isUnit _ _
    (fun z hz => integral _ d (constant_nonzero F hconst) ⟨z, hz⟩ p) hx
  value_mul p x y hx hy := natOrder_mul _
    (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h))
    (integral _ d (constant_nonzero F hconst) x p)
    (integral _ d (constant_nonzero F hconst) y p)
  unit_of_zero x hx hzero := by
    apply (isUnit_iff_order_zero _ d (constant_nonzero F hconst) x hx).mpr
    intro p
    rw [← natOrder_cast _ (fun h => hx (Subtype.ext h))
      (integral _ d (constant_nonzero F hconst) x p), hzero]
    rfl
  eventually_primary x hx := by
    obtain ⟨N, hN⟩ := eventually_primary _ d x (fun h => hx (Subtype.ext h))
    refine ⟨N, ?_⟩
    intro j hj
    exact congrArg Int.toNat (hN j hj)
  finite_outside x hx := by
    apply (finite_outside _ d hguard x (fun h => hx (Subtype.ext h))).subset
    intro i hi hz
    apply hi
    rw [natOrder, hz]
    rfl
  pure_triple x hx hl ho := by
    have hx0 : (x : RatFunc ℚ) ≠ 0 := fun h => hx (Subtype.ext h)
    have hcast (p : ProfilePlace (Outside (Set.range F))) :=
      natOrder_cast (valuations (Set.range F) d p) hx0
        (integral _ d (constant_nonzero F hconst) x p)
    have hl' : order (valuations (Set.range F) d .limit) x = 0 := by
      rw [← hcast .limit, hl]
      rfl
    have ho' : ∀ i, order (valuations (Set.range F) d (.outside i)) x = 0 := by
      intro i
      rw [← hcast (.outside i), ho]
      rfl
    convert pure_triple F hF hinj E d hG x hx0 hl' ho' using 1
    funext j
    exact hcast (.primary j)

@[simp] theorem profiles_value (p : ProfilePlace (Outside (Set.range F)))
    (x : SparsePrimaryDomain.domain (Set.range F) d) :
    (profiles F hF hinj hconst E d hG hguard).value p x =
      natOrder (valuations (Set.range F) d p) (x : RatFunc ℚ) := rfl

theorem profiles_value_cast (p : ProfilePlace (Outside (Set.range F)))
    (x : SparsePrimaryDomain.domain (Set.range F) d) (hx : x ≠ 0) :
    ((profiles F hF hinj hconst E d hG hguard).value p x : ℤ) =
      order (valuations (Set.range F) d p) (x : RatFunc ℚ) :=
  natOrder_cast _ (fun h => hx (Subtype.ext h))
    (integral _ d (constant_nonzero F hconst) x p)

/-- Coordinate comparisons imply actual divisibility in D. -/
theorem coordinate_divisibility
    (x y : SparsePrimaryDomain.domain (Set.range F) d) (hx : x ≠ 0) (hy : y ≠ 0)
    (hle : ∀ p, (profiles F hF hinj hconst E d hG hguard).value p x ≤
      (profiles F hF hinj hconst E d hG hguard).value p y) : x ∣ y :=
  (dvd_iff_natOrder_le _ d (constant_nonzero F hconst) x y hx hy).mpr hle

/-- The signed quotient congruences needed for finite low-order divisor classes.
The quotient is allowed negative primary coordinates and need not lie in D. -/
theorem signedDifferenceTriple :
    ValuationProfiles.SignedDifferenceTriple (profiles F hF hinj hconst E d hG hguard) := by
  intro z u hz hu hzl hul hout
  have hz0 : (z : RatFunc ℚ) ≠ 0 := fun h => hz (Subtype.ext h)
  have hu0 : (u : RatFunc ℚ) ≠ 0 := fun h => hu (Subtype.ext h)
  have hc (p : ProfilePlace (Outside (Set.range F))) :
      order (valuations (Set.range F) d p) ((z : RatFunc ℚ) / u) =
      ((profiles F hF hinj hconst E d hG hguard).value p z : ℤ) -
        (profiles F hF hinj hconst E d hG hguard).value p u := by
    rw [order_div _ hz0 hu0,
      profiles_value_cast F hF hinj hconst E d hG hguard p z hz,
      profiles_value_cast F hF hinj hconst E d hG hguard p u hu]
  have hl : order (valuations (Set.range F) d .limit) ((z : RatFunc ℚ) / u) = 0 := by
    rw [hc .limit, hzl, hul]
    simp
  have ho : ∀ i, order (valuations (Set.range F) d (.outside i)) ((z : RatFunc ℚ) / u) = 0 := by
    intro i
    rw [hc (.outside i), hout i, sub_self]
  convert pure_triple F hF hinj E d hG ((z : RatFunc ℚ) / u) (div_ne_zero hz0 hu0) hl ho using 1
  funext j
  exact (hc (.primary j)).symm

/-- The distinguished natural profile is exactly the order at zero. -/
theorem profiles_limit_cast (x : SparsePrimaryDomain.domain (Set.range F) d) (hx : x ≠ 0) :
    ((profiles F hF hinj hconst E d hG hguard).value .limit x : ℤ) =
      PrimaryStabilization.tOrder (x : RatFunc ℚ) := by
  rw [profiles_value_cast F hF hinj hconst E d hG hguard .limit x hx,
    limit_order _ d x (fun h => hx (Subtype.ext h))]

include hF hinj hconst E hG hguard in
/-- Actual divisors up to associates are finite at order zero and one. -/
theorem finite_associates_divisors_of_order_le_one
    (x : SparsePrimaryDomain.domain (Set.range F) d) (hx : x ≠ 0)
    (horder : PrimaryStabilization.tOrder (x : RatFunc ℚ) ≤ 1) :
    {a : Associates (SparsePrimaryDomain.domain (Set.range F) d) | a ∣ Associates.mk x}.Finite := by
  apply ValuationProfiles.finite_associates_divisors_of_limit_le_one
    (profiles F hF hinj hconst E d hG hguard)
    (signedDifferenceTriple F hF hinj hconst E d hG hguard)
    (coordinate_divisibility F hF hinj hconst E d hG hguard) hx
  have h := profiles_limit_cast F hF hinj hconst E d hG hguard x hx
  omega

end Realized

end UnconditionalCounterexample.SparseProfiles
