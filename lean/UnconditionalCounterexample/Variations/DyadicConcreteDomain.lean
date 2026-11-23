import UnconditionalCounterexample.Variations.DyadicFiniteProfiles

/-! # The dyadic valuation intersection is the literal univariate domain -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open GuardSupport Univariate FreezingCalendar DiscreteOrders DyadicDeviations UnivariateConductor

set_option backward.isDefEq.respectTransparency false

variable (a : Policy)

theorem horizontal_retained (i : HorizontalIndex (Horiz a)) :
    HorizontalOrders.Retained (poles (driver a).requirements) (horizontal a i) := by
  cases i with
  | inl c => exact centre_retained a c
  | inr q =>
    let C := chain (driver a).requirements
    exact (HorizontalOrders.retained_range_iff C.raw (fun i => ⟨C.raw_monic i,C.raw_irreducible i⟩) _).mpr
      q.property.1

theorem horizontal_covers (q : Horizontal) (hr : HorizontalOrders.Retained (poles (driver a).requirements) q) :
    ∃ i, horizontal a i = q := by
  let C := chain (driver a).requirements
  by_cases h : ∃ c, q = centre c
  · obtain ⟨c,h⟩ := h; exact ⟨.inl c,h.symm⟩
  · exact ⟨.inr ⟨q,(HorizontalOrders.retained_range_iff C.raw
      (fun i => ⟨C.raw_monic i,C.raw_irreducible i⟩) q).mp hr,fun c he => h ⟨c,he⟩⟩,rfl⟩

theorem primary_covers (p : PrimeIndex) (hp : ((driver a).permanentRole p).isSome) :
    ∃ i : Coordinates a, valuation a i = primaryVal a p hp := by
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp hp
  cases r with
  | regular c k i =>
    have he := (driver a).permanent_regular_unique (regularPrime_role a (c,k,i)) hr
    subst p
    cases c
    · exact ⟨.plus k i,rfl⟩
    · exact ⟨.minus k i,rfl⟩
  | auxiliary k i e => exact ⟨.other (.auxiliary k ⟨p,i,e,hr⟩),rfl⟩

private theorem eval_congr {p : PrimeIndex} {u v : ℚ_[p.val]} (h : u = v)
    (hu : Transcendental ℚ u) (hv : Transcendental ℚ v) :
    LocalEvaluation.evalAt u hu = LocalEvaluation.evalAt v hv := by subst v; rfl

private theorem all_branches {p : PrimeIndex} (s : Univariate.Site p) (x : RatFunc ℚ) :
    (∀ z : Point p, z ∈ s.fibre.points → LocalEvaluation.evalAt z.value.val z.transcendental x ∈ PadicInt.subring p.val) ↔
      ∀ b (hb : MixedStageSelection.Active s.paired b), ‖s.evaluate b hb x‖ ≤ 1 := by
  constructor
  · intro h b hb
    have hguard : (⟨s.guard,s.guard_trans⟩ : Point p) ∈ s.fibre.points := by
      cases he : s.primary <;> simp [Site.fibre,he,Fibre.points]
    cases b with
    | true =>
      change ‖LocalEvaluation.evalAt s.guard.val s.guard_trans x‖ ≤ 1
      exact h ⟨s.guard,s.guard_trans⟩ hguard
    | false =>
      have hpair := hb.resolve_left (by decide)
      obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp hpair
      have hm : (⟨z.val,z.property.1⟩ : Point p) ∈ s.fibre.points := by
        simp [Site.fibre,hz,Fibre.points]
      have he : s.branch false = z.val.val := by simp [Site.branch,hz]
      have hv := h ⟨z.val,z.property.1⟩ hm
      change ‖LocalEvaluation.evalAt (s.branch false) _ x‖ ≤ 1
      change ‖LocalEvaluation.evalAt z.val.val z.property.1 x‖ ≤ 1 at hv
      rw [eval_congr (p := p) he _ z.property.1]
      exact hv
  · intro h z hz
    obtain ⟨b,hb,he⟩ := s.branch_of_point hz
    have hv := h b hb
    change ‖LocalEvaluation.evalAt (s.branch b) _ x‖ ≤ 1 at hv
    rw [eval_congr (p := p) he _ z.transcendental] at hv
    exact hv

/-- The ring recovered by the conductor and the ring used for the dyadic
valuation profile are equal as subrings of the same rational function field. -/
theorem domain_eq_intersection : domain (driver a).requirements = fullIntersection (valuation a) := by
  let D := driver a
  let R := D.requirements
  ext x
  by_cases hx : x = 0
  · subst x; simp
  rw [mem_domain_iff,IntersectionDomain.mem_intersection,HorizontalOrders.mem_iff_retained_valuations_le_one
    (poles R) (poles_nonzero R) x hx]
  simp only [Subring.mem_top,true_and]
  constructor
  · rintro ⟨hh,hv⟩
    have guard (g : GuardIndex (Aux a) (Lone a)) : guardVal a g x ≤ 1 := by
      let p := guardPrime a g
      apply (EvaluationDVR.mem_valuationSubring _ _ _).mpr
      rw [← UnivariateExtraction.eval_permanent_guard]
      exact (all_branches _ x).mp (hv _) true (Or.inl rfl)
    have primary (p : PrimeIndex) (hp : (D.permanentRole p).isSome) : primaryVal a p hp x ≤ 1 :=
      (EvaluationDVR.mem_valuationSubring _ _ _).mpr
        ((all_branches _ x).mp (hv _) false (Or.inr ((D.paired_iff_role p).mpr hp)))
    intro i
    cases i with
    | centre c => exact hh _ (centre_retained a c)
    | plus k i => exact primary (regularPrime a (false,k,i)) (by rw [regularPrime_role]; rfl)
    | minus k i => exact primary (regularPrime a (true,k,i)) (by rw [regularPrime_role]; rfl)
    | other s => cases s with
      | auxiliary k j => exact primary j.prime (by rw [j.role_eq]; rfl)
      | horizontal q => exact hh _ (horizontal_retained a (.inr q))
      | plusGuard k j => exact guard (.inl (k,j))
      | minusGuard k j => exact guard (.inr (.inl (k,j)))
      | auxiliaryGuard k j => exact guard (.inr (.inr (.inl ⟨k,j⟩)))
      | loneGuard g => exact guard (.inr (.inr (.inr g)))
  · intro h
    constructor
    · intro q hq
      obtain ⟨i,rfl⟩ := horizontal_covers a q hq
      simpa [valuation_horizontal] using h (horizontalSite i)
    · intro p
      apply (all_branches _ x).mpr
      intro b hb
      cases b with
      | true =>
        let g := (guardPrime a).symm p
        have hg : UnivariateExtraction.guardVal R p x ≤ 1 := by
          have he := h (guardSite g)
          rw [valuation_guard] at he
          simpa [guardVal,g] using he
        have hn := (EvaluationDVR.mem_valuationSubring _ _ _).mp hg
        rw [← UnivariateExtraction.eval_permanent_guard] at hn
        exact hn
      | false =>
        have hrole := (D.paired_iff_role p).mp (hb.resolve_left (by decide))
        obtain ⟨i,he⟩ := primary_covers a p hrole
        apply (EvaluationDVR.mem_valuationSubring _ _ _).mp
        change primaryVal a p hrole x ≤ 1
        rw [← he]
        exact h i

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
