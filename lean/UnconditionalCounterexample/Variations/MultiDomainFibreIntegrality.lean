import UnconditionalCounterexample.Variations.MultiDomainEvaluated
import UnconditionalCounterexample.Variations.MultiDomainConductor
import UnconditionalCounterexample.Variations.DimensionClosedEvaluation

/-! # The rational evaluation of domain elements at the permanent fibres -/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain

variable {r : ℕ} {q : PrimeIndex} {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  (L : LocalPrescription r q) (G : Geometry r K)

private theorem primary_origin (p : PrimeIndex) (j : ℕ)
    (h : (permanentFibre L G p).primary.map Prod.fst = some j) :
    p = (if j % 2 = 0 then (permanentBatch L G (j/2)).first.prime else
      (permanentBatch L G (j/2)).second.prime) := by
  let n := firstAppearance L G p
  let B := permanentBatch L G n
  by_cases h₁ : p = B.first.prime
  · have hj := primary_at_first L G n
    rw [← h₁,h] at hj
    have he := Option.some.inj hj
    rw [he,show 2*n % 2 = 0 by omega,ite_eq_left rfl,show 2*n/2 = n by omega]
    exact h₁
  by_cases h₂ : p = B.second.prime
  · have hj := primary_at_second L G n
    rw [← h₂,h] at hj
    have he := Option.some.inj hj
    rw [he,ite_eq_right (by omega : (2*n+1)%2 ≠ 0),show (2*n+1)/2 = n by omega]
    exact h₂
  have hn := (valid_batch L G n).other_at p (first_mem L G p) (new_at_first L G p) h₁ h₂
  rw [frozen L G (first_mem L G p)] at hn
  simp [hn] at h

theorem prime_of_primary_label (p : PrimeIndex) (j : ℕ)
    (h : (permanentFibre L G p).primary.map Prod.fst = some j) :
    p = (primaryBirth L G j).prime :=
  (primary_origin L G _ _ h).trans (primary_origin L G _ _ (primary_label L G j)).symm

variable (c : Fin (r+1) → ℚ)
  (hc : MultivariateFibres.Retained (denominators (selectedData L G)) c)

local notation "B" => poleAlgebra (selectedData L G)

private theorem aeval_eq_component (p : PrimeIndex) (extra : Bool)
    (i : (permanentFibre L G p).Component extra) (f : Poly r) :
    aeval ((permanentFibre L G p).guard.points ((permanentFibre L G p).sidePoints c extra) i) f =
      (permanentFibre L G p).componentEval c extra i f := by
  change eval₂ (algebraMap ℚ ((permanentFibre L G p).guard.Field i)) _ f = eval₂ (Rat.castHom ((permanentFibre L G p).guard.Field i)) _ f
  rw [show algebraMap ℚ ((permanentFibre L G p).guard.Field i) = Rat.castHom _ from Subsingleton.elim ..]

def rationalFibreEval (p : PrimeIndex) (extra : Bool) (i : (permanentFibre L G p).Component extra) :
    B →ₐ[ℚ] (permanentFibre L G p).guard.Field i :=
  closedPointEval (denominators (selectedData L G)) B
    ((permanentFibre L G p).guard.points ((permanentFibre L G p).sidePoints c extra) i) (fun m ↦ by
      rw [aeval_eq_component]
      exact (permanentFibre L G p).componentEval_ne_zero c extra i m.val
        (mem_nonZeroDivisors_iff_ne_zero.mp (denominators_regular _ m.property)) (hc m))

theorem rationalFibreEval_polynomial (p : PrimeIndex) (extra : Bool)
    (i : (permanentFibre L G p).Component extra) (f : Poly r) :
    rationalFibreEval L G c hc p extra i (algebraMap _ B f) =
      (permanentFibre L G p).componentEval c extra i f :=
  (closedPointEval_polynomial _ _ _ _ _).trans (aeval_eq_component L G c p extra i f)

private theorem rational_guard (p : PrimeIndex) (extra : Bool) :
    (rationalFibreEval L G c hc p extra none).toRingHom =
      (IndependentTuples.evaluation (permanentFibre L G p).guard.tuple.x
        (permanentFibre L G p).guard.independent).comp (poleAlgebra (selectedData L G)).subtype := by
  apply IsLocalization.ringHom_ext (denominators (selectedData L G))
  apply RingHom.ext
  intro f
  exact (rationalFibreEval_polynomial L G c hc p extra none f).trans
    (((permanentFibre L G p).guard_eval c extra f).trans (IsFractionRing.lift_algebraMap
      (K := FunctionField (r+1)) (g := (aeval (permanentFibre L G p).guard.tuple.x : Poly r →ₐ[ℚ] (permanentFibre L G p).guard.Field (none : Option Unit)).toRingHom)
      (permanentFibre L G p).guard.independent f).symm)

private theorem rational_primary (p : PrimeIndex) (extra : Bool) {j : ℕ}
    {t : LocalTuple (r+1) (Padic.mulValuation (p := p.val))}
    (h : (permanentFibre L G p).primary = some (j,t)) (s : (permanentFibre L G p).Side extra) :
    (rationalFibreEval L G c hc p extra (some s)).toRingHom =
      (IndependentTuples.evaluation t.x t.independent).comp (poleAlgebra (selectedData L G)).subtype := by
  apply IsLocalization.ringHom_ext (denominators (selectedData L G))
  apply RingHom.ext
  intro f
  rw [Subsingleton.elim s ((permanentFibre L G p).primarySide extra h)]
  exact (rationalFibreEval_polynomial L G c hc p extra _ f).trans
    (((permanentFibre L G p).primary_eval c extra h f).trans (IsFractionRing.lift_algebraMap
      (K := FunctionField (r+1)) (g := (aeval t.x : Poly r →ₐ[ℚ] ℚ_[p.val]).toRingHom) t.independent f).symm)

private theorem rational_point (p : PrimeIndex) (h : (permanentFibre L G p).primary = none)
    (s : (permanentFibre L G p).Side true) :
    (rationalFibreEval L G c hc p true (some s)).toRingHom =
      (Rat.castHom ℚ_[p.val]).comp (MultivariateFibres.pointEval _ B c hc).toRingHom := by
  apply IsLocalization.ringHom_ext (denominators (selectedData L G))
  apply RingHom.ext
  intro f
  rw [Subsingleton.elim s (permanentFibre L G p).pointSide]
  exact (rationalFibreEval_polynomial L G c hc p true _ f).trans
    (((permanentFibre L G p).point_eval c _ h f).trans
      (congrArg (Rat.castHom ℚ_[p.val]) (MultivariateFibres.pointEval_polynomial _ _ c hc f)).symm)

theorem norm_rationalFibreEval (p : PrimeIndex) (extra : Bool) (i : (permanentFibre L G p).Component extra)
    (z : ordinary (selectedData L G)) (hpoint : extra = true →
      (permanentFibre L G p).primary = none → point (selectedData L G) c hc z ∈ PointPullback.localRationals p.val) :
    ‖rationalFibreEval L G c hc p extra i (intoPole z)‖ ≤ 1 := by
  cases i with
  | none =>
    rw [show rationalFibreEval L G c hc p extra none (intoPole z) = _ from
      RingHom.congr_fun (rational_guard L G c hc p extra) _]
    exact (GuardUnramified.norm_le_one_iff_valuation _ _ _).mpr (((mem_ordinary _).mp z.property).2.2 p)
  | some s =>
    cases h : (permanentFibre L G p).primary with
    | none =>
      have htrue : extra = true := by simpa [h] using s.property
      subst extra
      exact (RingHom.congr_fun (rational_point L G c hc p h s) (intoPole z)) ▸ hpoint rfl h
    | some jt =>
      obtain ⟨j,t⟩ := jt
      have hp := prime_of_primary_label L G p j (by rw [h]; rfl)
      subst p
      have ht := primary_fibre L G j
      rw [h] at ht
      have ht' : t = (primaryBirth L G j).tuple := congrArg Prod.snd (Option.some.inj ht)
      subst t
      rw [show rationalFibreEval L G c hc _ extra (some s) (intoPole z) = _ from
        RingHom.congr_fun (rational_primary L G c hc _ extra h s) _]
      have hv := ((mem_ordinary _).mp z.property).2.1 j
      have hv' : Padic.mulValuation ((IndependentTuples.evaluation _ (primaryBirth L G j).tuple.independent) (z : FunctionField (r+1))) ≤ 1 := hv
      change ‖(IndependentTuples.evaluation _ (primaryBirth L G j).tuple.independent) (z : FunctionField (r+1))‖ ≤ 1
      exact le_of_not_gt (fun hh ↦ hv'.not_gt (by
        simpa only [map_one] using (Padic.norm_lt_norm_iff_mulValuation_lt.mp
          (show ‖(1 : ℚ_[(primaryBirth L G j).prime.val])‖ < _ from (norm_one (α := ℚ_[(primaryBirth L G j).prime.val])).trans_lt hh))))

end UnconditionalCounterexample.MultivariateSelection
