import UnconditionalCounterexample.Variations.MultiDomainRealized
import UnconditionalCounterexample.Variations.MultiDomainPoleValues
import UnconditionalCounterexample.Variations.MultiDomainIntegerReturns

/-!
# Integer returns of the actual moving sequence

The persistent local targets apply on a tail at every prime. Evaluating the
moving recurrence in each component transfers these local returns to the
actual global ring.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open GuardSupport Variations MultiDomain WithZero Filter NormalizedWords MvPolynomial

variable {r : ℕ} (q : PrimeIndex) (upper : Bool)

local notation "L" => realizedLocal r q upper
local notation "G" => standardGeometry r
local notation "A" => selectedData L G
local notation "C" => realizedChoices (r := r) q upper
local notation "c" => flagPoint r

theorem component_return (p : PrimeIndex) (i : (permanentFibre L G p).Component (withPoint upper q p))
    (f : poleAlgebra A →+* (permanentFibre L G p).guard.Field i)
    (hf : ∀ g : Polys (r+1), f (algebraMap _ _ g) = (permanentFibre L G p).componentEval c _ i g)
    (ht : (permanentFibre L G p).localValuation i (f (algebraMap _ _ (X 0 : Polys (r+1)))) =
      exp (-Targets.seedOrder ((permanentFibre L G p).label i)))
    (hv : ∀ k, (permanentFibre L G p).localValuation i (f (selectedUnit L G k)) =
      exp (-(Targets.order (Targets.generator k) ((permanentFibre L G p).label i) : ℤ))) :
    ∀ᶠ n in atTop, (permanentFibre L G p).localValuation i
      ((f ((C).movingPole n) - 1) / (p.val : (permanentFibre L G p).guard.Field i)^n) ≤ 1 := by
  let F := permanentFibre L G p
  let e := F.componentEval c (withPoint upper q p) i
  let P := fun n ↦ e (siteRaw L G n)
  let v := F.localValuation i
  have hunit (n) : f (selectedUnit L G n) = RawWords.normalizedFactor P normalizationPower n := by
    rw [pole_normalized]
    simp only [hf,P,e]
    rfl
  have hq : ∀ᶠ n in atTop, let k := (Generator.q n).stage
      v ((Targets.stageValue v p.val (F.label i) (e (X 0)) P k / RawWords.normalizedFactor P normalizationPower k - 1)
        / (p.val : F.guard.Field i)^(n+1)) ≤ 1 := by
    filter_upwards [eventually_gt_atTop (firstAppearance L G p)] with n hn
    have h : firstAppearance L G p < (Generator.q n).stage := by simp [Generator.stage]; omega
    have h' := (processed_normalized q upper (eventual_processed L G p h) i).2
    simpa only [Targets.generator_stage, Targets.precision] using h'
  have hr := Targets.eventually_return v P (e (X 0)) (F.label i) p.val ((hf _ ▸ ht))
    (fun k ↦ hunit k ▸ hv k) hq
  filter_upwards [hr] with n hn
  unfold realizedChoices
  rw [pole_moving L G (realizedProfiles q upper) (raw_not_divisible_first L) f n]
  simp only [hf]
  exact hn

def tuplePole {E : Type*} [Field E] [Algebra ℚ E] {v : Valuation E ℤᵐ⁰}
    (T : LocalTuple (r+1) v) (D : Data (r+1)) : poleAlgebra D →+* E :=
  (IndependentTuples.evaluation T.x T.independent).comp (poleAlgebra D).toSubring.subtype

theorem tuplePole_raw {E : Type*} [Field E] [Algebra ℚ E] {v : Valuation E ℤᵐ⁰}
    (T : LocalTuple (r+1) v) (D : Data (r+1)) (g : Polys (r+1)) :
    tuplePole T D (algebraMap _ _ g) = aeval T.x g :=
  IsFractionRing.lift_algebraMap (K := FunctionField (r+1)) (g := (aeval T.x : Polys (r+1) →ₐ[ℚ] E).toRingHom)
    T.independent g

theorem realized_primary_return (j : ℕ) : ∀ᶠ n in atTop,
    (A).primary j ((((C).movingElement n : FunctionField (r+1))-1) /
      ((primaryBirth L G j).prime.val : FunctionField (r+1))^n) ≤ 1 := by
  let B := primaryBirth L G j
  let p := B.prime
  let F := permanentFibre L G p
  let extra := withPoint upper q p
  have hF : F.primary = some (j,B.tuple) := primary_fibre L G j
  let i : F.Component extra := some (F.primarySide extra hF)
  let f := tuplePole B.tuple A
  have hl : F.label i = some j := by simp [i,Fibre.label,hF]
  have h := component_return q upper p i f (fun g ↦ (tuplePole_raw _ _ g).trans (F.primary_eval c extra hF g).symm)
    (by rw [hl]; exact selected_primary_t L G j)
    (fun k ↦ by rw [hl]; exact realized_primary q upper j k)
  filter_upwards [h] with n hn
  change Padic.mulValuation ((IndependentTuples.evaluation B.tuple.x B.tuple.independent) _) ≤ 1
  rw [map_div₀,map_sub,map_one,map_pow,map_natCast]
  exact hn

theorem realized_guard_return (p : PrimeIndex) : ∀ᶠ n in atTop,
    (A).guard p ((((C).movingElement n : FunctionField (r+1))-1) / (p.val : FunctionField (r+1))^n) ≤ 1 := by
  let F := permanentFibre L G p
  let extra := withPoint upper q p
  let i : F.Component extra := none
  let f := tuplePole F.guard.tuple A
  have h := component_return q upper p i f (fun g ↦ (tuplePole_raw _ _ g).trans (F.guard_eval c extra g).symm)
    (by simp only [i,Fibre.label,Targets.seedOrder,neg_zero,exp_zero]; exact selected_guard_t L G p)
    (fun k ↦ by simp only [i,Fibre.label,Targets.order,Nat.cast_zero,neg_zero,exp_zero]; exact realized_guard q upper p k)
  filter_upwards [h] with n hn
  change GuardUnramified.valuation p.val _ ((IndependentTuples.evaluation F.guard.tuple.x F.guard.tuple.independent) _) ≤ 1
  rw [map_div₀,map_sub,map_one,map_pow,map_natCast]
  exact hn

theorem realized_integer_return (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n in atTop, (m : ordinary A) ∣ (C).movingElement n - 1 :=
  ordinary_integer_return (selectedClearing L G (raw_not_divisible_first L)) (places L G).injective _
    (realized_primary_return q upper) (realized_guard_return q upper) m hm

end UnconditionalCounterexample.MultivariateSelection
