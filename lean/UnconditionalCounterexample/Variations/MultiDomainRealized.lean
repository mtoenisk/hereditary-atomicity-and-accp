import UnconditionalCounterexample.Variations.MultiDomainEvaluated
import UnconditionalCounterexample.Variations.MultivariateSelectionActual
import UnconditionalCounterexample.Variations.MultivariateSelectionBornUnits
import UnconditionalCounterexample.Variations.MultivariateGeometry

/-!
# Ternary valuation columns of the selected multivariate polynomials

Processed primes use their saved arithmetic tests. Earlier factors at
future primary births and at guards outside the processed set are units.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain WithZero NormalizedWords

variable {r : ℕ} (q : PrimeIndex) (upper : Bool)

abbrev realizedLocal (r : ℕ) (q : PrimeIndex) (upper : Bool) :=
  actualPrescription q (flagPoint r) upper

local notation "L" => realizedLocal r q upper
local notation "G" => standardGeometry r
local notation "c" => flagPoint r

theorem processed_normalized {n : ℕ} {p : PrimeIndex} (hp : p ∈ (permanentBatch L G n).processed)
    (i : (permanentFibre L G p).Component (withPoint upper q p)) :
    let F := permanentFibre L G p
    let e := F.componentEval c (withPoint upper q p) i
    let v := F.localValuation i
    let P := fun k ↦ e (siteRaw L G k)
    let U := RawWords.normalizedFactor P normalizationPower
    v (U n) = exp (-(Targets.order (Targets.generator n) (F.label i) : ℤ)) ∧
      v ((Targets.stageValue v p.val (F.label i) (e (X 0)) P n / U n - 1) /
        (p.val : F.guard.Field i)^Targets.precision (Targets.generator n)) ≤ 1 := by
  let F := permanentFibre L G p
  let h := fun j : Fin n ↦ siteChain L G j.val
  have ha : p ∈ (allocate q n h).processed := (actual_batch L G n) ▸ hp
  have hc : (fun j ↦ algebraMap ℚ GeometricField (c j)) ∈ (standardGeometry r).fixed := by
    change algebraMap ℚ GeometricField ∘ c ∈ (standardGeometry r).fixed
    simp [standardGeometry]
  obtain ⟨_,ht⟩ := selected_tests q c upper G hc n ⟨p,ha⟩
  apply Targets.actual_normalized (requirements L G) _ _ _ _ (F.localValuation_prime i)
  · exact fun j ↦ F.componentEval_ne_zero c _ i _ (raw_irreducible _ j).ne_zero (raw_at_flagPoint L j)
  · have hv := ht.values i
    rwa [F.componentEval_baseChange] at hv

theorem realized_primary (j n : ℕ) :
    (selectedData L G).primary j (selectedGenerator L G n) =
      exp (-(Targets.order (Targets.generator n) (some j) : ℤ)) := by
  let B := primaryBirth L G j
  let p := B.prime
  let F := permanentFibre L G p
  let extra := withPoint upper q p
  have hF : F.primary = some (j,B.tuple) := primary_fibre L G j
  by_cases hn : j/2 ≤ n
  · let i : F.Component extra := some (F.primarySide extra hF)
    have h := (processed_normalized q upper (primary_processed L G j n hn) i).1
    have hl : F.label i = some j := by simp [i,Fibre.label,hF]
    rw [hl] at h
    change B.tuple.valuation (RawWords.normalizedFactor (fun k ↦ algebraMap _ (FunctionField (r+1)) (siteRaw L G k)) normalizationPower n) = _
    rw [localTuple_normalized B.tuple (siteRaw L G)]
    change Padic.mulValuation (RawWords.normalizedFactor _ normalizationPower n) = _
    change Padic.mulValuation (RawWords.normalizedFactor (fun k ↦ F.componentEval c extra (some (F.primarySide extra hF)) (siteRaw L G k)) normalizationPower n) = _ at h
    simpa only [F.primary_eval c extra hF] using h
  · have h0 : (0 : Fin (r+1) → GeometricField) ∈ (standardGeometry r).fixed := by simp [standardGeometry]
    have hu (i) (hi : i ≤ n) : (selectedData L G).primary j (rawValue (selectedData L G) i) = 1 :=
      primary_unit_of_earlier L G h0 j i (by omega)
    rw [Targets.order_zero_later_birth n j (by omega)]
    simp only [selectedGenerator, RawWords.normalizedFactor, map_div₀, map_prod, map_pow, hu n le_rfl]
    rw [Finset.prod_eq_one (fun i hi ↦ by rw [hu i (Finset.mem_range.mp hi).le,one_pow])]
    simp

theorem realized_guard (p : PrimeIndex) (n : ℕ) :
    (selectedData L G).guard p (selectedGenerator L G n) = 1 := by
  by_cases hp : p ∈ (permanentBatch L G n).processed
  · let F := permanentFibre L G p
    let extra := withPoint upper q p
    have h := (processed_normalized q upper hp (none : F.Component extra)).1
    change F.guard.tuple.valuation (RawWords.normalizedFactor (fun k ↦ algebraMap _ (FunctionField (r+1)) (siteRaw L G k)) normalizationPower n) = _
    rw [localTuple_normalized F.guard.tuple (siteRaw L G)]
    change GuardUnramified.valuation p.val (GaloisField p.val F.guard.degree) (RawWords.normalizedFactor (fun k ↦ F.componentEval c extra none (siteRaw L G k)) normalizationPower n) = exp (-(Targets.order (Targets.generator n) none : ℤ)) at h
    simpa only [F.guard_eval, Targets.order, Nat.cast_zero, neg_zero, exp_zero] using h
  · exact not_processed_guard_unit L G hp

theorem realizedProfiles : VerticalProfiles (selectedData L G) normalizationPower where
  b n j := by simpa only [Targets.generator_stage, Targets.b_order] using realized_primary q upper j (Generator.b n).stage
  q n j := by simpa only [Targets.generator_stage, Targets.q_order] using realized_primary q upper j (Generator.q n).stage
  guard := realized_guard q upper

def realizedChoices : ProfileChoices (selectedData L G) :=
  selectedProfileChoices L G (raw_not_divisible_first L) (realizedProfiles q upper)

end UnconditionalCounterexample.MultivariateSelection
