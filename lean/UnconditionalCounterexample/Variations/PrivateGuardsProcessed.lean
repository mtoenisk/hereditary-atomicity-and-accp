import UnconditionalCounterexample.Variations.PrivateGuardsTablePermanence
import UnconditionalCounterexample.Variations.PrivateGuardsTripleReturn
import UnconditionalCounterexample.Variations.PrivateGuardsEvaluated
import UnconditionalCounterexample.Variations.MultiDomainEvaluated

/-!
# Actual normalized arithmetic in every processed public and private fibre

The unramified guard has one permanent tuple. Its evaluation is read from
the regular schedule until a private pair is present and from the joint
three-point schedule thereafter.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection MultiDomain WithZero

variable {r d : ℕ} {K : Type*} [Field K] [CharZero K]
  (P : TablePolicy r K) (q : PrimeIndex) (c : Fin (r+1) → ℚ) (C : Config r d)

local notation "ruleP" => tableRule P q c
local notation "T" => publicPath P q c C

theorem processed_primary_mem (j n : ℕ) (hn : j/2 ≤ n) :
    let φ := (aeval (R := ℚ) (((T).places.primary j).x)).toRingHom
    φ (main C ruleP n) ∈ mixedSet (before C ruleP n) φ Padic.mulValuation ((T).places.primes j).val (some j) := by
  intro φ
  let F := (T).permanentFibre ((T).places.primes j)
  have hF : F.primary = some (j,(T).places.primary j) := (T).primary_fibre j
  let side := F.primarySide false hF
  let i : F.Component false := some side
  have he : F.componentEval c false i = φ := RingHom.ext (F.primary_eval c false hF)
  have hlabel : F.label i = some j := by simp [i,Fibre.label,hF]
  obtain ⟨N,hN⟩ := guarded_tests P q c C n _ ((T).primary_processed j n hn)
  have hs : ∀ k : Fin n, (before C ruleP n k).prime ≠ (T).places.primes j :=
    fun k => (primary_ne_private P q c C j k.val).symm
  have hv := (hN.regularly hs).values i
  change aeval (F.guard.points (F.sidePoints c false) i)
    (MvPolynomial.map (algebraMap ℚ ℚ_[((T).places.primes j).val]) (main C ruleP n)) ∈
    mixedSet (before C ruleP n) (F.componentEval c false i) (F.localValuation i) ((T).places.primes j).val (F.label i) at hv
  rw [F.componentEval_baseChange,he,hlabel] at hv
  exact hv

theorem processed_guard_mem (p : PrimeIndex) (n : ℕ) (hp : p ∈ ((T).batch n).processed) :
    let φ := (aeval (R := ℚ) (((T).places.guard p).x)).toRingHom
    φ (main C ruleP n) ∈ mixedSet (before C ruleP n) φ ((T).places.guardVal p) p.val none := by
  intro φ
  let F := (T).permanentFibre p
  obtain ⟨N,hN⟩ := guarded_tests P q c C n p hp
  by_cases hprivate : ∃ j : Fin n, (before C ruleP n j).prime = p
  · obtain ⟨j,rfl⟩ := hprivate
    let g := F.guard
    let s := (before C ruleP n j).pair
    have hv := tripleTests_mixedSet s g _ (hN.privately j rfl) none
    rw [aeval_map_algebraMap] at hv
    exact hv
  · have he : F.componentEval c false none = φ := RingHom.ext (F.guard_eval c false)
    have hv := (hN.regularly (fun j hj => hprivate ⟨j,hj⟩)).values none
    change aeval (F.guard.points (F.sidePoints c false) none) (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (main C ruleP n)) ∈
      mixedSet (before C ruleP n) (F.componentEval c false none) (F.localValuation (extra := false) none) p.val (F.label (extra := false) none) at hv
    rw [F.componentEval_baseChange,he] at hv
    exact hv

theorem processed_private_mem {j n : ℕ} (hj : j < n) (b : Bool) :
    let s := (event C ruleP j).pair
    let φ := (aeval (R := ℚ) (s.point b)).toRingHom
    φ (main C ruleP n) ∈ mixedSet (before C ruleP n) φ Padic.mulValuation (prime C ruleP j).val none := by
  intro s φ
  let g := ((T).permanentFibre (prime C ruleP j)).guard
  let k : Fin n := ⟨j,hj⟩
  have hp := (path_extra P q c C n).1 (extra_private (before C ruleP n) k)
  obtain ⟨N,hN⟩ := guarded_tests P q c C n _ hp
  have hv := tripleTests_mixedSet s g _ (hN.privately k rfl) (some b)
  rw [aeval_map_algebraMap] at hv
  exact hv

variable {E : Type*} [Field E] [Algebra ℚ E] {v : Valuation E ℤᵐ⁰}

/-- Transport along an actual independent tuple intertwines field generators
with the mixed polynomials evaluated on the completed sequence. -/
theorem tuple_generator (t : LocalTuple (r+1) v) (n : ℕ) :
    t.valuation ((family C ruleP).generator mixedPower n) = v (evaluated C ruleP (aeval t.x).toRingHom n) := by
  let e := IndependentTuples.evaluation t.x t.independent
  have he (f : Poly r) : e (algebraMap (Poly r) (FunctionField (r+1)) f) = aeval t.x f :=
    IsFractionRing.lift_algebraMap (K := FunctionField (r+1)) (g := (aeval t.x : Poly r →ₐ[ℚ] E).toRingHom)
      t.independent f
  change v (e (normalizedMain (fun j => algebraMap _ _ (main C ruleP j)) (fun j => algebraMap _ _ (puncture C ruleP j)) mixedPower n)) = _
  simp only [normalizedMain,map_div₀,map_prod,map_pow,map_mul,he,evaluated,Function.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]

end UnconditionalCounterexample.Variations.PrivateGuards.Live
