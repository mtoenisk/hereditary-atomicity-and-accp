import UnconditionalCounterexample.Variations.MultivariateSelectionActual
import UnconditionalCounterexample.Variations.PrivateGuardsTripleStage

/-! # Arithmetic and recovery tests at the regular primes of a punctured history -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection MultivariateInfinity

variable {r n : ℕ} {M : ℕ → Type*} {p : PrimeIndex}

private theorem regular_nonzero (F : Fibre r p) (c : Fin (r+1) → ℚ) (i : F.Component false)
    (g : Poly r) (hg : g ≠ 0) : F.componentEval c false i g ≠ 0 := by
  cases i with
  | none =>
    intro he
    apply hg
    apply F.guard.independent
    rw [map_zero]
    let L := GuardUnramified.LocalField p.val (GaloisField p.val F.guard.degree)
    change eval₂ (Rat.castHom L) _ g = 0 at he
    change eval₂ (algebraMap ℚ L) _ g = 0
    rwa [show algebraMap ℚ L = Rat.castHom L from Subsingleton.elim ..]
  | some u =>
    cases h : F.primary with
    | none =>
      have hu := u.property
      simp [h] at hu
    | some j =>
      intro he
      apply hg
      apply j.2.independent
      rw [map_zero]
      change eval₂ (Rat.castHom ℚ_[p.val]) (F.sidePoints c false u) g = 0 at he
      change eval₂ (algebraMap ℚ ℚ_[p.val]) j.2.x g = 0
      simpa only [Fibre.sidePoints, h, Option.elim_some,
        show algebraMap ℚ ℚ_[p.val] = Rat.castHom _ from Subsingleton.elim ..] using he

structure RegularTests (h : History r M n) (F : Fibre r p) (c : Fin (r+1) → ℚ) (N : ℕ) (f : MvPolynomial (Fin (r+1)) ℚ_[p.val]) : Prop where
  values : ∀ i : F.Component false, aeval (F.guard.points (F.sidePoints c false) i) f ∈ mixedSet h (F.componentEval c false i) (F.localValuation i) p.val (F.label i)
  denominators : ∀ s ≤ n, ∀ w : BoundedWord n,
    RecoveryGenerators.denScale (p.val : ℚ_[p.val]) Padic.norm_p_lt_one s (wordLocal (p := p) h w) + n*n ≤
      ((F.generators c false).genScale p.val Padic.norm_p_lt_one s + N) * w.latestExponent
  coefficients : ∀ s ≤ n, ∀ m,
    ‖(p.val : ℚ_[p.val]) ^ N * scaledCoefficient ((p.val : ℚ_[p.val])^s)
        ((p.val : ℚ_[p.val]) ^ ((F.generators c false).genScale p.val Padic.norm_p_lt_one s)) m f -
      scaledCoefficient ((p.val : ℚ_[p.val])^s)
        ((p.val : ℚ_[p.val]) ^ ((F.generators c false).genScale p.val Padic.norm_p_lt_one s)) m
          ((F.generators c false).direction p.val n)‖ ≤ ‖(p.val : ℚ_[p.val])‖^(n*n)
  gradients : ∀ i : F.Component false, ∀ w : BoundedWord n, ∃ α : F.guard.Field i,
    α ≠ 0 ∧ ‖α⁻¹‖ ≤ ‖(p.val : ℚ_[p.val])‖^(n*n) ∧
    ‖α⁻¹ • residueWordGradient (F.guard.points (F.sidePoints c false) i) f (wordLocal (p := p) h w) w.latestExponent -
      ∑ j : Fin (F.generators c false).count,
        (algebraMap ℚ_[p.val] (F.guard.Field i) (p.val : ℚ_[p.val]) ^ n)^j.val •
          (fun l => aeval (F.guard.points (F.sidePoints c false) i) (pderiv l ((F.generators c false).gen j)))‖ ≤
          ‖(p.val : ℚ_[p.val])‖^(n*n)

theorem regularOpen (h : History r M n) (F : Fibre r p) (c : Fin (r+1) → ℚ)
    (d : ℕ) (hd : F.floor c false n ≤ d) (leading : LocalPoly r p)
    (hL : leading.totalDegree ≤ d) :
    ∃ L : OpenLower r d p, ∃ N : ℕ, ∀ q : LocalPoly r p, q.totalDegree < d →
      (fun m => q.coeff m) ∈ L.neighborhood → RegularTests h F c N (leading + q) := by
  classical
  let u := F.guard.points (F.sidePoints c false)
  let φ := F.componentEval c false
  have hD (i : F.Component false) : φ i (oldDenominator h) ≠ 0 :=
    regular_nonzero F c i _ (oldDenominator_ne_zero h)
  have hH (i : F.Component false) (w : BoundedWord n) : aeval (u i) (wordLocal (p := p) h w) ≠ 0 := by
    change eval₂Hom _ _ (MvPolynomial.map _ _) ≠ 0
    rw [eval₂Hom_map_hom, ← IsScalarTower.algebraMap_eq ℚ ℚ_[p.val] (F.guard.Field i)]
    exact regular_nonzero F c i _ (wordDen_ne_zero h w)
  obtain ⟨N,T,hT,U,hU,H⟩ := (F.generators c false).exists_recovery_stage p.val
    (Nat.cast_ne_zero.mpr p.property.ne_zero) Padic.norm_p_lt_one
    (F.guard.points_generate _) (F.points_injective c false) n d hd leading hL
    (fun i => mixedRaw h (φ i) (F.localValuation i) p.val (F.label i))
    (fun i => mixedRaw_ne_zero h (φ i) _ _ (F.localValuation_prime i) _ (hD i))
    (fun i => mixedSet h (φ i) (F.localValuation i) p.val (F.label i))
    (fun i => mixedSet_mem h (φ i) _ _ (F.localValuation_prime i)
      (F.localValuation_compat i) _ (hD i))
    (wordLocal h) (fun w : BoundedWord n => w.latestExponent) (fun w => w.latestExponent_bounds.1) hH
  refine ⟨⟨T,hT,U,hU⟩,N,fun q hq hqU => ?_⟩
  obtain ⟨hv,hdn,hco,hgr⟩ := H q hq hqU
  exact ⟨hv,hdn,hco,hgr⟩

end UnconditionalCounterexample.Variations.PrivateGuards.Live
