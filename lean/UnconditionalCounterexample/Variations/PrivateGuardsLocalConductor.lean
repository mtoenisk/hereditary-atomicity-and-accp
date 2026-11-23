import UnconditionalCounterexample.Variations.PrivateGuardsConductorEvaluations
import UnconditionalCounterexample.Variations.PrivateGuardsConductorWords
import UnconditionalCounterexample.Variations.PrivateGuardsTablePermanence
import UnconditionalCounterexample.Variations.DimensionScheduledConductor

/-!
# Local recovery in the punctured-domain construction

At a public prime the recovered kernel sees its permanent guard and optional primary.
At a private prime it sees the guard and both members of the installed pair. In each
case the conductor is computed in the actual tensor image of the same subring of the
punctured horizontal algebra.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection MultivariateRecovery LocalAlgebra
  TransportedIntegralImage RadicalConductor
open scoped TensorProduct

variable {r d : ℕ} {k : Type*} [Field k] [CharZero k] (P : TablePolicy r k) (q : PrimeIndex)
  (c : Fin (r+1) → ℚ) (C : Config r d)

local notation "liveRule" => tableRule P q c
local notation "pole" => actualPole C liveRule
local notation "denoms" => actualDenominators C liveRule

private structure MixedRecoveryTests (p : PrimeIndex) {τ : Type*} {E : τ → Type*}
    [∀ i, NontriviallyNormedField (E i)] [∀ i, NormedAlgebra ℚ_[p.val] (E i)]
    (u : ∀ i, Fin (r+1) → E i) (G : RecoveryGenerators (K := ℚ_[p.val]) u) (n N : ℕ) : Prop where
  denominator : ∀ s ≤ n, ∀ w : BoundedWord n, RecoveryGenerators.denScale (p.val : ℚ_[p.val]) Padic.norm_p_lt_one s
    (wordLocal (before C liveRule n) w) + n*n ≤ (G.genScale p.val Padic.norm_p_lt_one s + N) * w.latestExponent
  coefficients : ∀ s ≤ n, ∀ m, ‖(p.val : ℚ_[p.val])^N * scaledCoefficient ((p.val : ℚ_[p.val])^s)
    ((p.val : ℚ_[p.val])^(G.genScale p.val Padic.norm_p_lt_one s)) m
    (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (main C liveRule n)) -
    scaledCoefficient ((p.val : ℚ_[p.val])^s) ((p.val : ℚ_[p.val])^(G.genScale p.val Padic.norm_p_lt_one s)) m
      (G.direction p.val n)‖ ≤ ‖(p.val : ℚ_[p.val])‖^(n*n)
  gradients : ∀ i w, ∃ α : E i, α ≠ 0 ∧ ‖α⁻¹‖ ≤ ‖(p.val : ℚ_[p.val])‖^(n*n) ∧
    ‖α⁻¹ • residueWordGradient (u i) (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (main C liveRule n))
      (wordLocal (before C liveRule n) w) w.latestExponent -
      ∑ j : Fin G.count, (algebraMap ℚ_[p.val] (E i) (p.val : ℚ_[p.val]) ^ n)^j.val •
        (fun l => aeval (u i) (pderiv l (G.gen j)))‖ ≤ ‖(p.val : ℚ_[p.val])‖^(n*n)

variable (p : PrimeIndex) (A : Type*) [CommRing A] [Algebra ℚ_[p.val] A]
    [Algebra (LocalPoly r p) A] [IsScalarTower ℚ_[p.val] (LocalPoly r p) A]
    [IsLocalization ((actualDenominators C (tableRule P q c)).map
      (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]))) A] [IsNoetherianRing A]
    (T : Subring (actualPole C (tableRule P q c))) (hw : HasClearedMixedWords C (tableRule P q c) T)
    (hclear : ∀ x : actualPole C (tableRule P q c), ∃ n : ℕ, 0 < n ∧ (n : actualPole C (tableRule P q c)) * x ∈ T)

include hw hclear

private theorem conductor_of_mixed_tests {τ : Type*} [Finite τ] {E : τ → Type*}
    [∀ i, NontriviallyNormedField (E i)] [∀ i, NormedAlgebra ℚ_[p.val] (E i)]
    [∀ i, FiniteDimensional ℚ_[p.val] (E i)] [∀ i, IsUltrametricDist (E i)]
    [∀ i, CharZero (E i)] (u : ∀ i, Fin (r+1) → E i)
    (hind : ∀ i, AlgebraicIndependent ℚ (u i))
    (hgen : ∀ i, Algebra.adjoin ℚ_[p.val] (Set.range (u i)) = ⊤)
    (hdist : Function.Injective fun i ↦ RingHom.ker (aeval (R := ℚ_[p.val]) (u i)).toRingHom)
    (G : RecoveryGenerators (K := ℚ_[p.val]) u) (start : ℕ)
    (ht : ∀ n ≥ start, ∃ N, MixedRecoveryTests P q c C p u G n N)
    (ev : ∀ i, A →ₐ[ℚ_[p.val]] E i) (hev : ∀ i (f : LocalPoly r p), ev i (algebraMap _ A f) = aeval (u i) f)
    (hval : ∀ i (x : T), ‖ev i (baseElement (K := ℚ_[p.val]) denoms A (x : pole))‖ ≤ 1) :
    conductorIdeal (image p.val pole A (tensorEquiv (K := ℚ_[p.val]) denoms pole A) T) = RingHom.ker (AlgHom.pi ev) := by
  classical
  let e := tensorEquiv (K := ℚ_[p.val]) denoms pole A
  let U := image p.val pole A e T
  obtain ⟨b,hb⟩ := hw
  obtain ⟨a,_,j,hj,hs⟩ := exists_fixed_word_exponent (W := BoundedWord) (fun _ w ↦ w.latestExponent)
    (fun n w ↦ ∃ x ∈ T, algebraMap (Poly r) pole ((main C liveRule n)^w.latestExponent) =
      algebraMap _ pole (wordDen (before C liveRule n) w) * x) b start hb
  choose words heq x hx hrel using fun n ↦ (hs n).2
  choose N hn using fun n ↦ ht (j n) (hs n).1
  let F (n : ℕ) := MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (main C liveRule (j n))
  let H (n : ℕ) := wordLocal (p := p) (before C liveRule (j n)) (words n)
  let X (n : ℕ) : U := ⟨baseElement (K := ℚ_[p.val]) denoms A (x n), original_mem p.val pole A e T ⟨x n,hx n⟩⟩
  have htarget : (⨅ i, RingHom.ker (ev i)) = RingHom.ker (AlgHom.pi ev) := by
    ext z
    change (z ∈ ⨅ i, RingHom.ker (ev i)) ↔ AlgHom.pi ev z = 0
    rw [Ideal.mem_iInf, _root_.funext_iff]
    rfl
  rw [← htarget]
  apply conductor_of_scheduled_local_words ((denoms).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]))) e T hclear u ev hev
    hgen hdist hval G j hj F H N a X
  · intro n
    have h := MultivariateWordRecovery.word_relation (K := ℚ_[p.val]) denoms A (main C liveRule (j n))
      (wordDen (before C liveRule (j n)) (words n)) (words n).latestExponent (x n) (by simpa only [map_pow] using hrel n)
    change algebraMap _ A (F n ^ a) = algebraMap _ A (H n) * baseElement (K := ℚ_[p.val]) denoms A (x n)
    rw [mul_comm]
    simpa only [F,H,wordLocal,heq] using h
  · intro i n
    change aeval (u i) (wordLocal (p := p) (before C liveRule (j n)) (words n)) ≠ 0
    rw [wordLocal,aeval_map_algebraMap]
    exact fun hz ↦ wordDen_ne_zero _ _ ((hind i) (hz.trans (map_zero _).symm))
  · intro n s hsn
    simpa only [heq] using (hn n).denominator s hsn (words n)
  · intro n s hsn m
    exact (hn n).coefficients s hsn m
  · intro i n
    obtain ⟨α,_,hi,hd⟩ := (hn n).gradients i (words n)
    exact ⟨α,hi,by simpa only [heq,map_natCast] using hd⟩

local notation "path" => publicPath P q c C
local notation "fibre" => TablePath.permanentFibre path p

/-- At a prime that is never private, scheduled words recover the ideal of the
permanent public guard and its optional rational primary. -/
theorem regular_local_conductor (hregular : ∀ n, prime C liveRule n ≠ p)
    (ev : ∀ i : (fibre).Component false, A →ₐ[ℚ_[p.val]] (fibre).guard.Field i)
    (hev : ∀ i (f : LocalPoly r p), ev i (algebraMap _ A f) = aeval ((fibre).guard.points ((fibre).sidePoints c false) i) f)
    (hval : ∀ i (x : T), ‖ev i (baseElement (K := ℚ_[p.val]) denoms A (x : pole))‖ ≤ 1) :
    conductorIdeal (image p.val pole A (tensorEquiv (K := ℚ_[p.val]) denoms pole A) T) = RingHom.ker (AlgHom.pi ev) := by
  let G := (fibre).generators c false
  apply conductor_of_mixed_tests P q c C p A T hw hclear _ (regularPoint_independent P q c C p)
    ((fibre).guard.points_generate _) ((fibre).points_injective c false) G ((path).firstAppearance p + 1) _ ev hev hval
  intro n hn
  obtain ⟨N,hN⟩ := guarded_tests P q c C n p ((path).eventual_processed p hn)
  have h := hN.regularly (fun j ↦ hregular j.val)
  exact ⟨N,h.denominators,h.coefficients,h.gradients⟩

section Private
variable (j₀ : ℕ)
local notation "p₀" => prime C liveRule j₀
local notation "g₀" => Fibre.guard (TablePath.permanentFibre path p₀)
local notation "pair₀" => Round.pair (event C liveRule j₀)
variable (Z : Type*) [CommRing Z] [Algebra ℚ_[(prime C (tableRule P q c) j₀).val] Z]
  [Algebra (LocalPoly r (prime C (tableRule P q c) j₀)) Z]
  [IsScalarTower ℚ_[(prime C (tableRule P q c) j₀).val] (LocalPoly r (prime C (tableRule P q c) j₀)) Z]
  [IsLocalization ((actualDenominators C (tableRule P q c)).map
    (MvPolynomial.map (algebraMap ℚ ℚ_[(prime C (tableRule P q c) j₀).val]))) Z]
  [IsNoetherianRing Z]

/-- At the prime chosen in round `j₀`, scheduled words recover the ideal determined
by its unramified guard and both members of that same private pair. -/
theorem private_local_conductor (ev : ∀ i : Option Bool, Z →ₐ[ℚ_[(p₀).val]] (g₀).Field i)
    (hev : ∀ i (f : LocalPoly r p₀), ev i (algebraMap _ Z f) = aeval ((pair₀).triple g₀ i) f)
    (hval : ∀ i (x : T), ‖ev i (baseElement (K := ℚ_[(p₀).val]) denoms Z (x : pole))‖ ≤ 1) :
    conductorIdeal (image (p₀).val pole Z (tensorEquiv (K := ℚ_[(p₀).val]) denoms pole Z) T) = RingHom.ker (AlgHom.pi ev) := by
  let G := (pair₀).generators g₀
  apply conductor_of_mixed_tests P q c C p₀ Z T hw hclear _ ((pair₀).triple_independent g₀)
    ((g₀).points_generate _) ((pair₀).triple_distinct g₀) G (max ((path).firstAppearance p₀) j₀ + 1) _ ev hev hval
  intro n hn
  have hj : j₀ < n := (le_max_right _ _).trans_lt hn
  obtain ⟨N,hN⟩ := guarded_tests P q c C n p₀ ((path).eventual_processed p₀ ((le_max_left _ _).trans_lt hn))
  have h := hN.privately (⟨j₀,hj⟩ : Fin n) rfl
  exact ⟨N,h.denominators,h.coefficients,h.gradients⟩

end Private
end UnconditionalCounterexample.Variations.PrivateGuards.Live
