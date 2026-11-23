import UnconditionalCounterexample.Variations.PrivateGuardsConductorPowers
import UnconditionalCounterexample.Variations.PrivateGuardsConductorEvaluations
import UnconditionalCounterexample.Variations.PrivateGuardsLocalConductor

/-! # The integer conductor for the live ring with prescribed lower dimension -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultivariateSelection MultiDomain LocalAlgebra
  MultivariateRecovery RadicalConductor TransportedIntegralImage
open scoped TensorProduct

variable {r d : ℕ} (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
  (q : PrimeIndex) (c : Fin (r+1) → ℚ) (C : Config r d)

local notation "policy" => genericTablePolicy r K
local notation "liveRule" => tableRule policy q c
local notation "path" => publicPath policy q c C
local notation "D" => conductorDomain policy q c C
local notation "B" => actualPole C liveRule
local notation "M" => actualDenominators C liveRule

private abbrev localRing (p : PrimeIndex) :=
  Localization ((M).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val])))

private abbrev pointsMap (p : PrimeIndex) (G : ScreenedGuard r p) {τ : Type*}
    (u : ∀ i : Option τ, Fin (r+1) → G.Field i) (hi : ∀ i, AlgebraicIndependent ℚ (u i)) :=
  fun i ↦ fibrePointEval C liveRule p (localRing K q c C p) (u i) (hi i)

section Fibre
variable (p : PrimeIndex) (G : ScreenedGuard r p) {τ : Type*} [Finite τ]
  (u : ∀ i : Option τ, Fin (r+1) → G.Field i) (hi : ∀ i, AlgebraicIndependent ℚ (u i))
  (hgen : ∀ i, Algebra.adjoin ℚ_[p.val] (Set.range (u i)) = ⊤)
  (hdist : Function.Injective fun i ↦ RingHom.ker (aeval (R := ℚ_[p.val]) (u i)).toRingHom)

local notation "A" => localRing K q c C p
local notation "e" => tensorEquiv (K := ℚ_[p.val]) M B A
local notation "v" => pointsMap K q c C p G u hi
local notation "f" => algebraMap D B

include hgen hdist in
set_option maxHeartbeats 1200000 in
private theorem selected_tensor_power (T : Subring D) (n : ℕ)
    (hclear : ∀ x : B, ∃ m : ℕ, 0 < m ∧ (m : B)*x ∈ T.map f)
    (hint : ∀ i (x : D), ‖originalPointValue policy q c C (u i) (hi i) (f x)‖ ≤ 1)
    (hlocal : (∀ i (x : T.map f), ‖v i (baseElement (K := ℚ_[p.val]) M A (x : B))‖ ≤ 1) →
      conductorIdeal (image p.val B A e (T.map f)) = RingHom.ker (AlgHom.pi v))
    (hfill : (∀ i, v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (algebraMap (Poly r) B (X 0)))) = u i 0) →
      (∀ i (x : (f).range), ‖v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (x : B)))‖ ≤ 1) →
      (⨅ i, RingHom.ker (v i).toRingHom) ≤ conductorIdeal (image p.val B A e (T.map f)) →
      ¬p.val ∣ n → image p.val B A e (f).range ≤ image p.val B A e (T.map f)) :
    ∃ k : ℕ, (¬p.val ∣ n → k = 0) ∧ ∀ z ∈ IntegralTensorImage.image p.val B (f).range,
      (p.val : ℚ_[p.val] ⊗[ℚ] B)^k*z ∈ IntegralTensorImage.image p.val B (T.map f) := by
  have hv (i : Option τ) (x : (f).range) : ‖v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (x : B)))‖ ≤ 1 := by
    obtain ⟨y,hy⟩ := x.property
    rw [← hy]
    exact (originalPointValue_base policy q c C A (u i) (hi i) (fibreRetained C liveRule p (u i) (hi i)) (f y)) ▸ hint i y
  have hk : (⨅ i, RingHom.ker (v i).toRingHom) ≤ conductorIdeal (image p.val B A e (T.map f)) := by
    have hle : T.map f ≤ (f).range := by rintro _ ⟨y,_,rfl⟩; exact ⟨y,rfl⟩
    rw [hlocal (fun i x ↦ hv i ⟨x,hle x.property⟩)]
    intro z hz
    exact funext fun i ↦ (Ideal.mem_iInf.mp hz i : v i z = 0)
  have hcoord (i : Option τ) : v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (algebraMap (Poly r) B (X 0)))) = u i 0 := by
    exact (originalPointValue_base policy q c C A (u i) (hi i) (fibreRetained C liveRule p (u i) (hi i)) _).trans
      ((originalPointValue_polynomial policy q c C (u i) (hi i) (X 0)).trans (aeval_X ..))
  apply tensor_power_at_fibre G e (T.map f) (f).range v n _ hclear hv hk (hfill hcoord hv hk)
  intro y
  obtain ⟨g,hg⟩ := closedPointValues_surjective u hgen hdist y
  exact ⟨algebraMap (LocalPoly r p) A g,funext fun i ↦ (fibrePointEval_polynomial C liveRule p A (u i) (hi i) g).trans (congrFun hg i)⟩

end Fibre

variable [Uncountable K]

set_option maxHeartbeats 1200000 in
/-- Any subring containing cofinally many bounded words contains a positive
integer multiple of the full selected domain. -/
theorem integer_conductor_of_mixed_words (T : Subring D)
    (hw : HasMixedWords C liveRule (T.map (algebraMap D B))) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : D, (m : D)*z ∈ T := by
  classical
  let f := algebraMap D B
  let S := T.map f
  have hclear := RationalHull.exists_nat_mul_mem_of_hull_eq_top S (mixed_hull_eq_top C K q c S hw)
  have hwords := hw.cleared C liveRule
  obtain ⟨m,hm,h⟩ := integer_conductor_from_powers K q c C S f.range hw (fun n _ hX p ↦ by
    by_cases hp : ∃ j, prime C liveRule j = p
    · obtain ⟨j,rfl⟩ := hp
      let p := prime C liveRule j
      let F := (path).permanentFibre p
      let s := (event C liveRule j).pair
      let u := s.triple F.guard
      apply selected_tensor_power K q c C p F.guard u (s.triple_independent F.guard)
        (F.guard.points_generate _) (s.triple_distinct F.guard) T n hclear (fun i z ↦ privatePoint_integral policy q c C j i z)
      · exact fun hv ↦ private_local_conductor policy q c C S hwords hclear j (localRing K q c C p)
          _ (fun i g ↦ fibrePointEval_polynomial C liveRule p _ (u i) _ g) hv
      · exact fun hcoord hint hk hpn ↦ s.good_tensor_inclusion F.guard _ S f.range _ _ n hX hpn hcoord hint hk
    · let F := (path).permanentFibre p
      let u := F.guard.points (F.sidePoints c false)
      apply selected_tensor_power K q c C p F.guard u (regularPoint_independent policy q c C p)
        (F.guard.points_generate _) (F.points_injective c false) T n hclear (regularPoint_integral policy q c C p)
      · exact fun hv ↦ regular_local_conductor policy q c C p (localRing K q c C p) S hwords hclear
          (fun k he ↦ hp ⟨k,he⟩) _ (fun i g ↦ fibrePointEval_polynomial C liveRule p _ (u i) _ g) hv
      · exact fun hcoord hint hk hpn ↦ F.guard.good_tensor_inclusion _ S f.range _ _ n hX hpn
          (F.sidePoints c false) (side_coordinate_norm policy q c C p) hcoord hint hk)
  refine ⟨m,hm,fun z ↦ ?_⟩
  obtain ⟨y,hy,he⟩ := h (f z) ⟨z,rfl⟩
  have hfy : f y = f ((m : D)*z) := he.trans (by simp)
  have he' : y = (m : D)*z := Subtype.ext (congrArg (B).subtype hfy)
  exact he' ▸ hy

end UnconditionalCounterexample.Variations.PrivateGuards.Live
