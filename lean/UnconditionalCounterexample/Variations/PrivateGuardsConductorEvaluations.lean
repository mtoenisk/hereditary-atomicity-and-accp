import UnconditionalCounterexample.Variations.PrivateGuardsConductorWords
import UnconditionalCounterexample.Variations.PrivateGuardsDomain
import UnconditionalCounterexample.Variations.DimensionClosedEvaluation
import UnconditionalCounterexample.Variations.PrivateGuardsTablePermanence

/-! # Original-domain integrality on the public and private conductor fibres -/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection.TablePath
open GuardSupport Variations

variable {r : ℕ} {q : PrimeIndex} (T : TablePath r q)

private theorem origin (p : PrimeIndex) (j : ℕ) (h : (T.permanentFibre p).primary.map Prod.fst = some j) :
    p = (if j % 2 = 0 then (T.batch (j/2)).first.prime else (T.batch (j/2)).second.prime) := by
  let n := T.firstAppearance p
  let B := T.batch n
  have hv := T.valid n
  by_cases h₁ : p = B.first.prime
  · have hf := (congrArg Fibre.primary (T.frozen (T.processed_covered n hv.first_mem))).symm.trans (hv.first_at _)
    have hr : (T.permanentFibre B.first.prime).primary.map Prod.fst = some (2*n) := by rw [hf]; rfl
    rw [← h₁,h] at hr
    rw [Option.some.inj hr,show 2*n%2 = 0 by omega,ite_eq_left rfl,show 2*n/2 = n by omega]
    exact h₁
  by_cases h₂ : p = B.second.prime
  · have hf := (congrArg Fibre.primary (T.frozen (T.processed_covered n hv.second_mem))).symm.trans (hv.second_at _)
    have hr : (T.permanentFibre B.second.prime).primary.map Prod.fst = some (2*n+1) := by rw [hf]; rfl
    rw [← h₂,h] at hr
    rw [Option.some.inj hr,ite_eq_right (by omega : (2*n+1)%2 ≠ 0),show (2*n+1)/2 = n by omega]
    exact h₂
  have hn := hv.other_at p (T.first_mem p) (T.new_at_first p) h₁ h₂
  rw [T.frozen] at hn
  simp [hn] at h

theorem prime_of_label (p : PrimeIndex) (j : ℕ) (h : (T.permanentFibre p).primary.map Prod.fst = some j) :
    p = ((T).primaryBirth j).prime := (T.origin p j h).trans (T.origin _ j (T.primary_label j)).symm

end UnconditionalCounterexample.MultivariateSelection.TablePath

namespace UnconditionalCounterexample.Variations.PrivateGuards.Live
open GuardSupport MvPolynomial MultivariateSelection MultiDomain MultivariateRecovery MultivariateWordRecovery

section SelectedPoint
variable {r d : ℕ} {J : ℕ → Type*} {c : Fin (r+1) → ℚ}
  (C : Config r d) (R : Rule r J c) (p : PrimeIndex)
  {E : Type*} [Field E] [Algebra ℚ_[p.val] E] [Algebra ℚ E] [IsScalarTower ℚ ℚ_[p.val] E]

instance actualPole_isLocalization : IsLocalization (actualDenominators C R) (actualPole C R) :=
  inferInstanceAs (IsLocalization (inverted (Set.range (main C R)) (family C R).puncture)
    ((family C R).poleAlgebra (fun n => (event C R n).irreducible)))

theorem fibreRetained (u : Fin (r+1) → E) (hu : AlgebraicIndependent ℚ u) :
    ∀ s : (actualDenominators C R).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val])), aeval u s.val ≠ 0 := by
  rintro ⟨_,f,hf,rfl⟩
  change eval₂Hom _ _ (MvPolynomial.map _ _) ≠ 0
  rw [eval₂Hom_map_hom,← IsScalarTower.algebraMap_eq ℚ ℚ_[p.val] E]
  change aeval u f ≠ 0
  apply (map_ne_zero_iff _ hu).mpr
  induction hf using Submonoid.closure_induction with
  | mem f h =>
    rcases h with ⟨n,rfl⟩ | ⟨n,rfl⟩
    · exact (event C R n).irreducible.ne_zero
    · exact (event C R n).irreducible_puncture.ne_zero
  | one => exact one_ne_zero
  | mul f g _ _ hf hg => exact mul_ne_zero hf hg

variable (A : Type*) [CommRing A] [Algebra ℚ_[p.val] A] [Algebra (LocalPoly r p) A]
    [IsScalarTower ℚ_[p.val] (LocalPoly r p) A]
    [IsLocalization ((actualDenominators C R).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]))) A]

def fibrePointEval (u : Fin (r+1) → E) (hu : AlgebraicIndependent ℚ u) : A →ₐ[ℚ_[p.val]] E :=
  closedPointEval _ A u (fibreRetained C R p u hu)

theorem fibrePointEval_polynomial (u : Fin (r+1) → E) (hu : AlgebraicIndependent ℚ u) (f : LocalPoly r p) :
    fibrePointEval C R p A u hu (algebraMap _ A f) = aeval u f :=
  closedPointEval_polynomial _ _ _ _ _

end SelectedPoint

variable {r d : ℕ} {K : Type*} [Field K] [CharZero K]
  (P : TablePolicy r K) (q : PrimeIndex) (c : Fin (r+1) → ℚ) (C : Config r d)
local notation "L" => tableRule P q c
local notation "T" => publicPath P q c C
local notation "B" => actualPole C L
local notation "M" => actualDenominators C L
abbrev conductorDomain := domain C L (fun j => ((T).places.primary j).valuation) (fun p => ((T).places.guard p).valuation)
local notation "D" => conductorDomain P q c C

def originalPointValue {E : Type*} [Field E] [Algebra ℚ E] (x : Fin (r+1) → E)
    (hi : AlgebraicIndependent ℚ x) : B →+* E := (IndependentTuples.evaluation x hi).comp (B).subtype

theorem originalPointValue_polynomial {E : Type*} [Field E] [Algebra ℚ E] (x : Fin (r+1) → E)
    (hi : AlgebraicIndependent ℚ x) (f : Poly r) :
    originalPointValue P q c C x hi (algebraMap (Poly r) (B) f) = aeval x f :=
  IsFractionRing.lift_algebraMap (K := FunctionField (r+1)) (g := (aeval x : Poly r →ₐ[ℚ] E).toRingHom) hi f

theorem originalPointValue_base {p : PrimeIndex} {E : Type*} [Field E] [Algebra ℚ_[p.val] E]
    [Algebra ℚ E] [IsScalarTower ℚ ℚ_[p.val] E]
    (A : Type*) [CommRing A] [Algebra ℚ_[p.val] A] [Algebra (LocalPoly r p) A]
    [IsScalarTower ℚ_[p.val] (LocalPoly r p) A] [IsLocalization ((M).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]))) A]
    (x : Fin (r+1) → E) (hi : AlgebraicIndependent ℚ x)
    (hr : ∀ s : (M).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val])), aeval x s.val ≠ 0) (b : B) :
    closedPointEval _ A x hr (baseElement (K := ℚ_[p.val]) M A b) = originalPointValue P q c C x hi b :=
  closedPointEval_baseElement _ _ _ _ _ (originalPointValue_polynomial P q c C x hi) b

theorem regularPoint_independent (p : PrimeIndex) (i : ((T).permanentFibre p).Component false) :
    AlgebraicIndependent ℚ (((T).permanentFibre p).guard.points (((T).permanentFibre p).sidePoints c false) i) := by
  let F := (T).permanentFibre p
  cases i with
  | none => exact F.guard.independent
  | some t =>
    cases hh : F.primary with
    | none => have h := t.property; change (F.primary.isSome || false) = true at h; simp [hh] at h
    | some j =>
      change AlgebraicIndependent ℚ (F.sidePoints c false t)
      rw [Fibre.sidePoints,hh,Option.elim_some]
      exact j.2.independent

private theorem padic_norm_of_integral {p : PrimeIndex} (v : ℚ_[p.val]) (h : Padic.mulValuation v ≤ 1) :
    ‖v‖ ≤ 1 := by
  exact le_of_not_gt (fun hn => h.not_gt (by
    simpa only [map_one] using (Padic.norm_lt_norm_iff_mulValuation_lt.mp
      (show ‖(1 : ℚ_[p.val])‖ < _ from (norm_one (α := ℚ_[p.val])).trans_lt hn))))

theorem side_coordinate_norm (p : PrimeIndex) (t : ((T).permanentFibre p).Side false) :
    ‖((T).permanentFibre p).sidePoints c false t 0‖ ≤ 1 := by
  let F := (T).permanentFibre p
  cases h : F.primary with
  | none => have hh := t.property; change (F.primary.isSome || false) = true at hh; simp [h] at hh
  | some j =>
    change ‖F.sidePoints c false t 0‖ ≤ 1
    rw [Fibre.sidePoints,h,Option.elim_some]
    exact padic_norm_of_integral _ (j.2.integral 0)

/-- Read the actual domain integrality directly on the public fibre. -/
theorem regularPoint_integral (p : PrimeIndex) (i : ((T).permanentFibre p).Component false) (z : D) :
    ‖originalPointValue P q c C _ (regularPoint_independent P q c C p i) (algebraMap (D) (B) z)‖ ≤ 1 := by
  let F := (T).permanentFibre p
  have hm := (mem_domain C L _ _).mp z.property
  cases i with
  | none => exact (GuardUnramified.norm_le_one_iff_valuation _ _ _).mpr (hm.2.2.1 p)
  | some t =>
    cases hh : F.primary with
    | none => have h := t.property; change (F.primary.isSome || false) = true at h; simp [hh] at h
    | some jt =>
      obtain ⟨j,u⟩ := jt
      have hp := (T).prime_of_label p j (show F.primary.map Prod.fst = some j from by rw [hh]; rfl)
      subst p
      have hf := (T).primary_fibre j
      rw [show ((T).permanentFibre ((T).primaryBirth j).prime).primary = _ from hh] at hf
      obtain rfl : u = ((T).primaryBirth j).tuple := congrArg Prod.snd (Option.some.inj hf)
      apply padic_norm_of_integral
      have hu : F.sidePoints c false t = ((T).primaryBirth j).tuple.x := by
        rw [Fibre.sidePoints,hh,Option.elim_some]
      have hIndependent : AlgebraicIndependent ℚ (F.sidePoints c false t) :=
        regularPoint_independent P q c C ((T).primaryBirth j).prime (some t)
      change Padic.mulValuation (IndependentTuples.evaluation (F.sidePoints c false t) hIndependent (z : FunctionField (r+1))) ≤ 1
      simp only [hu]
      exact hm.2.1 j

/-- The private and ordinary valuations at this puncture, and the public
unramified guard at the same rational prime, all occur in the domain. -/
theorem privatePoint_integral (j : ℕ)
    (i : Option Bool) (z : D) :
    let s := (event C L j).pair; let g := ((T).permanentFibre (prime C L j)).guard
    ‖originalPointValue P q c C (s.triple g i) (s.triple_independent g i) (algebraMap (D) (B) z)‖ ≤ 1 := by
  have hm := (mem_domain C L _ _).mp z.property
  cases i with
  | none => exact (GuardUnramified.norm_le_one_iff_valuation _ _ _).mpr (hm.2.2.1 _)
  | some b =>
    cases b
    · exact padic_norm_of_integral _ (hm.2.2.2.1 j)
    · exact padic_norm_of_integral _ (hm.2.2.2.2 j)

theorem regularPoint_base_integral (p : PrimeIndex) (A : Type*) [CommRing A] [Algebra ℚ_[p.val] A]
    [Algebra (LocalPoly r p) A] [IsScalarTower ℚ_[p.val] (LocalPoly r p) A]
    [IsLocalization ((M).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]))) A]
    (i : ((T).permanentFibre p).Component false) (z : D) :
    ‖fibrePointEval C L p A _ (regularPoint_independent P q c C p i)
      (baseElement (K := ℚ_[p.val]) M A (algebraMap (D) (B) z))‖ ≤ 1 := by
  rw [fibrePointEval,originalPointValue_base P q c C]
  exact regularPoint_integral P q c C p i z

theorem privatePoint_base_integral (j : ℕ) (A : Type*) [CommRing A]
    [Algebra ℚ_[(prime C L j).val] A] [Algebra (LocalPoly r (prime C L j)) A]
    [IsScalarTower ℚ_[(prime C L j).val] (LocalPoly r (prime C L j)) A]
    [IsLocalization ((M).map (MvPolynomial.map (algebraMap ℚ ℚ_[(prime C L j).val]))) A]
    (i : Option Bool) (z : D) :
    let s := (event C L j).pair; let g := ((T).permanentFibre (prime C L j)).guard
    ‖fibrePointEval C L (prime C L j) A _ (s.triple_independent g i)
      (baseElement (K := ℚ_[(prime C L j).val]) M A (algebraMap (D) (B) z))‖ ≤ 1 := by
  dsimp only
  rw [fibrePointEval,originalPointValue_base P q c C]
  exact privatePoint_integral P q c C j i z

end UnconditionalCounterexample.Variations.PrivateGuards.Live
