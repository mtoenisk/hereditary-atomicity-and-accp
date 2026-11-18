import UnconditionalCounterexample.ConstructionWords
import UnconditionalCounterexample.MixedStageSelection

/-!
# Actual finite word choices with one or two local branches

The existing DegreePlan supplies the same normalization exponent, predecessor
word denominators and reserved geometric tests. Transcendence at exactly the
active local arguments proves their nonvanishing. The mixed finite selector
then produces one raw polynomial satisfying all prefix requirements.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedConstructionWords

open Polynomial RawWords

variable {n : ℕ} {P : ℕ → ℚ[X]} {oldE : ℕ → ℕ}

open LocalStageSelection ShiftedEisenstein
open ConstructionWords
variable {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (paired : ι → Prop) (ell : ℕ) [Fact ell.Prime] (plan : DegreePlan n P oldE)
    (x v : ∀ j, Bool → ℚ_[p j]) (precision : ι → Bool → ℕ)

/-- The chosen numerator at a prefix. The word list, stage precision,
geometric tests and both kinds of denominator are computed from that prefix. -/
structure Choice where
  N : ι → ℕ
  coeff : Fin (plan.degree - 1) → ℚ
  positive_multiple : ∀ i, ∃ e : ℕ, 0 < e ∧ N i = (ell - 1) * e
  witnesses :
    let r := plan.degree - 1
    let c := SignedConstant.constant p N (r+1)
    let F := monicFamily r c coeff
    F.Monic ∧ F.natDegree = plan.degree ∧ F.coeff 0 = c ∧ Irreducible F ∧
    (∀ k prime, prime.Prime → prime ∣ (F.coeff k).den → ∃ j, prime = p j) ∧
    (∀ j,
      let H := fun w => (plan.wordDen w).map (algebraMap ℚ ℚ_[p j])
      let B := plan.denValue p x j
      let J := MixedStageSelection.fixedRemainder (paired j) (x j) B (v j) (r+1)
      let q0 := fun l : Fin r =>
        (MixedStageSelection.localTarget (paired j) (x j) B (v j) (r+1) c).coeff (l.val+1)
      ClearedAtPrime (p j) (n+1) c J Finset.univ H ∧
        MixedStageSelection.ConditionsAtPrime (p j) (paired j) r (n+1) c q0 (fun l => (coeff l : ℚ_[p j]))
          (x j) B (v j) (precision j) Finset.univ H StageWord.latestExponent) ∧
    (∀ test ∈ plan.tests, test.Holds (F.map (algebraMap ℚ (AlgebraicClosure ℚ)))) ∧
    ∃ model : ℤ_[ell][X], model.Monic ∧
      model.map (algebraMap ℤ_[ell] ℚ_[ell]) = F.map (algebraMap ℚ ℚ_[ell]) ∧
      model.map (PadicInt.toZModPow 1) = (X - C 1) ^ (r+1) ∧
      PadicInt.toZModPow 2 (model.eval 1) = (ell : ZMod (ell ^ 2))

theorem choice_nonempty (hinj : Function.Injective p) (hfresh : ∀ i, p i ≠ ell)
    (hP : ∀ j < n, (P j).Monic) (htrans : ∀ j b, MixedStageSelection.Active (paired j) b → Transcendental ℚ (x j b))
    (hsep : ∀ j, paired j → x j false ≠ x j true)
    (hv : ∀ j b, MixedStageSelection.Active (paired j) b → v j b ≠ 0) :
    Nonempty (Choice p paired ell plan x v precision) := by
  classical
  let r := plan.degree - 1
  have hd : r+1 = plan.degree := by dsimp [r]; have := plan.large_degree; omega
  have hr : 2 ≤ r := by have := plan.large_degree; omega
  have hx (j : ι) (b : Bool) (hb : MixedStageSelection.Active (paired j) b) : x j b ≠ 0 := by
    intro h
    exact X_ne_zero ((transcendental_iff.mp (htrans j b hb)) X (by simp [h]))
  have hB (j : ι) (b : Bool) (hb : MixedStageSelection.Active (paired j) b) : plan.denValue p x j b ≠ 0 := by
    rw [DegreePlan.denValue, ← eval_map]
    exact old_product_eval_ne_zero_of_transcendental n P hP _ _ (htrans j b hb)
  let H (j : ι) (w : Word n) := (plan.wordDen w).map (algebraMap ℚ ℚ_[p j])
  have hH (j : ι) (w : Word n) (_ : w ∈ (Finset.univ : Finset (Word n))) (b : Bool) (hb : MixedStageSelection.Active (paired j) b) :
      (H j w).eval (x j b) ≠ 0 :=
    old_product_eval_ne_zero_of_transcendental n P hP _ _ (htrans j b hb)
  obtain ⟨_, N, coeff, hmult, _, _, hmonic, hdeg, hzero, hirr, hsupp, hlocal, hgeom, hmodel⟩ :=
    MixedStageSelection.exists_stage_polynomial p hinj paired ell hfresh r (n+1) hr (by omega)
      x (plan.denValue p x) v precision hx hsep hB hv Finset.univ H StageWord.latestExponent
      (fun w _ => Nat.ne_of_gt w.latestExponent_bounds.1) hH plan.tests plan.tests_valid
  exact ⟨⟨N, coeff, hmult, hmonic, hdeg.trans hd, hzero, hirr, hsupp, hlocal, hgeom, hmodel⟩⟩


end UnconditionalCounterexample.MixedConstructionWords
