import UnconditionalCounterexample.MixedStageSelection
import UnconditionalCounterexample.SingleLocalStageSelection

/-!
# Transfer for one or two active arguments

At a selected prime the vanishing polynomial has both linear factors.
At an omitted prime it has the guard factor alone. Both coefficient estimates
come from the same signed constant and the same stage polynomial.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedWordTransfer
open Polynomial LocalAlgebra MixedStageSelection

def vanishing {K : Type*} [Field K] (paired : Prop) (x : Bool → K) : RatFunc K := by
  classical
  exact if paired then (RatFunc.X - RatFunc.C (x false)) * (RatFunc.X - RatFunc.C (x true))
    else RatFunc.X - RatFunc.C (x true)

@[simp] theorem vanishing_pair {K : Type*} [Field K] {paired : Prop} (h : paired)
    (x : Bool → K) : vanishing paired x =
      (RatFunc.X - RatFunc.C (x false)) * (RatFunc.X - RatFunc.C (x true)) := by
  simp [vanishing, h]

@[simp] theorem vanishing_single {K : Type*} [Field K] {paired : Prop} (h : ¬ paired)
    (x : Bool → K) : vanishing paired x = RatFunc.X - RatFunc.C (x true) := by
  simp [vanishing, h]

theorem signed_transfer {ι W : Type*} [Fintype ι]
    (processed : ι → ℕ) (hp : ∀ i, (processed i).Prime) (N : ι → ℕ)
    (p : ℕ) [Fact p.Prime] (paired : Prop) (n stage : ℕ) (hn : 2 < n + 1) :
    let c : ℚ_[p] := SignedConstant.constant processed N (n + 1)
    ∀ (q : Fin n → ℚ_[p]) (x B v : Bool → ℚ_[p]) (kv : Bool → ℕ),
    (∀ b, Active paired b → x b ≠ 0) → (∀ b, Active paired b → x b ∈ PadicInt.subring p) →
    ∀ (ws : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ),
    LocalStageSelection.ClearedAtPrime p stage c (fixedRemainder paired x B v (n + 1)) ws H →
    ConditionsAtPrime p paired n stage c
      (fun j => (localTarget paired x B v (n + 1) c).coeff (j.val + 1)) q x B v kv ws H a →
    ∀ (s : ℕ), s ≤ stage → ∀ w ∈ ws, 0 < a w → H w ≠ 0 →
    ∃ U V : padicScaledPolynomialRing p s,
      (RatFunc.C (p : ℚ_[p]) ^ (2 * s) * vanishing paired x) ^ a w =
        RatFunc.C (p : ℚ_[p]) ^ stage * ((U : RatFunc ℚ_[p]) + (V : RatFunc ℚ_[p]) *
          ((ShiftedEisenstein.monicFamily n c q : RatFunc ℚ_[p]) ^ a w / (H w : RatFunc ℚ_[p]))) := by
  classical
  dsimp only
  intro q x B v kv hx hxO ws H a hclear hcond s hs w hw ha hH
  by_cases hpair : paired
  · simp only [fixedRemainder, ite_eq_left hpair] at hclear
    simp only [localTarget, ite_eq_left hpair] at hcond
    simp only [vanishing, ite_eq_left hpair]
    exact signed_word_transfer_in_padic_scaled_ring processed hp N p n stage hn q x B v kv
      (fun b => hx b (Or.inr hpair)) (fun b => hxO b (Or.inr hpair)) ws H a hclear
      ⟨fun b => hcond.1 b (Or.inr hpair), fun z hz b => hcond.2.1 z hz b (Or.inr hpair),
        hcond.2.2⟩ s hs w hw ha hH
  · simp only [fixedRemainder, ite_eq_right hpair] at hclear
    simp only [localTarget, ite_eq_right hpair] at hcond
    simp only [vanishing, ite_eq_right hpair]
    have hc : (SignedConstant.constant processed N (n + 1) : ℚ_[p]) ≠ 0 :=
      Rat.cast_ne_zero.mpr (SignedConstant.constant_ne_zero processed hp N (n + 1))
    have hHeval : (H w).eval₂ RatFunc.C RatFunc.X ≠ (0 : RatFunc ℚ_[p]) := by
      rw [eval₂_C_X_eq_coe]
      exact RatFunc.algebraMap_ne_zero hH
    have h := SingleLocalStageSelection.word_transfer_of_local_conditions p RatFunc.C RatFunc.X
      n stage (by omega) _ hc (SignedConstant.constant_inv_mem_padicInt processed N (n + 1) p)
      q (x true) (B true) (v true) (kv true) (hx true (Or.inl rfl)) (hxO true (Or.inl rfl))
      ws H a hclear ⟨hcond.1 true (Or.inl rfl), fun z hz => hcond.2.1 z hz true (Or.inl rfl),
        hcond.2.2⟩ s hs w hw ha hHeval
    simpa only [eval₂_C_X_eq_coe] using h

end UnconditionalCounterexample.MixedWordTransfer
