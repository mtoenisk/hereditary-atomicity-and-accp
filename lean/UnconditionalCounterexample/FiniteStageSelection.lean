import UnconditionalCounterexample.GeometricStage
import UnconditionalCounterexample.LocalStageSelection

/-!
# One polynomial satisfying all finite-stage requirements

This joins the actual local preparation and geometric rational selection for
Proposition 3.1. The constant, coefficient
vectors, local returns, word derivatives, coefficient precisions, geometric
tests, and auxiliary Eisenstein model refer to one and the same rational
polynomial. Choosing previous denominators, enumerating tests and prime
assignments, and iterating the resulting finite successor are separate steps.
-/

noncomputable section
namespace UnconditionalCounterexample.FiniteStageSelection

open Polynomial ShiftedEisenstein LocalStageSelection SeparationExclusions

/-- One rational polynomial satisfies all prepared local conditions, every valid
geometric test, and both shifted-Eisenstein congruences at the auxiliary prime.
All conclusions refer to the same middle-coefficient vector q. -/
theorem exists_stage_polynomial {ι W K : Type*} [Fintype ι] [Field K] [CharZero K]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (n stage : ℕ) (hn : 2 ≤ n) (hstage : 1 ≤ stage)
    (x B v : ∀ i, Bool → ℚ_[p i]) (kv : ι → Bool → ℕ)
    (hx : ∀ i b, x i b ≠ 0) (hsep : ∀ i, x i false ≠ x i true)
    (hB : ∀ i b, B i b ≠ 0) (hv : ∀ i b, v i b ≠ 0)
    (t : Finset W) (H : ∀ i, W → ℚ_[p i][X]) (a : W → ℕ)
    (ha : ∀ w ∈ t, a w ≠ 0) (hH : ∀ i w, w ∈ t → ∀ b, (H i w).eval (x i b) ≠ 0)
    (I : Finset (Test K)) (hI : ∀ test ∈ I, test.Valid) :
    ∃ h N : ι → ℕ, ∃ q : Fin n → ℚ,
      (∀ i, ∃ e : ℕ, 0 < e ∧ N i = (ell - 1) * e) ∧
      (∀ i, 0 < N i) ∧ (∀ i, h i + stage ≤ N i) ∧
      let C0 := SignedConstant.constant p N (n + 1)
      let F := monicFamily n C0 q
      F.Monic ∧ F.natDegree = n + 1 ∧ F.coeff 0 = C0 ∧ Irreducible F ∧
      (∀ k prime, prime.Prime → prime ∣ (F.coeff k).den → ∃ i, prime = p i) ∧
      (∀ i,
        ClearedAtPrime (p i) stage C0
          (LocalInterpolation.fixedRemainder (x i false) (x i true)
            (B i false * v i false) (B i true * v i true) (n + 1)) t (H i) ∧
        let q0 : Fin n → ℚ_[p i] := fun j =>
          (LocalInterpolation.localTarget (x i false) (x i true)
            (B i false * v i false) (B i true * v i true) (n + 1) C0).coeff (j.val + 1)
        ConditionsAtPrime (p i) n stage C0 q0 (fun j => (q j : ℚ_[p i]))
          (x i) (B i) (v i) (kv i) t (H i) a) ∧
      (∀ test ∈ I, test.Holds (F.map (algebraMap ℚ K))) ∧
      ∃ g : ℤ_[ell][X], g.Monic ∧
        g.map (algebraMap ℤ_[ell] ℚ_[ell]) = F.map (algebraMap ℚ ℚ_[ell]) ∧
        g.map (PadicInt.toZModPow 1) = (X - C 1) ^ (n + 1) ∧
        PadicInt.toZModPow 2 (g.eval 1) = (ell : ZMod (ell ^ 2)) := by
  obtain ⟨h, N, δ, hmult, hpos, hbudget, hlocal, c0, hc0, hc⟩ :=
    exists_prepared_local_data p hinj ell hfresh n stage (by omega) hstage
      x B v kv hx hsep hB hv t H a ha hH
  let C0 := SignedConstant.constant p N (n + 1)
  let q0 : Fin n → ∀ i, ℚ_[p i] := fun j i =>
    (LocalInterpolation.localTarget (x i false) (x i true)
      (B i false * v i false) (B i true * v i true) (n + 1) C0).coeff (j.val + 1)
  obtain ⟨q, hm, hd, hcoeff, hirr, hsupp, happ, hgeom, hmodel⟩ :=
    GeometricStage.exists_irreducible_approximating_family_with_tests
      p hinj n hn C0 (SignedConstant.constant_ne_zero p (fun _ => Fact.out) N (n + 1))
      (SignedConstant.constant_denominator_support p (fun _ => Fact.out) N (n + 1))
      q0 (fun _ i => δ i) (fun _ i => (hlocal i).1) ell hfresh c0 hc0 hc I hI
  refine ⟨h, N, q, hmult, hpos, hbudget, hm, hd, hcoeff, hirr, hsupp, ?_, hgeom, hmodel⟩
  intro i
  exact ⟨(hlocal i).2.1, (hlocal i).2.2 (fun j => (q j : ℚ_[p i])) (fun j => happ j i)⟩

end UnconditionalCounterexample.FiniteStageSelection
