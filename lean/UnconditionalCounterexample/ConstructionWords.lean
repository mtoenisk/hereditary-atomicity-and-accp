import UnconditionalCounterexample.FiniteStageSelection
import UnconditionalCounterexample.GeometricReservations
import UnconditionalCounterexample.RawWords

/-!
# Choosing the numerator for the literal word list of a prefix

At zero-based stage n, first choose the normalization power, the denominator
of every signed word, and the degree. The subsequent prime assignments and
local return targets can depend on those choices. The polynomial selected for
those targets preserves precisely the points reserved by that prefix and
passes the geometric tests for every one of the listed words.
-/

namespace UnconditionalCounterexample.ConstructionWords

open Polynomial RawWords GeometricReservations

abbrev Word (n : ℕ) := StageWord n (n + 1)

/-- Denominators and the degree are decided before the primes and coefficients. -/
structure DegreePlan (n : ℕ) (P : ℕ → ℚ[X]) (oldE : ℕ → ℕ) where
  E : ℕ
  powers : Word n → Fin n → ℕ
  degree : ℕ
  E_pos : 0 < E
  powers_pos : ∀ w j, 0 < powers w j
  large_degree : 5 ≤ degree
  increasing : ∀ j < n, (P j).natDegree < degree
  infinity : ∀ w, (∏ j : Fin n, (P j.val) ^ powers w j).natDegree < w.latestExponent * degree
  expand : ∀ F : ℚ[X], ∀ w : Word n,
    let φ := algebraMap ℚ[X] (RatFunc ℚ)
    (φ F / φ (∏ j : Fin n, P j.val ^ E)) ^ w.latestExponent *
        (∏ j ∈ Finset.range n,
          normalizedFactor (fun k => φ (P k)) oldE j ^ w.oldExponent j) =
      φ (F ^ w.latestExponent) / φ (∏ j : Fin n, P j.val ^ powers w j)

theorem degreePlan_nonempty (n : ℕ) (P : ℕ → ℚ[X]) (oldE : ℕ → ℕ)
    (hmonic : ∀ j < n, (P j).Monic) : Nonempty (DegreePlan n P oldE) := by
  let φ := algebraMap ℚ[X] (RatFunc ℚ)
  have hP (j : ℕ) (hj : j < n) : φ (P j) ≠ 0 := by
    exact (map_ne_zero_iff φ (RatFunc.algebraMap_injective ℚ)).mpr (hmonic j hj).ne_zero
  obtain ⟨E, e, d, hE, he, _, _, h5, hinc, hdeg, hword⟩ :=
    choose_construction_stage φ n 0 P oldE hP
  refine ⟨⟨E, fun w j => e w j.val, d, hE, fun w j => he w _ j.isLt, h5, hinc, ?_, ?_⟩⟩
  · intro w
    rw [Fin.prod_univ_eq_prod_range (fun j => P j ^ e w j) n]
    exact hdeg w
  · intro F w
    dsimp only
    rw [Fin.prod_univ_eq_prod_range (fun j => P j ^ E) n,
      Fin.prod_univ_eq_prod_range (fun j => P j ^ e w j) n]
    exact hword F w

variable {n : ℕ} {P : ℕ → ℚ[X]} {oldE : ℕ → ℕ}

noncomputable def DegreePlan.wordDen (plan : DegreePlan n P oldE) (w : Word n) : ℚ[X] :=
  ∏ j : Fin n, P j.val ^ plan.powers w j

noncomputable def DegreePlan.rawDen (plan : DegreePlan n P oldE) : ℚ[X] :=
  ∏ j : Fin n, P j.val ^ plan.E

noncomputable def DegreePlan.tests (plan : DegreePlan n P oldE) :=
  finiteTests (reservedPoints geometricEnumeration P n) StageWord.latestExponent
    (fun w => (plan.wordDen w).map (algebraMap ℚ (AlgebraicClosure ℚ)))

theorem DegreePlan.tests_valid (plan : DegreePlan n P oldE) :
    ∀ test ∈ plan.tests, test.Valid :=
  finiteTests_valid_old_products geometricEnumeration P n StageWord.latestExponent plan.powers
    fun w => w.latestExponent_bounds.1

theorem old_product_eval_ne_zero_of_transcendental {K : Type*} [Field K] [Algebra ℚ K]
    (n : ℕ) (P : ℕ → ℚ[X]) (hP : ∀ j < n, (P j).Monic) (e : Fin n → ℕ)
    (x : K) (hx : Transcendental ℚ x) :
    ((∏ j : Fin n, P j.val ^ e j).map (algebraMap ℚ K)).eval x ≠ 0 := by
  rw [eval_map]
  apply old_product_eval_ne_zero P n x _ e
  intro j hj hz
  exact (hP j hj).ne_zero ((transcendental_iff.mp hx) (P j) hz)

section Selection

open LocalStageSelection ShiftedEisenstein
variable {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (ell : ℕ) [Fact ell.Prime] (plan : DegreePlan n P oldE)
    (x v : ∀ j, Bool → ℚ_[p j]) (precision : ι → Bool → ℕ)

noncomputable def DegreePlan.denValue (j : ι) (b : Bool) : ℚ_[p j] :=
  plan.rawDen.eval₂ (algebraMap ℚ ℚ_[p j]) (x j b)

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
      let J := LocalInterpolation.fixedRemainder (x j false) (x j true)
        (B false * v j false) (B true * v j true) (r+1)
      let q0 := fun l : Fin r => (LocalInterpolation.localTarget (x j false) (x j true)
        (B false * v j false) (B true * v j true) (r+1) c).coeff (l.val+1)
      ClearedAtPrime (p j) (n+1) c J Finset.univ H ∧
        ConditionsAtPrime (p j) r (n+1) c q0 (fun l => (coeff l : ℚ_[p j]))
          (x j) B (v j) (precision j) Finset.univ H StageWord.latestExponent) ∧
    (∀ test ∈ plan.tests, test.Holds (F.map (algebraMap ℚ (AlgebraicClosure ℚ)))) ∧
    ∃ model : ℤ_[ell][X], model.Monic ∧
      model.map (algebraMap ℤ_[ell] ℚ_[ell]) = F.map (algebraMap ℚ ℚ_[ell]) ∧
      model.map (PadicInt.toZModPow 1) = (X - C 1) ^ (r+1) ∧
      PadicInt.toZModPow 2 (model.eval 1) = (ell : ZMod (ell ^ 2))

theorem choice_nonempty (hinj : Function.Injective p) (hfresh : ∀ i, p i ≠ ell)
    (hP : ∀ j < n, (P j).Monic) (htrans : ∀ j b, Transcendental ℚ (x j b))
    (hsep : ∀ j, x j false ≠ x j true) (hv : ∀ j b, v j b ≠ 0) :
    Nonempty (Choice p ell plan x v precision) := by
  classical
  let r := plan.degree - 1
  have hd : r+1 = plan.degree := by dsimp [r]; have := plan.large_degree; omega
  have hr : 2 ≤ r := by have := plan.large_degree; omega
  have hx (j : ι) (b : Bool) : x j b ≠ 0 := by
    intro h
    exact X_ne_zero ((transcendental_iff.mp (htrans j b)) X (by simp [h]))
  have hB (j : ι) (b : Bool) : plan.denValue p x j b ≠ 0 := by
    rw [DegreePlan.denValue, ← eval_map]
    exact old_product_eval_ne_zero_of_transcendental n P hP _ _ (htrans j b)
  let H (j : ι) (w : Word n) := (plan.wordDen w).map (algebraMap ℚ ℚ_[p j])
  have hH (j : ι) (w : Word n) (_ : w ∈ (Finset.univ : Finset (Word n))) (b : Bool) :
      (H j w).eval (x j b) ≠ 0 :=
    old_product_eval_ne_zero_of_transcendental n P hP _ _ (htrans j b)
  obtain ⟨_, N, coeff, hmult, _, _, hmonic, hdeg, hzero, hirr, hsupp, hlocal, hgeom, hmodel⟩ :=
    FiniteStageSelection.exists_stage_polynomial p hinj ell hfresh r (n+1) hr (by omega)
      x (plan.denValue p x) v precision hx hsep hB hv Finset.univ H StageWord.latestExponent
      (fun w _ => Nat.ne_of_gt w.latestExponent_bounds.1) hH plan.tests plan.tests_valid
  exact ⟨⟨N, coeff, hmult, hmonic, hdeg.trans hd, hzero, hirr, hsupp, hlocal, hgeom, hmodel⟩⟩

end Selection

end UnconditionalCounterexample.ConstructionWords
