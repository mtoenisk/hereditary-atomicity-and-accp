import UnconditionalCounterexample.FiniteStageSelection
import UnconditionalCounterexample.SingleLocalInterpolation

/-!
# One polynomial for mixed single-guard and paired primes

At each ordinary prime the guard branch is always present, while the primary
branch is constrained exactly when that prime is selected. The corresponding
actual one- or two-point target yields coefficient neighborhoods for one shared
signed constant. One rational shifted-Eisenstein polynomial then satisfies all
local arithmetic conditions and all valid geometric tests simultaneously.
-/

noncomputable section
namespace UnconditionalCounterexample.MixedStageSelection

open Polynomial LocalStageSelection ShiftedEisenstein SeparationExclusions

/-- The guard is always active; a primary branch is present exactly at a selected prime. -/
def Active (paired : Prop) (b : Bool) : Prop := b = true ∨ paired

private def branches (paired : Prop) : Finset Bool := by
  classical
  exact if paired then Finset.univ else {true}

@[simp] private theorem mem_branches (paired : Prop) (b : Bool) :
    b ∈ branches paired ↔ Active paired b := by
  classical
  simp only [branches, Active]
  split_ifs <;> simp_all

/-- The fixed remainder is chosen at the actual number of branches. -/
def fixedRemainder {K : Type*} [Field K] (paired : Prop)
    (x B v : Bool → K) (d : ℕ) : K[X] := by
  classical
  exact if paired then LocalInterpolation.fixedRemainder (x false) (x true)
    (B false * v false) (B true * v true) d
  else SingleLocalInterpolation.fixedRemainder (x true) (B true * v true) d

/-- One local monic target, with no primary interpolation outside the selected set. -/
def localTarget {K : Type*} [Field K] (paired : Prop)
    (x B v : Bool → K) (d : ℕ) (c : K) : K[X] := by
  classical
  exact if paired then LocalInterpolation.localTarget (x false) (x true)
    (B false * v false) (B true * v true) d c
  else SingleLocalInterpolation.localTarget (x true) (B true * v true) d c

theorem localTarget_monic_degree {K : Type*} [Field K] (paired : Prop)
    (x B v : Bool → K) (d : ℕ) (c : K) (hd : 2 < d) :
    (localTarget paired x B v d c).IsMonicOfDegree d := by
  classical
  by_cases hp : paired
  · simpa only [localTarget, ite_eq_left hp] using
      LocalInterpolation.localTarget_monic_degree (x false) (x true)
        (B false * v false) (B true * v true) d c hd
  · simpa only [localTarget, ite_eq_right hp] using
      SingleLocalInterpolation.localTarget_monic_degree (x true) (B true * v true) d c (by omega)

theorem localTarget_eval_zero {K : Type*} [Field K] (paired : Prop)
    (x B v : Bool → K) (d : ℕ) (c : K) (hd : d ≠ 0)
    (hx : ∀ b, Active paired b → x b ≠ 0) :
    (localTarget paired x B v d c).eval 0 = c := by
  classical
  by_cases hp : paired
  · simpa only [localTarget, ite_eq_left hp] using
      LocalInterpolation.localTarget_eval_zero (x false) (x true)
        (B false * v false) (B true * v true) d c
        (hx false (Or.inr hp)) (hx true (Or.inl rfl)) hd
  · simpa only [localTarget, ite_eq_right hp] using
      SingleLocalInterpolation.localTarget_eval_zero (x true) (B true * v true) d c hd

theorem localTarget_eval {K : Type*} [Field K] (paired : Prop)
    (x B v : Bool → K) (d : ℕ) (c : K)
    (hx : ∀ b, Active paired b → x b ≠ 0)
    (hsep : paired → x false ≠ x true) (b : Bool) (hb : Active paired b) :
    (localTarget paired x B v d c).eval (x b) = B b * v b := by
  classical
  by_cases hp : paired
  · simp only [localTarget, ite_eq_left hp]
    cases b with
    | false => exact LocalInterpolation.localTarget_eval_left _ _ _ _ _ _
    | true => exact LocalInterpolation.localTarget_eval_right _ _ _ _ _ _ (hsep hp)
  · have hbtrue : b = true := hb.resolve_right hp
    subst b
    simpa only [localTarget, ite_eq_right hp] using
      SingleLocalInterpolation.localTarget_eval (x true) (B true * v true) d c (hx true (Or.inl rfl))

theorem localTarget_eq_monicFamily {K : Type*} [Field K] (paired : Prop)
    (x B v : Bool → K) (n : ℕ) (c : K) (hn : 2 < n + 1)
    (hx : ∀ b, Active paired b → x b ≠ 0) :
    monicFamily n c (fun j => (localTarget paired x B v (n + 1) c).coeff (j.val + 1)) =
      localTarget paired x B v (n + 1) c := by
  have hT := localTarget_monic_degree paired x B v (n + 1) c hn
  apply monicFamily_eq _ _ _ _ hT.monic hT.natDegree_eq
  · rw [coeff_zero_eq_eval_zero]
    exact localTarget_eval_zero paired x B v (n + 1) c (by omega) hx
  · intro j
    rfl

/-- The common conditions quantify only over actual branches and preserve all
scheduled word derivatives and every scaled coefficient. -/
def ConditionsAtPrime {W : Type*} (p : ℕ) [Fact p.Prime] (paired : Prop)
    (n stage : ℕ) (c : ℚ_[p]) (q0 q : Fin n → ℚ_[p])
    (x B v : Bool → ℚ_[p]) (kv : Bool → ℕ)
    (t : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ) : Prop :=
  (∀ b : Bool, Active paired b →
    (monicFamily n c q).eval (x b) ≠ 0 ∧
    ‖(monicFamily n c q).eval (x b) / B b‖ = ‖v b‖ ∧
    (v b / ((monicFamily n c q).eval (x b) / B b) - 1) /
      (p : ℚ_[p]) ^ kv b ∈ PadicInt.subring p) ∧
  (∀ w ∈ t, ∀ b : Bool, Active paired b →
    (LocalInterpolation.wordDerivative (monicFamily n c q)
      (H w) (a w) (x b)).valuation < -(stage : ℤ)) ∧
  (∀ s : ℕ, s ≤ stage → ∀ j : ℕ,
    (C c⁻¹ * (monicFamily n c q - monicFamily n c q0).comp
      (C (((p : ℚ_[p]) ^ s)⁻¹) * X)).coeff j /
        (p : ℚ_[p]) ^ stage ∈ PadicInt.subring p)

theorem exists_local_target_tolerance {W : Type*}
    (p : ℕ) [Fact p.Prime] (paired : Prop) (n stage : ℕ) (hn : 2 < n + 1) (c : ℚ_[p])
    (x B v : Bool → ℚ_[p]) (kv : Bool → ℕ)
    (hx : ∀ b, Active paired b → x b ≠ 0) (hsep : paired → x false ≠ x true)
    (hB : ∀ b, Active paired b → B b ≠ 0) (hv : ∀ b, Active paired b → v b ≠ 0)
    (t : Finset W) (H : W → ℚ_[p][X]) (a : W → ℕ)
    (hword : ∀ w ∈ t, ∀ b, Active paired b →
      (p : ℝ) ^ stage < ‖LocalInterpolation.wordDerivative
        (localTarget paired x B v (n + 1) c) (H w) (a w) (x b)‖) :
    let q0 : Fin n → ℚ_[p] := fun j =>
      (localTarget paired x B v (n + 1) c).coeff (j.val + 1)
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : Fin n → ℚ_[p], (∀ j, ‖q j - q0 j‖ < δ) →
      ConditionsAtPrime p paired n stage c q0 q x B v kv t H a := by
  classical
  dsimp only
  let T := localTarget paired x B v (n + 1) c
  let q0 : Fin n → ℚ_[p] := fun j => T.coeff (j.val + 1)
  have hT : monicFamily n c q0 = T := localTarget_eq_monicFamily paired x B v n c hn hx
  have htarget (b : Bool) (hb : b ∈ branches paired) :
      (monicFamily n c q0).eval (x b) = B b * v b := by
    rw [hT]
    exact localTarget_eval paired x B v (n + 1) c hx hsep b ((mem_branches _ _).mp hb)
  obtain ⟨δ, hδ, hstable⟩ := CoefficientStability.exists_padic_stage_tolerance_full
    n c q0 (branches paired) x B v kv (fun b hb => hB b ((mem_branches _ _).mp hb))
    (fun b hb => hv b ((mem_branches _ _).mp hb)) htarget
    (t.product (branches paired)) (fun wb => x wb.2) (fun wb => H wb.1)
    (fun wb => a wb.1) (fun _ => (p : ℝ) ^ stage)
    (fun wb hwb => by
      rw [hT]
      exact hword wb.1 (Finset.mem_product.mp hwb).1
        wb.2 ((mem_branches _ _).mp (Finset.mem_product.mp hwb).2))
    (Finset.range (stage + 1)) (fun _ => c⁻¹) (fun s => ((p : ℚ_[p]) ^ s)⁻¹)
    (fun _ => stage)
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  obtain ⟨hval, hwords, hcoeff⟩ := hstable q hq
  refine ⟨fun b hb => hval b ((mem_branches _ _).mpr hb), ?_, ?_⟩
  · intro w hw b hb
    exact SignedConstant.valuation_lt_neg_of_pow_lt_norm p _ stage
      (hwords (w, b) (Finset.mem_product.mpr ⟨hw, (mem_branches _ _).mpr hb⟩))
  · intro s hs j
    exact hcoeff s (Finset.mem_range.mpr (by omega)) j

/-- Both local models have nonzero affine derivative slope at every actual
branch, so one bound on the constant works for the whole finite word list. -/
theorem exists_bound_word_derivatives {W K : Type*} [NormedField K] [CharZero K]
    (paired : Prop) (t : Finset W) (x B v : Bool → K) (d : ℕ)
    (hx : ∀ b, Active paired b → x b ≠ 0) (hsep : paired → x false ≠ x true)
    (hB : ∀ b, Active paired b → B b ≠ 0) (hv : ∀ b, Active paired b → v b ≠ 0)
    (H : W → K[X]) (a : W → ℕ) (r : W → ℝ)
    (ha : ∀ w ∈ t, a w ≠ 0)
    (hH : ∀ w ∈ t, ∀ b, Active paired b → (H w).eval (x b) ≠ 0) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ c : K, R < ‖c‖ → ∀ w ∈ t, ∀ b, Active paired b →
      r w < ‖LocalInterpolation.wordDerivative (localTarget paired x B v d c) (H w) (a w) (x b)‖ := by
  classical
  by_cases hp : paired
  · obtain ⟨R, hR, hlarge⟩ := LocalInterpolation.exists_bound_word_derivatives t
      (x false) (x true) (B false * v false) (B true * v true) d
      (hx false (Or.inr hp)) (hx true (Or.inl rfl)) (hsep hp)
      (mul_ne_zero (hB false (Or.inr hp)) (hv false (Or.inr hp)))
      (mul_ne_zero (hB true (Or.inl rfl)) (hv true (Or.inl rfl)))
      H a r ha (fun w hw => hH w hw false (Or.inr hp))
      (fun w hw => hH w hw true (Or.inl rfl))
    refine ⟨R, hR, ?_⟩
    intro c hc w hw b _
    simp only [localTarget, ite_eq_left hp]
    cases b with
    | false => exact (hlarge c hc w hw).1
    | true => exact (hlarge c hc w hw).2
  · obtain ⟨R, hR, hlarge⟩ := SingleLocalInterpolation.exists_bound_word_derivatives t
      (x true) (B true * v true) d (hx true (Or.inl rfl))
      (mul_ne_zero (hB true (Or.inl rfl)) (hv true (Or.inl rfl))) H a r ha
      (fun w hw => hH w hw true (Or.inl rfl))
    refine ⟨R, hR, ?_⟩
    intro c hc w hw b hb
    have hbtrue : b = true := hb.resolve_right hp
    subst b
    simpa only [localTarget, ite_eq_right hp] using hlarge c hc w hw


/-- Clearing exponents and one signed rational constant are chosen for all
ordinary primes together, whether their local model has one branch or two. -/
theorem exists_prepared_local_data {ι W : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (paired : ι → Prop) (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (n stage : ℕ) (hn : 2 < n + 1) (hstage : 1 ≤ stage)
    (x B v : ∀ i, Bool → ℚ_[p i]) (kv : ι → Bool → ℕ)
    (hx : ∀ i b, Active (paired i) b → x i b ≠ 0)
    (hsep : ∀ i, paired i → x i false ≠ x i true)
    (hB : ∀ i b, Active (paired i) b → B i b ≠ 0)
    (hv : ∀ i b, Active (paired i) b → v i b ≠ 0)
    (t : Finset W) (H : ∀ i, W → ℚ_[p i][X]) (a : W → ℕ)
    (ha : ∀ w ∈ t, a w ≠ 0)
    (hH : ∀ i w, w ∈ t → ∀ b, Active (paired i) b → (H i w).eval (x i b) ≠ 0) :
    ∃ h N : ι → ℕ, ∃ δ : ι → ℝ,
      (∀ i, ∃ e : ℕ, 0 < e ∧ N i = (ell - 1) * e) ∧
      (∀ i, 0 < N i) ∧ (∀ i, h i + stage ≤ N i) ∧
      (∀ i, 0 < δ i ∧
        ClearedAtPrime (p i) stage (SignedConstant.constant p N (n + 1))
          (fixedRemainder (paired i) (x i) (B i) (v i) (n + 1)) t (H i) ∧
        let q0 : Fin n → ℚ_[p i] := fun j =>
          (localTarget (paired i) (x i) (B i) (v i) (n + 1)
            (SignedConstant.constant p N (n + 1))).coeff (j.val + 1)
        ∀ q : Fin n → ℚ_[p i], (∀ j, ‖q j - q0 j‖ < δ i) →
          ConditionsAtPrime (p i) (paired i) n stage (SignedConstant.constant p N (n + 1))
            q0 q (x i) (B i) (v i) (kv i) t (H i) a) ∧
      ∃ c : ℤ_[ell], (c : ℚ_[ell]) = (SignedConstant.constant p N (n + 1) : ℚ_[ell]) ∧
        PadicInt.toZModPow 1 c = (-1) ^ (n + 1) := by
  classical
  let J (i : ι) := fixedRemainder (paired i) (x i) (B i) (v i) (n + 1)
  choose h hclear using fun i => exists_clearing_for_scales (p i) stage (J i) t (H i)
  choose R hR hderiv using fun i => exists_bound_word_derivatives
    (paired i) t (x i) (B i) (v i) (n + 1) (hx i) (hsep i) (hB i) (hv i)
    (H i) a (fun _ => (p i : ℝ) ^ stage) ha (hH i)
  obtain ⟨N, hmult, hpos, hbudget, hnorm, hc⟩ := SignedConstant.exists_constant_exponents
    p hinj ell hfresh (n + 1) stage hstage h R
  have hword (i : ι) (w : W) (hw : w ∈ t) (b : Bool) (hb : Active (paired i) b) :
      (p i : ℝ) ^ stage < ‖LocalInterpolation.wordDerivative
        (localTarget (paired i) (x i) (B i) (v i) (n + 1)
          (SignedConstant.constant p N (n + 1))) (H i w) (a w) (x i b)‖ :=
    hderiv i _ (hnorm i) w hw b hb
  choose δ hδ hstable using fun i => exists_local_target_tolerance
    (p i) (paired i) n stage hn (SignedConstant.constant p N (n + 1))
    (x i) (B i) (v i) (kv i) (hx i) (hsep i) (hB i) (hv i) t (H i) a (hword i)
  refine ⟨h, N, δ, hmult, hpos, hbudget, fun i => ⟨hδ i, ?_, hstable i⟩, hc⟩
  intro s hs
  have hp0 : (p i : ℚ_[p i]) ^ stage ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (show (p i).Prime from Fact.out).ne_zero)
  have hintegral (z : ℚ_[p i]) (hz : ‖z‖ ≤ (p i : ℝ) ^ h i) :
      (z / (SignedConstant.constant p N (n + 1) : ℚ_[p i])) /
        (p i : ℚ_[p i]) ^ stage ∈ PadicInt.subring (p i) := by
    apply (PadicTargetStability.div_mem_padicInt_iff _ _ hp0).mpr
    rw [Padic.norm_p_pow]
    exact SignedConstant.norm_div_constant_le_stage_precision p hinj N (n + 1)
      i (h i) stage (hbudget i) z hz
  exact ⟨fun k => hintegral _ ((hclear i s hs).1 k),
    fun w hw k => hintegral _ ((hclear i s hs).2 w hw k)⟩

/-- One single rational shifted-Eisenstein polynomial meets every local model,
all scheduled arithmetic precision and all valid geometric tests at once. -/
theorem exists_stage_polynomial {ι W K : Type*} [Fintype ι] [Field K] [CharZero K]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (paired : ι → Prop) (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (n stage : ℕ) (hn : 2 ≤ n) (hstage : 1 ≤ stage)
    (x B v : ∀ i, Bool → ℚ_[p i]) (kv : ι → Bool → ℕ)
    (hx : ∀ i b, Active (paired i) b → x i b ≠ 0)
    (hsep : ∀ i, paired i → x i false ≠ x i true)
    (hB : ∀ i b, Active (paired i) b → B i b ≠ 0)
    (hv : ∀ i b, Active (paired i) b → v i b ≠ 0)
    (t : Finset W) (H : ∀ i, W → ℚ_[p i][X]) (a : W → ℕ)
    (ha : ∀ w ∈ t, a w ≠ 0)
    (hH : ∀ i w, w ∈ t → ∀ b, Active (paired i) b → (H i w).eval (x i b) ≠ 0)
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
          (fixedRemainder (paired i) (x i) (B i) (v i) (n + 1)) t (H i) ∧
        let q0 : Fin n → ℚ_[p i] := fun j =>
          (localTarget (paired i) (x i) (B i) (v i) (n + 1) C0).coeff (j.val + 1)
        ConditionsAtPrime (p i) (paired i) n stage C0 q0 (fun j => (q j : ℚ_[p i]))
          (x i) (B i) (v i) (kv i) t (H i) a) ∧
      (∀ test ∈ I, test.Holds (F.map (algebraMap ℚ K))) ∧
      ∃ g : ℤ_[ell][X], g.Monic ∧
        g.map (algebraMap ℤ_[ell] ℚ_[ell]) = F.map (algebraMap ℚ ℚ_[ell]) ∧
        g.map (PadicInt.toZModPow 1) = (X - C 1) ^ (n + 1) ∧
        PadicInt.toZModPow 2 (g.eval 1) = (ell : ZMod (ell ^ 2)) := by
  obtain ⟨h, N, δ, hmult, hpos, hbudget, hlocal, c0, hc0, hc⟩ :=
    exists_prepared_local_data p hinj paired ell hfresh n stage (by omega) hstage
      x B v kv hx hsep hB hv t H a ha hH
  let C0 := SignedConstant.constant p N (n + 1)
  let q0 : Fin n → ∀ i, ℚ_[p i] := fun j i =>
    (localTarget (paired i) (x i) (B i) (v i) (n + 1) C0).coeff (j.val + 1)
  obtain ⟨q, hm, hd, hcoeff, hirr, hsupp, happ, hgeom, hmodel⟩ :=
    GeometricStage.exists_irreducible_approximating_family_with_tests
      p hinj n hn C0 (SignedConstant.constant_ne_zero p (fun _ => Fact.out) N (n + 1))
      (SignedConstant.constant_denominator_support p (fun _ => Fact.out) N (n + 1))
      q0 (fun _ i => δ i) (fun _ i => (hlocal i).1) ell hfresh c0 hc0 hc I hI
  refine ⟨h, N, q, hmult, hpos, hbudget, hm, hd, hcoeff, hirr, hsupp, ?_, hgeom, hmodel⟩
  intro i
  exact ⟨(hlocal i).2.1, (hlocal i).2.2 (fun j => (q j : ℚ_[p i])) (fun j => happ j i)⟩

end UnconditionalCounterexample.MixedStageSelection
