import UnconditionalCounterexample.Variations.PrivateGuardsPair
import UnconditionalCounterexample.Variations.DimensionLocalStage

/-!
# Later main stages at the private pairs

The two actual tuples have different first-coordinate residues, so their
local point ideals are distinct. At any subsequent main stage prescribe
both normalized values to arbitrary precision, simultaneously with the
coefficient and word-gradient conditions used for the local conductor.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial Filter GuardSupport
open scoped Topology

variable {r : ℕ} {p : PrimeIndex} {G : MvPolynomial (Fin (r+1)) ℚ}
  {tests : Finset (MvPolynomial (Fin (r+1)) ℚ)} (s : Pair p G tests)

def Pair.point (i : Bool) (j : Fin (r+1)) : ℚ_[p.val] :=
  if i then (s.ordinarily j).val else (s.privately j).val

theorem Pair.point_independent (i : Bool) : AlgebraicIndependent ℚ (s.point i) := by
  cases i
  · exact s.private_independent
  · exact s.ordinary_independent

theorem Pair.kernels_injective :
    Function.Injective (fun i => RingHom.ker (aeval (R := ℚ_[p.val]) (s.point i)).toRingHom) := by
  have hne : RingHom.ker (aeval (R := ℚ_[p.val]) (s.point false)).toRingHom ≠
      RingHom.ker (aeval (R := ℚ_[p.val]) (s.point true)).toRingHom := by
    intro he
    let f : MvPolynomial (Fin (r+1)) ℚ_[p.val] := X 0 - C (s.point false 0)
    have h : f ∈ RingHom.ker (aeval (R := ℚ_[p.val]) (s.point false)).toRingHom := by
      simp [RingHom.mem_ker, f]
    rw [he] at h
    have eq : s.point true 0 = s.point false 0 := by simpa [RingHom.mem_ker, f, sub_eq_zero] using h
    exact s.distinct (congrArg PadicInt.toZMod (Subtype.ext eq.symm))
  intro i j hij
  cases i <;> cases j <;> first | rfl | exact (hne hij).elim | exact (hne hij.symm).elim

/-- The coefficient neighbourhood enforces the prescribed normalized unit
return at both actual tuples. The same neighbourhood enforces every local
coefficient and derivative estimate, with arbitrarily large scaling exponent. -/
theorem Pair.main_neighborhood {κ η : Type*} [Finite κ] [Finite η]
    (V : MvPolynomial (Fin (r+1)) ℚ_[p.val]) (hV : ∀ i, aeval (s.point i) V = 0) :
    ∃ b : ℕ, ∀ d > b, ∀ (leading : MvPolynomial (Fin (r+1)) ℚ_[p.val])
      (D : MvPolynomial (Fin (r+1)) ℚ), D ≠ 0 → ∀ (v : Bool → ℚ_[p.val]), (∀ i, ‖v i‖ = 1) →
      ∀ (H : κ → MvPolynomial (Fin (r+1)) ℚ_[p.val]) (a : κ → ℕ), (∀ j, 0 < a j) →
      (∀ i j, aeval (s.point i) (H j) ≠ 0) →
      ∀ (coeffTest : η → MvPolynomial (Fin (r+1)) ℚ_[p.val] →ₗ[ℚ_[p.val]] ℚ_[p.val])
      (ε : ℝ), 0 < ε → ∀ N₀ : ℕ,
      ∃ N ≥ N₀, ∃ T : MvPolynomial (Fin (r+1)) ℚ_[p.val], T.totalDegree < d ∧
        ∃ U ∈ 𝓝 (fun m => T.coeff m), ∀ q : MvPolynomial (Fin (r+1)) ℚ_[p.val],
          q.totalDegree < d → (fun m => q.coeff m) ∈ U →
          (∀ i, let normalized := aeval (s.point i) (leading + q) / aeval (s.point i) D
                ‖normalized‖ = 1 ∧ ‖normalized - v i‖ < ε) ∧
          (∀ l, ‖(p.val : ℚ_[p.val]) ^ N * coeffTest l (leading + q) - coeffTest l V‖ < ε) ∧
          ∀ i j, ∃ α : ℚ_[p.val], α ≠ 0 ∧ ‖α⁻¹‖ < ε ∧
            ‖α⁻¹ • residueWordGradient (s.point i) (leading + q) (H j) (a j) -
              (fun l => aeval (s.point i) (pderiv l V))‖ < ε := by
  classical
  obtain ⟨b,hb⟩ := exists_local_stage_neighborhood (κ := κ) (η := η) (E := fun _ => ℚ_[p.val])
    s.point (fun _ => Subsingleton.elim ..) s.kernels_injective V hV (p.val : ℚ_[p.val])
    (Nat.cast_ne_zero.mpr p.property.ne_zero) Padic.norm_p_lt_one
  refine ⟨b,?_⟩
  intro d hd leading D hD v hv H a ha hH coeffTest ε hε N₀
  let B (i : Bool) := aeval (s.point i) D
  have hB (i : Bool) : B i ≠ 0 :=
    fun h => hD ((s.point_independent i) (h.trans (map_zero _).symm))
  let S (i : Bool) := (fun z : ℚ_[p.val] => z / B i) ⁻¹' Metric.ball (v i) (min ε 1)
  have hS (i : Bool) : S i ∈ 𝓝 (v i * B i) := by
    apply (Metric.isOpen_ball.preimage (continuous_id.div_const _)).mem_nhds
    change v i * B i / B i ∈ Metric.ball (v i) (min ε 1)
    rw [mul_div_cancel_right₀ _ (hB i)]
    exact Metric.mem_ball_self (lt_min hε zero_lt_one)
  obtain ⟨N,hN,T,hT,U,hU,h⟩ := hb d hd leading (fun i => v i * B i)
    (fun i => mul_ne_zero (norm_ne_zero_iff.mp ((hv i).symm ▸ one_ne_zero)) (hB i))
    S hS H a ha hH coeffTest ε hε N₀
  refine ⟨N,hN,T,hT,U,hU,?_⟩
  intro q hq hUq
  obtain ⟨hval,hcoeff,hgrad⟩ := h q hq hUq
  refine ⟨fun i => ?_,hcoeff,hgrad⟩
  have hclose : ‖aeval (s.point i) (leading + q) / B i - v i‖ < min ε 1 := by
    simpa only [S,Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hval i
  exact ⟨(Padic.norm_eq_of_norm_sub_lt_right (by rw [hv]; exact hclose.trans_le (min_le_right ..))).trans
    (hv i), hclose.trans_le (min_le_left ..)⟩

end UnconditionalCounterexample.Variations.PrivateGuards
