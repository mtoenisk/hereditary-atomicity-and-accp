import UnconditionalCounterexample.Variations.DimensionRecoveryGenerators

noncomputable section
namespace UnconditionalCounterexample.Variations.RecoveryGenerators

open MvPolynomial Filter
open scoped Topology

universe uK uσ uι uE

variable {K : Type uK} {σ : Type uσ} {ι : Type uι} [NontriviallyNormedField K] [Fintype σ] [Finite ι]
variable {E : ι → Type uE} [∀ i, NontriviallyNormedField (E i)] [∀ i, NormedAlgebra K (E i)]
  [∀ i, CharZero (E i)] [∀ i, FiniteDimensional K (E i)]
variable {u : ∀ i, σ → E i} (G : RecoveryGenerators (K := K) u)
   (π : K) (hπ : π ≠ 0) (hsmall : ‖π‖ < 1)

def genScale (s : ℕ) := (exists_scaledCoefficient_bound π hsmall s G.gen).choose

omit [Finite ι] [∀ i, CharZero (E i)] [∀ i, FiniteDimensional K (E i)] in
theorem genScale_spec (s : ℕ) (j : Fin G.count) (m : σ →₀ ℕ) :
    ‖scaledCoefficient (π^s) (π^(G.genScale π hsmall s)) m (G.gen j)‖ ≤ 1 :=
  (exists_scaledCoefficient_bound π hsmall s G.gen).choose_spec j m

def denScale (s : ℕ) (H : MvPolynomial σ K) :=
  (exists_scaledCoefficient_bound π hsmall s (fun _ : Unit ↦ H)).choose

theorem denScale_spec (s : ℕ) (H : MvPolynomial σ K) (m : σ →₀ ℕ) :
    ‖scaledCoefficient (π^s) (π^(denScale π hsmall s H)) m H‖ ≤ 1 :=
  (exists_scaledCoefficient_bound π hsmall s (fun _ : Unit ↦ H)).choose_spec () m

variable (hgen : ∀ i, Algebra.adjoin K (Set.range (u i)) = ⊤)
    (hdist : Function.Injective (fun i ↦ RingHom.ker (aeval (R := K) (u i)).toRingHom))

/-- Stage threshold depends only on the frozen points and generators and the stage number. -/
def threshold (n : ℕ) := (exists_local_stage_neighborhood_uniform.{uK,uσ,uι,uE,uσ,uσ} u hgen hdist
  (G.direction π n) (G.direction_vanish π n) π hπ hsmall).choose + 1

/-- Before the actual polynomial is selected, there is one local coefficient neighborhood
covering every scale up to the current stage, every listed word, and all retained points. -/
theorem exists_recovery_stage {κ : Type uσ} [Fintype κ] (n d : ℕ)
    (hd : G.threshold π hπ hsmall hgen hdist n ≤ d)
    (leading : MvPolynomial σ K) (hL : leading.totalDegree ≤ d)
    (y : ∀ i, E i) (hy : ∀ i, y i ≠ 0) (S : ∀ i, Set (E i)) (hS : ∀ i, S i ∈ 𝓝 (y i))
    (H : κ → MvPolynomial σ K) (a : κ → ℕ) (ha : ∀ j, 0 < a j)
    (hH : ∀ i j, aeval (u i) (H j) ≠ 0) :
    ∃ (N : ℕ) (target : MvPolynomial σ K), target.totalDegree < d ∧
      ∃ U ∈ 𝓝 (fun m ↦ target.coeff m), ∀ q : MvPolynomial σ K,
        q.totalDegree < d → (fun m ↦ q.coeff m) ∈ U →
        (∀ i, aeval (u i) (leading + q) ∈ S i) ∧
        (∀ s ≤ n, ∀ w, denScale π hsmall s (H w) + n*n ≤ (G.genScale π hsmall s + N) * a w) ∧
        (∀ s ≤ n, ∀ m, ‖π ^ N * scaledCoefficient (π^s) (π^(G.genScale π hsmall s)) m (leading + q) -
          scaledCoefficient (π^s) (π^(G.genScale π hsmall s)) m (G.direction π n)‖ ≤ ‖π‖^(n*n)) ∧
        ∀ i w, ∃ α : E i, α ≠ 0 ∧ ‖α⁻¹‖ ≤ ‖π‖^(n*n) ∧
          ‖α⁻¹ • residueWordGradient (u i) (leading + q) (H w) (a w) -
          ∑ j : Fin G.count, (algebraMap K (E i) π ^ n)^j.val •
            (fun l ↦ aeval (u i) (pderiv l (G.gen j)))‖ ≤ ‖π‖^(n*n) := by
  classical
  let V := G.direction π n
  let box := monomialBox σ d ∪ V.support
  let b (w : Fin (n+1) × κ) := denScale π hsmall w.1.val (H w.2)
  let t (l : Fin (n+1) × ↥box) :=
    scaledCoefficient (π^l.1.val) (π^(G.genScale π hsmall l.1.val)) l.2.val
  let bmax := Finset.univ.sup b + n*n
  let h := exists_local_stage_neighborhood_uniform.{uK,uσ,uι,uE,uσ,uσ} u hgen hdist V (G.direction_vanish π n) π hπ hsmall
  obtain ⟨N, hN, target, htarget, U, hU, htests⟩ := h.choose_spec d hd leading y hy S hS H a ha hH t
    (‖π‖^(n*n)) (pow_pos (norm_pos_iff.mpr hπ) _) bmax
  refine ⟨N, target, htarget, U, hU, fun q hq hmem ↦ ?_⟩
  obtain ⟨hval, hc, hg⟩ := htests q hq hmem
  refine ⟨hval, fun s hs w ↦ ?_, fun s hs m ↦ ?_, fun i w ↦ ?_⟩
  · let v : Fin (n+1) × κ := (⟨s, by omega⟩,w)
    have h₁ := Finset.le_sup (f := b) (Finset.mem_univ v)
    have h₂ := Nat.le_mul_of_pos_right (G.genScale π hsmall s + N) (ha w)
    change b v + n*n ≤ _
    dsimp [bmax] at hN
    omega
  · by_cases hm : m ∈ box
    · exact (hc (⟨s,by omega⟩,⟨m,hm⟩)).le
    · have hv : m ∉ V.support := fun h ↦ hm (Finset.mem_union_right _ h)
      have hf : m ∉ (leading+q).support := fun h ↦ hm (Finset.mem_union_left _ (support_subset_monomialBox
        (leading+q) ((totalDegree_add ..).trans (max_le hL hq.le)) h))
      have h₁ : scaledCoefficient (π^s) (π^(G.genScale π hsmall s)) m (leading + q) = 0 := by
        change _ * (leading+q).coeff m = 0
        rw [notMem_support_iff.mp hf, mul_zero]
      have h₂ : scaledCoefficient (π^s) (π^(G.genScale π hsmall s)) m (G.direction π n) = 0 := by
        change _ * V.coeff m = 0
        rw [notMem_support_iff.mp hv, mul_zero]
      simp [h₁,h₂]
  · obtain ⟨α,hα,hi,hv⟩ := hg i w
    refine ⟨α,hα,hi.le,?_⟩
    rw [← G.direction_gradient]
    exact hv.le

end UnconditionalCounterexample.Variations.RecoveryGenerators
