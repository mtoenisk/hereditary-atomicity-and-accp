import UnconditionalCounterexample.Variations.DimensionGuardLattice
import UnconditionalCounterexample.Variations.GuardGoodPrimes
import UnconditionalCounterexample.Variations.DimensionTensorConductor

/-!
# Full tensor inclusion at a good prime of the selected multivariate table

The ordinary Witt-vector guard is accompanied by at most one rational
p-adic value. A coordinate denominator prime to the local prime and the
point-kernel inclusion suffice for both component shapes.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection.ScreenedGuard

open GuardSupport Variations LocalAlgebra.TransportedIntegralImage RadicalConductor
open scoped TensorProduct

variable {r : ℕ} {p : PrimeIndex} (G : ScreenedGuard r p) {τ : Type*}
  {B A : Type*} [CommRing B] [Algebra ℚ B] [CommRing A] [Algebra ℚ_[p.val] A]
  (e : ℚ_[p.val] ⊗[ℚ] B ≃ₐ[ℚ_[p.val]] A)
  (T D : Subring B) (v : ∀ i : Option τ, A →ₐ[ℚ_[p.val]] G.Field i)

theorem good_tensor_inclusion [Subsingleton τ] (b : B) (n : ℕ) (hb : (n : B)*b ∈ T) (hp : ¬p.val ∣ n)
    (x : τ → Fin (r+1) → ℚ_[p.val]) (hx : ∀ t, ‖x t 0‖ ≤ 1)
    (hcoord : ∀ i, v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] b)) = G.points x i 0)
    (hint : ∀ i (d : D), ‖v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (d : B)))‖ ≤ 1)
    (hk : (⨅ i, RingHom.ker (v i).toRingHom) ≤ conductorIdeal (image p.val B A e T)) :
    image p.val B A e D ≤ image p.val B A e T := by
  classical
  let k := GaloisField p.val G.degree
  let g : A →ₐ[ℚ_[p.val]] GuardUnramified.LocalField p.val k := v none
  have hgi : g (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] b)) = algebraMap _ _ (G.w 0) := hcoord none
  have hg : Algebra.adjoin ℤ_[p.val] ({G.w 0} : Set (WittVector p.val k)) = ⊤ := G.generates
  intro z hz
  have hnorm (i) := norm_value_le_one_tensorImage p.val B A e D (v i) (hint i) z hz
  by_cases hτ : Nonempty τ
  · obtain ⟨t⟩ := hτ
    let s : A →ₐ[ℚ_[p.val]] ℚ_[p.val] := v (some t)
    exact GuardUnramified.paired_tensor_mem p.val k B A e T g b n hb hp (G.w 0) hg hgi G.outside s
      (⟨x t 0, hx t⟩ : ℤ_[p.val]) (hcoord (some t)) ((le_iInf (fun i ↦ by
        cases i with
        | none => exact inf_le_left
        | some t' => rw [Subsingleton.elim t' t]; exact inf_le_right)).trans hk) z (hnorm none) (hnorm (some t))
  · exact GuardUnramified.single_tensor_mem p.val k B A e T g b n hb hp (G.w 0) hg hgi
      ((le_iInf (fun i ↦ by
        cases i with
        | none => exact le_rfl
        | some t => exact (hτ ⟨t⟩).elim)).trans hk) z (hnorm none)

/-- At a prime dividing the coordinate denominator, the lattice in the same
typed product of fields still gives a uniform power conductor. -/
theorem exceptional_tensor_power [Finite τ]
    [Algebra ℤ_[p.val] A] [IsScalarTower ℤ_[p.val] ℚ_[p.val] A]
    (hs : Function.Surjective (AlgHom.pi v)) (hclear : ∀ b : B, ∃ n : ℕ, 0 < n ∧ (n : B)*b ∈ T)
    (hint : ∀ i (d : D), ‖v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (d : B)))‖ ≤ 1)
    (hk : (⨅ i, RingHom.ker (v i).toRingHom) ≤ conductorIdeal (image p.val B A e T)) :
    ∃ k : ℕ, ∀ z ∈ image p.val B A e D, (p.val : A)^k * z ∈ image p.val B A e T := by
  classical
  let := Fintype.ofFinite (Option τ)
  apply exists_power_tensorImage_le e T D (AlgHom.pi v) hs G.integerProductMap _ _ hclear
  · intro z hz
    exact (G.exists_integerProductMap_iff _).mpr (fun i ↦
      norm_value_le_one_tensorImage p.val B A e D (v i) (hint i) z hz)
  · intro z hz
    apply hk
    apply Ideal.mem_iInf.mpr
    intro i
    exact congrFun (RingHom.mem_ker.mp hz) i

end UnconditionalCounterexample.MultivariateSelection.ScreenedGuard
