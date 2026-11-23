import UnconditionalCounterexample.Variations.MultiDomainConductorFibres
import UnconditionalCounterexample.Variations.TripleGuardInterpolation
import UnconditionalCounterexample.Variations.PrivateGuardsTriple

/-! # Good-prime conductor at a selected private three-branch fibre -/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection.ScreenedGuard
open GuardSupport Variations LocalAlgebra.TransportedIntegralImage RadicalConductor GuardUnramified
open scoped TensorProduct

variable {r : ℕ} {p : PrimeIndex} (G : ScreenedGuard r p)

def tripleCoordinate (y : Bool → ℤ_[p.val]) : ∀ i : Option Bool, G.Integers i
  | none => G.w 0
  | some t => y t

private theorem eval_at_component (y : Bool → ℤ_[p.val]) (i : Option Bool) (P : Polynomial ℤ_[p.val]) :
    (Polynomial.aeval (G.tripleCoordinate y) P) i = Polynomial.aeval (G.tripleCoordinate y i) P := by
  let e := Pi.evalAlgHom ℤ_[p.val] (fun i : Option Bool => G.Integers i) i
  exact (Polynomial.aeval_algHom_apply e _ _).symm

theorem triple_interpolation (y : Bool → ℤ_[p.val])
    (hne : PadicInt.toZMod (y false) ≠ PadicInt.toZMod (y true)) :
    Function.Surjective (Polynomial.aeval (R := ℤ_[p.val]) (G.tripleCoordinate y)) := by
  intro w
  obtain ⟨P,hg,ha,hb⟩ := guard_two_primary_values p.val (GaloisField p.val G.degree) (G.w 0)
    G.generates G.outside _ _ hne (w none) (w (some false)) (w (some true))
  refine ⟨P,funext fun i => ?_⟩
  rw [G.eval_at_component]
  cases i with
  | none => exact hg
  | some t =>
    cases t
    · exact ha
    · exact hb

variable {B A : Type*} [CommRing B] [Algebra ℚ B] [CommRing A] [Algebra ℚ_[p.val] A]
  (e : ℚ_[p.val] ⊗[ℚ] B ≃ₐ[ℚ_[p.val]] A)
  (T D : Subring B) (v : ∀ i : Option Bool, A →ₐ[ℚ_[p.val]] G.Field i)

/-- At a private prime away from the one coordinate denominator, integral
polynomial interpolation fills all three components of the tensor image. -/
theorem good_triple_tensor_inclusion (b : B) (n : ℕ) (hb : (n : B)*b ∈ T) (hp : ¬p.val ∣ n)
    (y : Bool → ℤ_[p.val]) (hne : PadicInt.toZMod (y false) ≠ PadicInt.toZMod (y true))
    (hcoord : ∀ i, v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] b)) = G.integerMap i (G.tripleCoordinate y i))
    (hint : ∀ i (d : D), ‖v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (d : B)))‖ ≤ 1)
    (hk : (⨅ i, RingHom.ker (v i).toRingHom) ≤ conductorIdeal (image p.val B A e T)) :
    image p.val B A e D ≤ image p.val B A e T := by
  let U := image p.val B A e T
  let t : U := ⟨_,coordinate_mem_of_prime_to p.val B A e T b n hb hp⟩
  let ev := AlgHom.pi v
  let j := G.integerProductMap (τ := Bool)
  let sc := algebraMap ℤ_[p.val] (∀ i : Option Bool, G.Integers i)
  intro z hz
  apply mem_of_integral_values U (tensorScalars p.val B A e T) sc j.toRingHom ev.toRingHom _
    t (G.tripleCoordinate y) (funext hcoord) (G.triple_interpolation y hne) _ z
  · exact (G.exists_integerProductMap_iff _).mpr fun i =>
      norm_value_le_one_tensorImage p.val B A e D (v i) (hint i) z hz
  · ext a i
    change v i (algebraMap ℚ_[p.val] A (a : ℚ_[p.val])) =
      G.integerMap i (algebraMap ℤ_[p.val] (G.Integers i) a)
    rw [(v i).commutes,(G.integerMap i).commutes,IsScalarTower.algebraMap_apply ℤ_[p.val] ℚ_[p.val] (G.Field i)]
    rfl
  · intro z hz
    apply conductorIdeal_subset U z (hk _)
    apply Ideal.mem_iInf.mpr
    exact fun i => congrFun (RingHom.mem_ker.mp hz) i

end UnconditionalCounterexample.MultivariateSelection.ScreenedGuard

namespace UnconditionalCounterexample.Variations.PrivateGuards.Pair
open GuardSupport MultivariateSelection LocalAlgebra.TransportedIntegralImage RadicalConductor
open scoped TensorProduct
variable {r : ℕ} {p : PrimeIndex} {F : Poly r} {tests : Finset (Poly r)}
  (s : Pair p F tests) (G : ScreenedGuard r p)
  {B A : Type*} [CommRing B] [Algebra ℚ B] [CommRing A] [Algebra ℚ_[p.val] A]
  (e : ℚ_[p.val] ⊗[ℚ] B ≃ₐ[ℚ_[p.val]] A)
  (T D : Subring B) (v : ∀ i : Option Bool, A →ₐ[ℚ_[p.val]] G.Field i)

/-- The selected pair supplies the required two distinct residue classes
through its private and ordinary first coordinates. -/
theorem good_tensor_inclusion (b : B) (n : ℕ) (hb : (n : B)*b ∈ T) (hp : ¬p.val ∣ n)
    (hcoord : ∀ i, v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] b)) = s.triple G i 0)
    (hint : ∀ i (d : D), ‖v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (d : B)))‖ ≤ 1)
    (hk : (⨅ i, RingHom.ker (v i).toRingHom) ≤ conductorIdeal (image p.val B A e T)) :
    image p.val B A e D ≤ image p.val B A e T := by
  let y : Bool → ℤ_[p.val] := fun t => if t then s.ordinarily 0 else s.privately 0
  apply G.good_triple_tensor_inclusion e T D v b n hb hp y s.distinct _ hint hk
  intro i
  cases i with
  | none => exact hcoord none
  | some t => cases t <;> apply hcoord

end UnconditionalCounterexample.Variations.PrivateGuards.Pair
