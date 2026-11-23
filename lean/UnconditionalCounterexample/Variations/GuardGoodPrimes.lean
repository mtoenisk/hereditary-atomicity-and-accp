import UnconditionalCounterexample.Variations.GuardTensorImage
import UnconditionalCounterexample.Variations.GuardNorm
import UnconditionalCounterexample.RadicalConductor

/-!
# Full local tensor inclusion away from the coordinate denominator

After the conductor kernel calculation, one coordinate suffices at a
guard-only prime or at a guard paired with an ordinary rational evaluation.
The coordinate denominator is chosen once from the original subring.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.GuardUnramified

open Polynomial LocalAlgebra.TransportedIntegralImage RadicalConductor
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [Algebra (ZMod p) k] [Finite k]

abbrev scalarPair : ℤ_[p] →+* WittVector p k × ℤ_[p] :=
  (algebraMap ℤ_[p] (WittVector p k)).prod (RingHom.id _)

omit [Finite k] in
private theorem paired_surjective (x : WittVector p k)
    (hgen : Algebra.adjoin ℤ_[p] ({x} : Set (WittVector p k)) = ⊤)
    (hout : x.coeff 0 ∉ Set.range (algebraMap (ZMod p) k)) (y : ℤ_[p]) :
    Function.Surjective (eval₂RingHom (scalarPair p k) (x,y)) := by
  rintro ⟨u,v⟩
  obtain ⟨P,hu,hv⟩ := guard_primary_values p k x hgen hout y u v
  use P
  apply Prod.ext
  · have h : (RingHom.fst _ _).comp (eval₂RingHom (scalarPair p k) (x,y)) =
        (aeval x : Polynomial ℤ_[p] →ₐ[ℤ_[p]] WittVector p k).toRingHom := by
      apply Polynomial.ringHom_ext <;> simp [scalarPair]
    exact (DFunLike.congr_fun h P).trans hu
  · have h : (RingHom.snd _ _).comp (eval₂RingHom (scalarPair p k) (x,y)) = evalRingHom y := by
      apply Polynomial.ringHom_ext <;> simp [scalarPair]
    exact (DFunLike.congr_fun h P).trans hv

variable (B A : Type*) [CommRing B] [Algebra ℚ B] [CommRing A] [Algebra ℚ_[p] A]
    (e : ℚ_[p] ⊗[ℚ] B ≃ₐ[ℚ_[p]] A) (T : Subring B)
    (g : A →ₐ[ℚ_[p]] LocalField p k) (b : B) (n : ℕ) (hnt : (n : B) * b ∈ T) (hp : ¬ p ∣ n)
    (x : WittVector p k) (hgen : Algebra.adjoin ℤ_[p] ({x} : Set (WittVector p k)) = ⊤)
    (hx : g (e ((1 : ℚ_[p]) ⊗ₜ[ℚ] b)) = algebraMap _ _ x)

include hnt hp hx hgen in
theorem single_tensor_mem
    (hk : RingHom.ker g.toRingHom ≤ conductorIdeal (image p B A e T))
    (z : A) (hz : ‖g z‖ ≤ 1) : z ∈ image p B A e T := by
  let U := image p B A e T
  let t : U := ⟨_, coordinate_mem_of_prime_to p B A e T b n hnt hp⟩
  apply mem_of_integral_values U (tensorScalars p B A e T) (algebraMap ℤ_[p] (WittVector p k))
    (algebraMap _ (LocalField p k)) g.toRingHom _ t x hx _ _ z
  · obtain ⟨w,hw⟩ := (integral_iff p k _).mp ((norm_le_one_iff_valuation p k _).mp hz)
    exact ⟨w,hw⟩
  · ext a
    change g (algebraMap ℚ_[p] A (a : ℚ_[p])) = algebraMap _ (LocalField p k) (algebraMap ℤ_[p] (WittVector p k) a)
    rw [g.commutes, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p]]
    rfl
  · intro w
    have hm : w ∈ Algebra.adjoin ℤ_[p] ({x} : Set (WittVector p k)) := hgen ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    exact hm
  · exact fun w hw => conductorIdeal_subset U w (hk hw)

include hnt hp hx hgen in
theorem paired_tensor_mem
    (hout : x.coeff 0 ∉ Set.range (algebraMap (ZMod p) k)) (s : A →ₐ[ℚ_[p]] ℚ_[p])
    (y : ℤ_[p]) (hy : s (e ((1 : ℚ_[p]) ⊗ₜ[ℚ] b)) = y)
    (hk : RingHom.ker g.toRingHom ⊓ RingHom.ker s.toRingHom ≤ conductorIdeal (image p B A e T))
    (z : A) (hg : ‖g z‖ ≤ 1) (hs : ‖s z‖ ≤ 1) : z ∈ image p B A e T := by
  let U := image p B A e T
  let t : U := ⟨_, coordinate_mem_of_prime_to p B A e T b n hnt hp⟩
  let O := WittVector p k
  let L := LocalField p k
  let j := (algebraMap O L).prodMap (algebraMap ℤ_[p] ℚ_[p])
  let ev := g.toRingHom.prod s.toRingHom
  apply mem_of_integral_values U (tensorScalars p B A e T) (scalarPair p k) j ev _ t (x,y)
    (Prod.ext hx hy) (paired_surjective p k x hgen hout y) _ z
  · obtain ⟨w,hw⟩ := (integral_iff p k _).mp ((norm_le_one_iff_valuation p k _).mp hg)
    exact ⟨(w,⟨s z,hs⟩), Prod.ext hw rfl⟩
  · ext a
    · change g (algebraMap ℚ_[p] A (a : ℚ_[p])) = algebraMap O L (algebraMap ℤ_[p] O a)
      rw [g.commutes, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p]]
      rfl
    · change s (algebraMap ℚ_[p] A (a : ℚ_[p])) = (a : ℚ_[p])
      exact s.commutes _
  · intro w hw
    change ev w = 0 at hw
    exact conductorIdeal_subset U w (hk ⟨congrArg Prod.fst hw,congrArg Prod.snd hw⟩)

end UnconditionalCounterexample.Variations.GuardUnramified
