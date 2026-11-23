import UnconditionalCounterexample.Variations.DimensionClosedPoints
import Mathlib.RingTheory.Nakayama
import UnconditionalCounterexample.Variations.DimensionTensorConductor
import UnconditionalCounterexample.LocalAlgebra.ConductorLifting

namespace UnconditionalCounterexample.Variations

open MvPolynomial

/-- Lifting every residue class into the subalgebra suffices for full generation
in a finite integral lattice with principal reduction kernel. -/
theorem subalgebra_eq_top_of_residue_lifts {R A E : Type*} [CommRing R] [CommRing A]
    [CommRing E] [Algebra R A] [Module.Finite R A] (T : Subalgebra R A) (p : R)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal R)) (red : A →+* E)
    (hker : ∀ z, red z = 0 → ∃ w : A, z = p • w)
    (hlift : ∀ x : A, ∃ y ∈ T, red y = red x) : T = ⊤ := by
  let I := Ideal.span ({p} : Set R)
  have h : (⊤ : Submodule R A) ≤ T.toSubmodule ⊔ I • (⊤ : Submodule R A) := by
    intro x _
    obtain ⟨y, hy, he⟩ := hlift x
    obtain ⟨w, hw⟩ := hker (x-y) (by simp [he])
    exact Submodule.mem_sup.mpr ⟨y, hy, x-y, hw ▸ Submodule.smul_mem_smul
      (Ideal.subset_span (Set.mem_singleton p)) Submodule.mem_top, by abel⟩
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hp) h
  exact top_unique fun _ _ ↦ htop Submodule.mem_top

/-- Coordinates whose reductions generate pairwise distinct closed residue fields generate
the full product of their integral rings. This applies to the primary and guard product,
and to the two rational coordinates of a private pair. -/
theorem integral_closedPoint_product_generated {R k σ ι : Type*} [CommRing R] [Field k]
    [Finite ι] {O E : ι → Type*} [∀ i, CommRing (O i)] [∀ i, Field (E i)]
    [∀ i, Algebra R (O i)] [∀ i, Module.Finite R (O i)] [∀ i, Algebra k (E i)]
    (p : R) (hp : p ∈ Ideal.jacobson (⊥ : Ideal R)) (base : R →+* k)
    (hsurj : Function.Surjective base) (red : ∀ i, O i →+* E i)
    (hred : ∀ i c, red i (algebraMap R (O i) c) = algebraMap k (E i) (base c))
    (hker : ∀ i z, red i z = 0 → ∃ w : O i, z = p • w)
    (u : ∀ i, σ → O i)
    (hgen : ∀ i, Algebra.adjoin k (Set.range (red i ∘ u i)) = ⊤)
    (hdist : Function.Injective fun i ↦ RingHom.ker (aeval (R := k) (red i ∘ u i)).toRingHom)
    (T : Subalgebra R (∀ i, O i)) (hcoord : ∀ j : σ, (fun i ↦ u i j) ∈ T) : T = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  let f : (∀ i, O i) →+* (∀ i, E i) := RingHom.pi fun i ↦ (red i).comp (Pi.evalRingHom O i)
  apply subalgebra_eq_top_of_residue_lifts T p hp f
  · intro z hz
    choose w hw using fun i ↦ hker i (z i) (congrFun hz i)
    exact ⟨w, funext hw⟩
  intro x
  obtain ⟨P, hP⟩ := closedPointValues_surjective (fun i ↦ red i ∘ u i) hgen hdist (f x)
  obtain ⟨Q, hQ⟩ := map_surjective base hsurj P
  let b := aeval (R := R) (fun j ↦ (⟨fun i ↦ u i j, hcoord j⟩ : T)) Q
  refine ⟨b, b.property, funext fun i ↦ ?_⟩
  have h (Q : MvPolynomial σ R) :
      red i (((aeval (R := R) (fun j ↦ (⟨fun i ↦ u i j, hcoord j⟩ : T)) Q : T) : ∀ i, O i) i) =
        aeval (red i ∘ u i) (map base Q) := by
    induction Q using MvPolynomial.induction_on with
    | C c =>
      simp only [map_C, aeval_C, Subalgebra.coe_algebraMap, Pi.algebraMap_apply]
      exact hred i c
    | add A B ha hb => simpa only [map_add, Subalgebra.coe_add, Pi.add_apply] using congrArg₂ (· + ·) ha hb
    | mul_X P j h => simpa only [map_mul, map_X, aeval_X, Subalgebra.coe_mul, Pi.mul_apply,
        Function.comp_apply] using congrArg₂ (· * ·) h (rfl : red i (u i j) = _)
  exact (h Q).trans (hQ ▸ congrFun hP i)

open LocalAlgebra LocalAlgebra.TransportedIntegralImage RadicalConductor
open scoped TensorProduct

/-- At every prime, a single power of the uniformizer sends the actual larger
tensor image into the smaller one. The integral residue tuples need only belong
to a finitely generated lattice. -/
theorem exists_power_tensorImage_le {p : ℕ} [Fact p.Prime]
    {B A E O : Type*} [CommRing B] [Algebra ℚ B] [CommRing A] [Algebra ℚ_[p] A]
    [CommRing E] [Algebra ℚ_[p] E] [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O]
    [Algebra ℤ_[p] A] [IsScalarTower ℤ_[p] ℚ_[p] A]
    [Algebra ℤ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E]
    (e : ℚ_[p] ⊗[ℚ] B ≃ₐ[ℚ_[p]] A) (T D : Subring B) (ev : A →ₐ[ℚ_[p]] E)
    (he : Function.Surjective ev) (integral : O →ₐ[ℤ_[p]] E)
    (hval : ∀ z ∈ image p B A e D, ev z ∈ Set.range integral)
    (hker : RingHom.ker ev ≤ conductorIdeal (image p B A e T))
    (hclear : ∀ b : B, ∃ n : ℕ, 0 < n ∧ (n : B) * b ∈ T) :
    ∃ k : ℕ, ∀ z ∈ image p B A e D, (p : A)^k * z ∈ image p B A e T := by
  let U : Subalgebra ℤ_[p] A := {
    __ := image p B A e T
    algebraMap_mem' := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] A]
      exact scalar_mem p B A e T _ c.property }
  let f := ev.restrictScalars ℤ_[p]
  let L := LinearMap.range integral.toLinearMap
  have hL : L.FG := by
    change (LinearMap.range integral.toLinearMap).FG
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map _
  have hcl (z : A) : ∃ k : ℕ, (p : ℤ_[p])^k • z ∈ U := by
    obtain ⟨k,hk⟩ := exists_power_mul_mem p B A e T hclear z
    refine ⟨k, ?_⟩
    simpa only [Algebra.smul_def, map_pow, map_natCast] using (show (p : A)^k * z ∈ U from hk)
  obtain ⟨k, hk⟩ := scaled_lattice_mem_image U (p : ℤ_[p]) hcl f he L hL
  refine ⟨k, fun z hz ↦ ?_⟩
  apply (mem_iff_map_mem_of_kernel_subset (image p B A e T) ev.toRingHom
    (fun x hx ↦ by simpa using hker (show x ∈ RingHom.ker ev from hx) 1) _).mpr
  obtain ⟨y, hy, heq⟩ := hk (ev z) (hval z hz)
  refine ⟨y, hy, ?_⟩
  simpa only [f, AlgHom.restrictScalars_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul,
    map_pow, map_natCast, Algebra.smul_def] using heq

end UnconditionalCounterexample.Variations
