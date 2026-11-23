import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Residue fields of the conductor quotient

The intersection of the closed point ideals is the radical of
the conductor. The quotient by the conductor is finite dimensional by
nilpotent descent. Nonreducedness would yield a nonzero derivation to a
closed residue field. Surjective evaluation and scalar clearing also put a
multiple of each entire finitely generated integral lattice in the image.
-/

namespace UnconditionalCounterexample.Variations

open scoped KaehlerDifferential

/-- An essentially finite type algebra over a field is reduced if all derivations to
its closed residue fields vanish. The contrapositive extracts a residue-valued
first-order direction from any nonreduced thickening. -/
theorem isReduced_of_residue_derivations_eq_zero (k W : Type*) [Field k] [CommRing W]
    [Algebra k W] [Algebra.EssFiniteType k W]
    (h : ∀ (P : Ideal W), P.IsMaximal → ∀ D : Derivation k W (W ⧸ P), D = 0) :
    IsReduced W := by
  have hu : Algebra.FormallyUnramified k W := by
    constructor
    by_contra hn
    have : Nontrivial Ω[W⁄k] := not_subsingleton_iff_nontrivial.mp hn
    obtain ⟨S, hS, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule W Ω[W⁄k])).resolve_left bot_ne_top
    obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (isSimpleModule_iff_isCoatom.mpr hS)
    let L := e.toLinearMap.comp S.mkQ
    let H := KaehlerDifferential.linearMapEquivDerivation k W (M := W ⧸ P)
    have hL : L = 0 := H.map_eq_zero_iff.mp (h P hP (H L))
    have hsurj : Function.Surjective L := e.surjective.comp S.mkQ_surjective
    obtain ⟨z, hz⟩ := hsurj 1
    rw [hL, LinearMap.zero_apply] at hz
    let := hP
    exact zero_ne_one hz
  exact Algebra.FormallyUnramified.isReduced_of_field k W

/-- If the evaluation kernel is the radical of the conductor, the quotient by the conductor
is finite dimensional whenever the product of the residue fields is finite dimensional. -/
theorem finite_quotient_of_eval_ker_eq_radical {k B E : Type*} [Field k] [CommRing B] [CommRing E]
    [Algebra k B] [Algebra k E] [IsNoetherianRing B] [Module.Finite k E]
    (I : Ideal B) (f : B →ₐ[k] E) (hf : Function.Surjective f)
    (hker : RingHom.ker f = I.radical) : Module.Finite k (B ⧸ I) := by
  have hle : I ≤ RingHom.ker f := hker ▸ Ideal.le_radical
  let g := Ideal.Quotient.liftₐ I f (fun _ hz ↦ hle hz)
  apply Module.finite_of_surjective_of_ker_le_nilradical g
  · intro y
    obtain ⟨z, rfl⟩ := hf y
    exact ⟨Ideal.Quotient.mk I z, rfl⟩
  · intro x hx
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    change f z = 0 at hx
    obtain ⟨n, hn⟩ := hker ▸ (show z ∈ RingHom.ker f from hx)
    exact (show IsNilpotent (Ideal.Quotient.mk I z) from ⟨n, by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩)
  · exact IsNoetherian.noetherian _

variable {R B E : Type*} [CommRing R] [CommRing B] [CommRing E] [Algebra R B] [Algebra R E]

/-- Clearing denominators elementwise before surjective evaluation gives one power
that puts a whole finitely generated integral lattice in the actual evaluation image. -/
theorem scaled_lattice_mem_image (T : Subalgebra R B) (p : R)
    (hclear : ∀ x : B, ∃ k : ℕ, p^k • x ∈ T) (ev : B →ₐ[R] E)
    (he : Function.Surjective ev) (L : Submodule R E) (hL : L.FG) :
    ∃ k : ℕ, ∀ y ∈ L, p^k • y ∈ T.map ev := by
  classical
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hL
  choose x hx using fun i ↦ he (f i)
  choose k hk using fun i ↦ hclear (x i)
  let d := Finset.univ.sup k
  refine ⟨d, ?_⟩
  let m : E →ₗ[R] E := p^d • LinearMap.id
  suffices h : L ≤ (T.map ev).toSubmodule.comap m from fun y hy ↦ h hy
  rw [← hf, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hki : k i ≤ d := Finset.le_sup (f := k) (Finset.mem_univ i)
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hki
  change p^d • f i ∈ T.map ev
  refine ⟨p^d • x i, ?_, by
    change ev (p^d • x i) = _
    rw [map_smul, hx]⟩
  rw [hl, add_comm, pow_add, mul_smul]
  exact T.smul_mem (hk i) _

end UnconditionalCounterexample.Variations
