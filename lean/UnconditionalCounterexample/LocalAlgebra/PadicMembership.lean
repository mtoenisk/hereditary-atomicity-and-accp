import UnconditionalCounterexample.LocalAlgebra.LocalGlobal
import UnconditionalCounterexample.LocalAlgebra.PadicLocalization

/-!
# Detection of integral membership by p-adic tensor products
-/

namespace UnconditionalCounterexample.LocalAlgebra

open scoped TensorProduct

/-- A vector in every p-adic scalar extension of an integer lattice already
belongs to that lattice. No finiteness assumption on the lattice is needed. -/
theorem integerLattice_mem_iff_mem_all_padicImages
    {M : Type*} [AddCommGroup M] (A : Submodule ℤ M) (x : M) :
    x ∈ A ↔ ∀ (p : ℕ) (_ : Fact p.Prime),
      x ⊗ₜ[ℤ] (1 : PadicInt p) ∈ LocalOrderTensor.tensorImage (PadicInt p) A := by
  constructor
  · intro hx p _
    exact ⟨(⟨x, hx⟩ : A) ⊗ₜ[ℤ] (1 : PadicInt p), rfl⟩
  · intro h
    apply (submodule_mem_iff_local_denominators A x).mpr
    intro P hP
    obtain ⟨p, hp, rfl⟩ := integer_maximal_eq_span_prime P hP
    let : Fact p.Prime := ⟨hp⟩
    let : SMul ℤ (PadicLocalization.IntegerLocalization p) := Algebra.toSMul
    obtain ⟨s, hs⟩ := submodule_local_denominator_of_tensorImage
      (A := PadicLocalization.IntegerLocalization p) (B := PadicInt p)
      (PadicLocalization.primeIdeal p).primeCompl A x (h p inferInstance)
    exact ⟨s, s.property, hs⟩

end UnconditionalCounterexample.LocalAlgebra
