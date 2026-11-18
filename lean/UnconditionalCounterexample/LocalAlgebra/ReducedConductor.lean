import UnconditionalCounterexample.LocalAlgebra.PairLattice
import UnconditionalCounterexample.LocalAlgebra.ConductorLifting

/-!
# Exact lifting from the reduced pair quotient

An integral pair with unit difference transfers a common scalar multiplier to elements
with integral quotient coordinates. Lifting this assertion to the ambient algebra
requires that the quotient kernel belong to the smaller subalgebra.
-/

namespace UnconditionalCounterexample.LocalAlgebra

universe u v w

theorem scaled_mem_of_integral_pair
    {R : Type u} {K : Type v} {B : Type w}
    [CommRing R] [CommRing K] [CommRing B] [Algebra R K] [Algebra R B]
    (T : Subalgebra R B) (f : B →ₐ[R] (K × K))
    (hker : ∀ z : B, f z = 0 → z ∈ T)
    (α β n : R) (hdiff : IsUnit (β - α))
    (t : B) (ht : f t = (algebraMap R K α, algebraMap R K β))
    (hnt : n • t ∈ T) (x : B)
    (hx : ∃ a b : R, f x = (algebraMap R K a, algebraMap R K b)) :
    n • x ∈ T := by
  obtain ⟨a, b, hab⟩ := hx
  have hpair : n • (algebraMap R K α, algebraMap R K β) ∈ T.map f := by
    refine ⟨n • t, hnt, ?_⟩
    change f (n • t) = n • (algebraMap R K α, algebraMap R K β)
    rw [map_smul, ht]
  have h := mapped_pair_lattice_multiple_mem (T.map f) α β n hdiff hpair a b
  have himage : f (n • x) ∈ (T.toSubring).map f.toRingHom := by
    rw [map_smul, hab]
    exact h
  exact (mem_iff_map_mem_of_kernel_subset T.toSubring f.toRingHom hker (n • x)).mpr
    himage

end UnconditionalCounterexample.LocalAlgebra
