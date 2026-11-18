import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Tactic.Ring

/-!
# The integral lattice at a pair of rational evaluations

A primary argument and a guard argument differ by a unit in the p-adic integers.
Together with the diagonal constants, their pair spans the full integral coefficient
lattice. Multiplying the pair by n gives the analogous containment for n times the
lattice.
-/

namespace UnconditionalCounterexample.LocalAlgebra

universe u v

/-- Diagonal scalars and a scaled pair with unit difference contain the same
scalar multiple of the whole product. No division in the source ring is used. -/
theorem pair_lattice_multiple_mem
    {R : Type u} [CommRing R] (S : Subalgebra R (R × R))
    (α β n : R) (hdiff : IsUnit (β - α)) (hpair : n • (α, β) ∈ S)
    (x y : R) : n • (x, y) ∈ S := by
  obtain ⟨u, hu⟩ := hdiff
  let d : R := (y - x) * ↑u⁻¹
  let c : R := x - d * α
  have hdu : d * (β - α) = y - x := by
    dsimp [d]
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  have hmem : d • (n • (α, β)) + (n * c) • (1 : R × R) ∈ S :=
    S.add_mem (S.smul_mem hpair d) (S.smul_mem S.one_mem (n * c))
  convert hmem using 1
  apply Prod.ext
  · change n * x = d * (n * α) + (n * c) * 1
    dsimp [c]
    ring
  · change n * y = d * (n * β) + (n * c) * 1
    dsimp [c]
    calc
      n * y = n * x + n * (y - x) := by ring
      _ = n * x + n * (d * (β - α)) := by rw [hdu]
      _ = d * (n * β) + n * (x - d * α) * 1 := by ring

/-- The same lattice statement after applying the actual coefficient algebra
map into an ambient ring. This is the form used for the reduced p-adic quotient. -/
theorem mapped_pair_lattice_multiple_mem
    {R : Type u} {K : Type v} [CommRing R] [CommRing K] [Algebra R K]
    (S : Subalgebra R (K × K)) (α β n : R) (hdiff : IsUnit (β - α))
    (hpair : n • (algebraMap R K α, algebraMap R K β) ∈ S)
    (x y : R) : n • (algebraMap R K x, algebraMap R K y) ∈ S := by
  let f : (R × R) →ₐ[R] (K × K) :=
    AlgHom.prodMap (Algebra.ofId R K) (Algebra.ofId R K)
  have hpair' : n • (α, β) ∈ S.comap f := by
    change f (n • (α, β)) ∈ S
    rw [map_smul]
    exact hpair
  have h := pair_lattice_multiple_mem (S.comap f) α β n hdiff hpair' x y
  change f (n • (x, y)) ∈ S at h
  rw [map_smul] at h
  exact h

end UnconditionalCounterexample.LocalAlgebra
