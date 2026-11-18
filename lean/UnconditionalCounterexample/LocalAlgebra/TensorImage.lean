import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor products of orders and their images
-/

namespace UnconditionalCounterexample.LocalAlgebra
namespace LocalOrderTensor

open scoped TensorProduct

variable {R M C : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup C] [Module R C]

/-- The actual image of the tensor product of a submodule in the ambient tensor
product. Keeping the image avoids identifying a submodule with its inclusion. -/
def tensorImage (C : Type*) [AddCommGroup C] [Module R C] (A : Submodule R M) :
    Submodule R (M ⊗[R] C) := LinearMap.range (A.subtype.rTensor C)

end LocalOrderTensor
end UnconditionalCounterexample.LocalAlgebra
