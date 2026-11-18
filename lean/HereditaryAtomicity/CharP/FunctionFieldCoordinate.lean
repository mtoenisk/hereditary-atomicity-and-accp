import HereditaryAtomicity.CharP.FunctionField

/-!
# Coherent rational-function structures at a chosen coordinate

A transcendental element u gives explicit polynomial and rational-function
algebra structures, both sending X to u. The scalar towers and transport of
finite dimension and separability allow the finite function-field arithmetic
to be applied after changing to a sole-pole coordinate.
-/

open scoped IntermediateField Polynomial
namespace HereditaryAtomicity.CharP.FunctionField

/-- The polynomial algebra structure which evaluates X at the chosen coordinate. -/
@[instance_reducible]
noncomputable def polynomialAlgebra
    {k L : Type*} [Field k] [Field L] [Algebra k L] (t : L) : Algebra k[X] L :=
  (Polynomial.aeval t).toRingHom.toAlgebra

/-- The rational-function algebra structure induced by k(X) ≃ k(t) ⊆ L. -/
@[instance_reducible]
noncomputable def rationalAlgebra
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (t : L) (ht : Transcendental k t) : Algebra (RatFunc k) L :=
  ((k⟮t⟯).val.toRingHom.comp (RatFunc.algEquivOfTranscendental t ht).toRingHom).toAlgebra

/-- The polynomial algebra map is ordinary evaluation at the coordinate. -/
theorem polynomialAlgebra_map
    {k L : Type*} [Field k] [Field L] [Algebra k L] (t : L) (f : k[X]) :
    let := polynomialAlgebra (k := k) t
    algebraMap k[X] L f = Polynomial.aeval t f := rfl

/-- The rational-function variable maps to the chosen coordinate. -/
theorem rationalAlgebra_map_X
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (t : L) (ht : Transcendental k t) :
    let := rationalAlgebra t ht
    algebraMap (RatFunc k) L RatFunc.X = t := by
  exact RatFunc.algEquivOfTranscendental_X t ht

/-- Polynomial evaluation respects the given constant-field algebra. -/
theorem polynomialAlgebra_scalarTower
    {k L : Type*} [Field k] [Field L] [Algebra k L] (t : L) :
    let := polynomialAlgebra (k := k) t
    IsScalarTower k k[X] L := by
  let := polynomialAlgebra (k := k) t
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap k L c = Polynomial.aeval t (algebraMap k k[X] c)
  simp

/-- The rational-coordinate algebra respects the given constant-field algebra. -/
theorem rationalAlgebra_scalarTower
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (t : L) (ht : Transcendental k t) :
    let := rationalAlgebra t ht
    IsScalarTower k (RatFunc k) L := by
  let := rationalAlgebra t ht
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (congrArg Subtype.val ((RatFunc.algEquivOfTranscendental t ht).commutes c)).symm

/-- The polynomial and rational-coordinate algebra structures are compatible. -/
theorem coordinate_scalarTower
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (t : L) (ht : Transcendental k t) :
    let := polynomialAlgebra (k := k) t
    let := rationalAlgebra t ht
    IsScalarTower k[X] (RatFunc k) L := by
  let := polynomialAlgebra (k := k) t
  let := rationalAlgebra t ht
  apply IsScalarTower.of_algebraMap_eq
  intro f
  change Polynomial.aeval t f = ((RatFunc.algEquivOfTranscendental t ht) (algebraMap k[X] (RatFunc k) f) : L)
  simp

/-- Finite dimension over the actual embedded k(t) transports to the explicit k(X) chart. -/
theorem rationalAlgebra_finite
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (t : L) (ht : Transcendental k t) [FiniteDimensional k⟮t⟯ L] :
    let := rationalAlgebra t ht
    FiniteDimensional (RatFunc k) L := by
  let := rationalAlgebra t ht
  let b := Module.finBasis k⟮t⟯ L
  refine (b.mapCoeffs (RatFunc.algEquivOfTranscendental t ht).symm.toRingEquiv ?_).finiteDimensional_of_finite
  intro c x
  change ((RatFunc.algEquivOfTranscendental t ht) ((RatFunc.algEquivOfTranscendental t ht).symm c) : L) * x = (c : L) * x
  simp

/-- Separability over the actual embedded k(t) transports to the explicit k(X) chart. -/
theorem rationalAlgebra_isSeparable
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (t : L) (ht : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ L] :
    let := rationalAlgebra t ht
    Algebra.IsSeparable (RatFunc k) L := by
  let := rationalAlgebra t ht
  apply Algebra.IsSeparable.of_equiv_equiv
    (RatFunc.algEquivOfTranscendental t ht).symm.toRingEquiv (RingEquiv.refl L)
  ext c
  change ((RatFunc.algEquivOfTranscendental t ht) ((RatFunc.algEquivOfTranscendental t ht).symm c) : L) = (c : L)
  simp
end HereditaryAtomicity.CharP.FunctionField
