import UnconditionalCounterexample.PoleAlgebra
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Scalar extension of the actual pole localization

For a field extension `k → K`, scalar extension of the pole algebra at `S`
is the pole algebra in `RatFunc K` at the coefficient-mapped set `S`.
The equivalence is constructed from localization and the polynomial tensor
equivalence. It provides an injective map into `RatFunc K`, with explicit
polynomial, variable, inverse, and numerator/denominator formulas.

The tensor algebra is not identified with the whole rational-function field.
The set `S` may be infinite; only nonvanishing of its polynomials is required.
The final helpers identify the linear submodule of the actual base-changed
subalgebra and descend equality by faithful flatness of the field extension.
They do not assume geometric separation or the desired recovery conclusion.
-/

noncomputable section
namespace UnconditionalCounterexample.ScalarExtension
open Polynomial TensorProduct

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- Extend polynomial coefficients and multiply by the left tensor scalar. -/
def polynomialTensorHom : K ⊗[k] k[X] →ₐ[K] K[X] :=
  AlgHom.liftEquiv k K _ _ (Polynomial.mapAlgHom (Algebra.ofId k K))

/-- The inverse polynomial map sends the variable to `1 ⊗ X`. -/
def polynomialTensorInv : K[X] →ₐ[K] K ⊗[k] k[X] :=
  Polynomial.aeval (1 ⊗ₜ[k] (Polynomial.X : k[X]))

@[simp] theorem polynomialTensorHom_tmul (x : K) (f : k[X]) :
    polynomialTensorHom k K (x ⊗ₜ[k] f) = x • f.map (algebraMap k K) := rfl

/-- The canonical polynomial scalar-extension equivalence. -/
def polynomialTensorEquiv : K ⊗[k] k[X] ≃ₐ[K] K[X] :=
  AlgEquiv.ofAlgHom (polynomialTensorHom k K) (polynomialTensorInv k K)
    (by ext; simp [polynomialTensorInv])
    (by ext; simp [polynomialTensorInv])

@[simp] theorem polynomialTensorEquiv_tmul (x : K) (f : k[X]) :
    polynomialTensorEquiv k K (x ⊗ₜ[k] f) = x • f.map (algebraMap k K) := rfl

/-- The actual image of the selected polynomials under coefficient extension. -/
def extendedSet (S : Set k[X]) : Set K[X] :=
  Polynomial.map (algebraMap k K) '' S

theorem extendedSet_nonzero (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0) :
    ∀ f ∈ extendedSet k K S, f ≠ 0 := by
  rintro _ ⟨f, hf, rfl⟩
  exact (Polynomial.map_ne_zero_iff (algebraMap k K).injective).mpr (hS f hf)

/-- The polynomial tensor ring acts through coefficient extension followed by
the canonical inclusion into the target pole algebra. -/
instance tensorPolynomialAlgebra (S : Set k[X]) :
    Algebra (K ⊗[k] k[X]) (PoleAlgebra.generated (extendedSet k K S)) :=
  ((algebraMap K[X] (PoleAlgebra.generated (extendedSet k K S))).comp
    (polynomialTensorEquiv k K).toRingHom).toAlgebra

set_option backward.isDefEq.respectTransparency false in
instance scalarTower_tensorPolynomial (S : Set k[X]) :
    IsScalarTower K (K ⊗[k] k[X]) (PoleAlgebra.generated (extendedSet k K S)) := by
  apply IsScalarTower.of_algebraMap_eq (R := K) (S := K ⊗[k] k[X])
    (A := PoleAlgebra.generated (extendedSet k K S))
  intro r
  change algebraMap K (PoleAlgebra.generated (extendedSet k K S)) r =
    algebraMap K[X] (PoleAlgebra.generated (extendedSet k K S))
      (polynomialTensorEquiv k K (algebraMap K (K ⊗[k] k[X]) r))
  rw [(polynomialTensorEquiv k K).commutes, ← IsScalarTower.algebraMap_apply]

theorem mapped_denominators (S : Set k[X]) :
    ((Submonoid.closure S).map
      (Algebra.TensorProduct.includeRight (R := k) (A := K))).map
        (polynomialTensorEquiv k K).toRingHom = Submonoid.closure (extendedSet k K S) := by
  rw [MonoidHom.map_mclosure, MonoidHom.map_mclosure, Set.image_image]
  change Submonoid.closure ((fun f : k[X] => polynomialTensorEquiv k K (1 ⊗ₜ[k] f)) '' S) =
    Submonoid.closure ((fun f : k[X] => f.map (algebraMap k K)) '' S)
  simp only [polynomialTensorEquiv_tmul, one_smul]

/-- The target is the localization at the mapped denominator monoid, with the
specified polynomial tensor algebra map. -/
theorem target_isLocalization (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0) :
    IsLocalization ((Submonoid.closure S).map
      (Algebra.TensorProduct.includeRight (R := k) (A := K)))
      (PoleAlgebra.generated (extendedSet k K S)) := by
  let : IsLocalization (Submonoid.closure (extendedSet k K S))
    (PoleAlgebra.generated (extendedSet k K S)) :=
      PoleAlgebra.isLocalization_generated _ (extendedSet_nonzero k K S hS)
  exact IsLocalization.of_ringEquiv_left (polynomialTensorEquiv k K).toRingEquiv
    (mapped_denominators k K S) (fun _ => rfl)

/-- Scalar extension is the actual pole localization at mapped polynomials. -/
def tensorEquiv (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0) :
    K ⊗[k] PoleAlgebra.generated S ≃ₐ[K] PoleAlgebra.generated (extendedSet k K S) := by
  let : IsLocalization (Submonoid.closure S) (PoleAlgebra.generated S) :=
    PoleAlgebra.isLocalization_generated S hS
  let : IsLocalization ((Submonoid.closure S).map
      (Algebra.TensorProduct.includeRight (R := k) (A := K)))
      (PoleAlgebra.generated (extendedSet k K S)) := target_isLocalization k K S hS
  exact IsLocalization.tensorProductEquivOfMapIncludeRight k K (Submonoid.closure S)
    (PoleAlgebra.generated S) (PoleAlgebra.generated (extendedSet k K S))

/-- The scalar-extended pole algebra embeds in the rational-function field. -/
def embedding (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0) :
    K ⊗[k] PoleAlgebra.generated S →ₐ[K] RatFunc K :=
  (PoleAlgebra.generated (extendedSet k K S)).val.comp (tensorEquiv k K S hS).toAlgHom

theorem embedding_injective (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0) :
    Function.Injective (embedding k K S hS) :=
  Subtype.val_injective.comp (tensorEquiv k K S hS).injective

@[simp] theorem tensorEquiv_tmul_polynomial
    (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0) (x : K) (f : k[X]) :
    tensorEquiv k K S hS (x ⊗ₜ[k] algebraMap k[X] (PoleAlgebra.generated S) f) =
      algebraMap K[X] (PoleAlgebra.generated (extendedSet k K S))
        (x • f.map (algebraMap k K)) := by
  let : IsLocalization (Submonoid.closure S) (PoleAlgebra.generated S) :=
    PoleAlgebra.isLocalization_generated S hS
  let : IsLocalization ((Submonoid.closure S).map
      (Algebra.TensorProduct.includeRight (R := k) (A := K)))
      (PoleAlgebra.generated (extendedSet k K S)) := target_isLocalization k K S hS
  change IsLocalization.tensorProductEquivOfMapIncludeRight k K (Submonoid.closure S)
    (PoleAlgebra.generated S) (PoleAlgebra.generated (extendedSet k K S))
      (x ⊗ₜ[k] algebraMap k[X] (PoleAlgebra.generated S) f) = _
  rw [IsLocalization.tensorProductEquivOfMapIncludeRight_tmul]
  rfl

@[simp] theorem embedding_tmul_polynomial
    (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0) (x : K) (f : k[X]) :
    embedding k K S hS (x ⊗ₜ[k] algebraMap k[X] (PoleAlgebra.generated S) f) =
      algebraMap K[X] (RatFunc K) (x • f.map (algebraMap k K)) := by
  change ((tensorEquiv k K S hS
    (x ⊗ₜ[k] algebraMap k[X] (PoleAlgebra.generated S) f)) : RatFunc K) = _
  rw [tensorEquiv_tmul_polynomial]
  rfl

/-- The image is exactly the target pole localization, not the ambient field. -/
theorem embedding_range (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0) :
    (embedding k K S hS).range = PoleAlgebra.generated (extendedSet k K S) := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    exact (tensorEquiv k K S hS x).property
  · intro hf
    obtain ⟨x, hx⟩ := (tensorEquiv k K S hS).surjective ⟨f, hf⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- Any actual fraction representation may be used to compute scalar extension.
Its denominator need only be nonzero; membership of `b` is already part of its type. -/
theorem embedding_one_tmul_fraction
    (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (b : PoleAlgebra.generated S) (a s : k[X]) (hs : s ≠ 0)
    (hb : (b : RatFunc k) = algebraMap k[X] (RatFunc k) a /
      algebraMap k[X] (RatFunc k) s) :
    embedding k K S hS (1 ⊗ₜ[k] b) =
      algebraMap K[X] (RatFunc K) (a.map (algebraMap k K)) /
      algebraMap K[X] (RatFunc K) (s.map (algebraMap k K)) := by
  have hs0 : algebraMap k[X] (RatFunc k) s ≠ 0 := RatFunc.algebraMap_ne_zero hs
  have hsK : algebraMap K[X] (RatFunc K) (s.map (algebraMap k K)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      ((Polynomial.map_ne_zero_iff (algebraMap k K).injective).mpr hs)
  have hprod : b * algebraMap k[X] (PoleAlgebra.generated S) s =
      algebraMap k[X] (PoleAlgebra.generated S) a := by
    apply Subtype.ext
    exact (eq_div_iff hs0).mp hb
  apply (eq_div_iff hsK).mpr
  calc
    _ = embedding k K S hS
        ((1 ⊗ₜ[k] b) * (1 ⊗ₜ[k] algebraMap k[X] (PoleAlgebra.generated S) s)) := by
      rw [map_mul, embedding_tmul_polynomial]
      simp only [one_smul]
    _ = embedding k K S hS
        (1 ⊗ₜ[k] algebraMap k[X] (PoleAlgebra.generated S) a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hprod]
    _ = _ := by rw [embedding_tmul_polynomial, one_smul]

theorem embedding_tmul_fraction
    (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (x : K) (b : PoleAlgebra.generated S) (a s : k[X]) (hs : s ≠ 0)
    (hb : (b : RatFunc k) = algebraMap k[X] (RatFunc k) a /
      algebraMap k[X] (RatFunc k) s) :
    embedding k K S hS (x ⊗ₜ[k] b) = algebraMap K (RatFunc K) x *
      (algebraMap K[X] (RatFunc K) (a.map (algebraMap k K)) /
        algebraMap K[X] (RatFunc K) (s.map (algebraMap k K))) := by
  have hx : x ⊗ₜ[k] b = x • (1 ⊗ₜ[k] b) := by
    simpa only [smul_eq_mul, mul_one] using
      (TensorProduct.smul_tmul' (R := k) x (1 : K) b).symm
  rw [hx, map_smul, embedding_one_tmul_fraction k K S hS b a s hs hb,
    Algebra.smul_def]

/-- Formula on arbitrary pure tensors using the canonical reduced numerator
and denominator of the represented rational function. -/
theorem embedding_tmul_apply (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (x : K) (b : PoleAlgebra.generated S) :
    embedding k K S hS (x ⊗ₜ[k] b) = algebraMap K (RatFunc K) x *
      (algebraMap K[X] (RatFunc K) ((b : RatFunc k).num.map (algebraMap k K)) /
        algebraMap K[X] (RatFunc K) ((b : RatFunc k).denom.map (algebraMap k K))) :=
  embedding_tmul_fraction k K S hS x b _ _ (b : RatFunc k).denom_ne_zero
    (RatFunc.num_div_denom (b : RatFunc k)).symm

@[simp] theorem embedding_one_tmul_X (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0) :
    embedding k K S hS (1 ⊗ₜ[k] ⟨RatFunc.X, PoleAlgebra.X_mem S⟩) = RatFunc.X := by
  change embedding k K S hS
    (1 ⊗ₜ[k] algebraMap k[X] (PoleAlgebra.generated S) Polynomial.X) = _
  rw [embedding_tmul_polynomial]
  simp

theorem embedding_one_tmul_inverse (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (f : k[X]) (hf : f ∈ S) :
    embedding k K S hS
      (1 ⊗ₜ[k] ⟨(algebraMap k[X] (RatFunc k) f)⁻¹, PoleAlgebra.inverse_mem hf⟩) =
      (algebraMap K[X] (RatFunc K) (f.map (algebraMap k K)))⁻¹ := by
  have h := embedding_one_tmul_fraction k K S hS
    ⟨(algebraMap k[X] (RatFunc k) f)⁻¹, PoleAlgebra.inverse_mem hf⟩
    1 f (hS f hf) (by simp)
  simpa using h

/-- Equality of extended linear submodules descends along a field extension. -/
theorem submodule_eq_of_baseChange_eq
    {M : Type*} [AddCommGroup M] [Module k M]
    (A B : Submodule k M) (h : A.baseChange K = B.baseChange K) : A = B :=
  Submodule.baseChange_injective h

theorem subalgebra_eq_of_baseChange_eq
    {B : Type*} [CommRing B] [Algebra k B]
    (A C : Subalgebra k B)
    (h : A.toSubmodule.baseChange K = C.toSubmodule.baseChange K) : A = C := by
  apply Subalgebra.toSubmodule_injective
  exact submodule_eq_of_baseChange_eq k K _ _ h

theorem subalgebra_eq_top_of_baseChange_eq_top
    {B : Type*} [CommRing B] [Algebra k B]
    (A : Subalgebra k B)
    (h : A.toSubmodule.baseChange K = ⊤) : A = ⊤ := by
  apply subalgebra_eq_of_baseChange_eq k K A ⊤
  simpa only [Algebra.top_toSubmodule, Submodule.baseChange_top] using h

/-- The actual image of scalar extension of a subalgebra under its inclusion. -/
def subalgebraBaseChange {B : Type*} [CommRing B] [Algebra k B]
    (A : Subalgebra k B) : Subalgebra K (K ⊗[k] B) :=
  (Algebra.TensorProduct.map (AlgHom.id K K) A.val).range

/-- Algebraic scalar extension has the expected underlying linear submodule. -/
theorem subalgebraBaseChange_toSubmodule
    {B : Type*} [CommRing B] [Algebra k B] (A : Subalgebra k B) :
    (subalgebraBaseChange k K A).toSubmodule = A.toSubmodule.baseChange K := by
  change LinearMap.range (Algebra.TensorProduct.map (AlgHom.id K K) A.val).toLinearMap =
    LinearMap.range (A.toSubmodule.subtype.baseChange K)
  congr 1

theorem subalgebraBaseChange_eq_top_iff
    {B : Type*} [CommRing B] [Algebra k B] (A : Subalgebra k B) :
    subalgebraBaseChange k K A = ⊤ ↔ A = ⊤ := by
  rw [← Algebra.toSubmodule_eq_top, subalgebraBaseChange_toSubmodule]
  constructor
  · exact subalgebra_eq_top_of_baseChange_eq_top k K A
  · intro h
    simp [h]

/-- The actual tensor extension of a finite algebra map remains finite. -/
theorem tensorMap_finite
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hf : f.Finite) :
    (Algebra.TensorProduct.map (AlgHom.id k K) f).toRingHom.Finite :=
  RingHom.Finite.tensorProductMap (f := AlgHom.id k K) (g := f) (RingHom.Finite.id K) hf

/-- Recovery after an explicit scalar-extension equivalence descends to the
original subalgebra. The equality of the image is the conclusion supplied by
the separate geometric-fibre argument. -/
theorem subalgebra_eq_top_of_mapped_baseChange_eq_top
    {B C : Type*} [CommRing B] [CommRing C] [Algebra k B] [Algebra K C]
    (A : Subalgebra k B) (e : K ⊗[k] B ≃ₐ[K] C)
    (h : (subalgebraBaseChange k K A).map e.toAlgHom = ⊤) : A = ⊤ := by
  apply (subalgebraBaseChange_eq_top_iff k K A).mp
  apply top_unique
  intro x _
  have hx : e x ∈ (subalgebraBaseChange k K A).map e.toAlgHom := by
    rw [h]
    trivial
  obtain ⟨y, hy, heq⟩ := hx
  exact (e.injective heq) ▸ hy

/-- A finite algebra map makes its target finite over the actual image subalgebra. -/
theorem finite_over_algHom_range
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (hf : f.Finite) :
    Module.Finite f.range B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra A f.range := f.rangeRestrict.toRingHom.toAlgebra
  have : IsScalarTower A f.range B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Finite A B := hf
  exact Module.Finite.of_restrictScalars_finite A f.range B

/-- A finite subalgebra inclusion remains finite over its actual scalar-extended
image, including after transporting the ambient algebra through an equivalence. -/
theorem finite_mapped_subalgebraBaseChange
    {B C : Type*} [CommRing B] [CommRing C] [Algebra k B] [Algebra K C]
    (A : Subalgebra k B) [Module.Finite A B]
    (e : K ⊗[k] B ≃ₐ[K] C) :
    Module.Finite ((subalgebraBaseChange k K A).map e.toAlgHom) C := by
  let f : K ⊗[k] A →ₐ[K] K ⊗[k] B := Algebra.TensorProduct.map (AlgHom.id K K) A.val
  have hf : f.Finite := tensorMap_finite k K A.val (RingHom.finite_algebraMap.mpr inferInstance)
  have hcomp : (e.toAlgHom.comp f).Finite := e.toRingEquiv.finite.comp hf
  have hrange : (e.toAlgHom.comp f).range = (subalgebraBaseChange k K A).map e.toAlgHom := by
    rw [AlgHom.range_comp]
    rfl
  rw [← hrange]
  exact finite_over_algHom_range _ hcomp

end UnconditionalCounterexample.ScalarExtension
