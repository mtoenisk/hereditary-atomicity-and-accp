import UnconditionalCounterexample.FibreSurjectivity
import UnconditionalCounterexample.PoleAlgebra
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Geometric fibres of the rational pole algebra

In a polynomial localization over an algebraically closed field with a retained point,
the maximal ideals are the evaluation kernels at retained points. For a finite
subalgebra extension, point separation gives uniqueness over each maximal fibre and a
simple-zero tangent identifies its fibre ideal. Surjectivity on maximal fibres then
gives equality of the algebras.

`pole_subalgebra_eq_top` states the result for the concrete `PoleAlgebra`,
with ordinary `RatFunc.eval` and the explicit quotient-rule derivative.
Finiteness is an explicit input supplied by the monogenic pole-at-infinity
step; scalar extension and faithful descent are separate obligations.
No Noetherian hypothesis on the subalgebra or degree restriction on omitted
polynomials is used.
-/

namespace UnconditionalCounterexample.CurveFibres

open Polynomial

universe u v
variable {k : Type u} [Field k]
variable (M : Submonoid (Polynomial k)) (B : Type v) [CommRing B]
  [Algebra k B] [Algebra (Polynomial k) B] [IsScalarTower k (Polynomial k) B]
  [IsLocalization M B]

/-- A retained point means every inverted polynomial is nonvanishing. -/
def Retained (α : k) : Prop := ∀ q : M, Polynomial.eval α (q : Polynomial k) ≠ 0

noncomputable def pointEval (α : k) (hα : Retained M α) : B →ₐ[k] k :=
  IsLocalization.liftAlgHom (f := Polynomial.aeval α)
    (fun q : M => isUnit_iff_ne_zero.mpr (by simpa using hα q))

@[simp] theorem pointEval_algebraMap (α : k) (hα : Retained M α) (p : Polynomial k) :
    pointEval M B α hα (algebraMap (Polynomial k) B p) = p.eval α := by
  simp only [pointEval, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  change Polynomial.aeval α p = p.eval α
  simp

theorem pointEval_surjective (α : k) (hα : Retained M α) :
    Function.Surjective (pointEval M B α hα) := by
  intro a
  exact ⟨algebraMap k B a, (pointEval M B α hα).commutes a⟩

theorem pointEval_ker_isMaximal (α : k) (hα : Retained M α) :
    (RingHom.ker (pointEval M B α hα).toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (pointEval_surjective M B α hα)

theorem pointEval_ker_under (α : k) (hα : Retained M α) :
    (RingHom.ker (pointEval M B α hα).toRingHom).under (Polynomial k) =
      Ideal.span {X - C α} := by
  rw [← Polynomial.ker_evalRingHom]
  ext p
  change pointEval M B α hα (algebraMap (Polynomial k) B p) = 0 ↔ p.eval α = 0
  rw [pointEval_algebraMap]

theorem pointEval_ker_eq_map (α : k) (hα : Retained M α) :
    RingHom.ker (pointEval M B α hα).toRingHom =
      (Ideal.span {X - C α}).map (algebraMap (Polynomial k) B) := by
  rw [← pointEval_ker_under M B α hα, IsLocalization.map_under M B]

/-- The existence of one retained point rules out the zero maximal ideal. -/
theorem maximal_under_ne_bot
    (hinj : Function.Injective (algebraMap (Polynomial k) B))
    (α₀ : k) (hα₀ : Retained M α₀) (n : Ideal B) (hn : n.IsMaximal) :
    n.under (Polynomial k) ≠ ⊥ := by
  intro hzero
  have hnzero : n = ⊥ := by
    rw [← IsLocalization.map_under M B n, hzero, Ideal.map_bot]
  have hbot : (⊥ : Ideal B).IsMaximal := hnzero ▸ hn
  have hkerzero := hbot.eq_of_le (pointEval_ker_isMaximal M B α₀ hα₀).ne_top bot_le
  have hz : algebraMap (Polynomial k) B (X - C α₀) ∈
      RingHom.ker (pointEval M B α₀ hα₀).toRingHom := by
    change pointEval M B α₀ hα₀ (algebraMap (Polynomial k) B (X - C α₀)) = 0
    rw [pointEval_algebraMap]
    simp
  rw [← hkerzero, Ideal.mem_bot] at hz
  have : (X - C α₀ : Polynomial k) = 0 := hinj (by simpa using hz)
  exact X_sub_C_ne_zero α₀ this

/-- Every maximal ideal of a polynomial localization with a retained point
is the kernel of evaluation at a retained point. -/
theorem maximal_eq_pointEval_ker [IsAlgClosed k]
    (hinj : Function.Injective (algebraMap (Polynomial k) B))
    (α₀ : k) (hα₀ : Retained M α₀) (n : Ideal B) (hn : n.IsMaximal) :
    ∃ α : k, ∃ hα : Retained M α,
      n = RingHom.ker (pointEval M B α hα).toRingHom := by
  have hnprime := (IsLocalization.isPrime_iff_isPrime_disjoint M B n).mp hn.isPrime
  obtain ⟨p, hp, hpgen⟩ :=
    (Ideal.isPrime_iff_of_isPrincipalIdealRing
      (maximal_under_ne_bot M B hinj α₀ hα₀ n hn)).mp hnprime.1
  have hdeg : p.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible k hp.irreducible]
    exact one_ne_zero
  obtain ⟨α, hαroot⟩ := IsAlgClosed.exists_root p hdeg
  have hrootideal : n.under (Polynomial k) = Ideal.span {X - C α} := by
    rw [hpgen]
    apply (PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible).eq_of_le
    · rw [← Polynomial.ker_evalRingHom]
      exact (RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom α)
        (fun c => ⟨C c, by simp⟩)).ne_top
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact dvd_iff_isRoot.mpr hαroot
  have hret : Retained M α := by
    intro q hq
    have hmem : (q : Polynomial k) ∈ n.under (Polynomial k) := by
      rw [hrootideal, Ideal.mem_span_singleton]
      exact dvd_iff_isRoot.mpr hq
    exact Set.disjoint_left.mp hnprime.2 q.property hmem
  refine ⟨α, hret, ?_⟩
  rw [pointEval_ker_eq_map, ← hrootideal, IsLocalization.map_under M B]

/-- Two k-valued algebra maps with the same kernel are equal, because both
fix every element of k. -/
theorem algHom_eq_of_ker_eq {R : Type*} [CommRing R] [Algebra k R]
    (f g : R →ₐ[k] k) (h : RingHom.ker f.toRingHom = RingHom.ker g.toRingHom) :
    f = g := by
  ext a
  have hf : a - algebraMap k R (f a) ∈ RingHom.ker f.toRingHom := by
    change f (a - algebraMap k R (f a)) = 0
    simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [h] at hf
  change g (a - algebraMap k R (f a)) = 0 at hf
  have hh : g a - f a = 0 := by
    simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using hf
  exact (sub_eq_zero.mp hh).symm

/-- Point separation forces different evaluation kernels on the subalgebra. -/
theorem point_eq_of_under_eq (A : Subalgebra k B)
    (hsep : ∀ α β : k, ∀ hα : Retained M α, ∀ hβ : Retained M β, α ≠ β →
      ∃ a : A, pointEval M B α hα a ≠ pointEval M B β hβ a)
    (α β : k) (hα : Retained M α) (hβ : Retained M β)
    (heq : (RingHom.ker (pointEval M B α hα).toRingHom).under A =
      (RingHom.ker (pointEval M B β hβ).toRingHom).under A) : α = β := by
  by_contra hne
  obtain ⟨a, ha⟩ := hsep α β hα hβ hne
  have hh : (pointEval M B α hα).comp A.val = (pointEval M B β hβ).comp A.val :=
    algHom_eq_of_ker_eq _ _ heq
  exact ha (DFunLike.congr_fun hh a)

/-- A simple-zero element and a unique maximal ideal determine the whole ideal. -/
theorem ideal_eq_pointEval_ker_of_simple_zero
    (I : Ideal B) (α : k) (hα : Retained M α)
    (hI : I ≤ RingHom.ker (pointEval M B α hα).toRingHom)
    (hunique : ∀ n : Ideal B, n.IsMaximal → I ≤ n →
      n = RingHom.ker (pointEval M B α hα).toRingHom)
    (f : Polynomial k) (hf : algebraMap (Polynomial k) B f ∈ I)
    (hdf : f.derivative.eval α ≠ 0) :
    I = RingHom.ker (pointEval M B α hα).toRingHom := by
  have hfroot : f.IsRoot α := by
    have hh := hI hf
    change pointEval M B α hα (algebraMap (Polynomial k) B f) = 0 at hh
    rwa [pointEval_algebraMap] at hh
  obtain ⟨g, rfl⟩ := dvd_iff_isRoot.mpr hfroot
  have hg : g.eval α ≠ 0 := by simpa using hdf
  let x : B := algebraMap (Polynomial k) B (X - C α)
  let y : B := algebraMap (Polynomial k) B g
  have hxy : x * y ∈ I := by simpa only [map_mul] using hf
  have htop : I ⊔ Ideal.span {y} = ⊤ := by
    by_contra hne
    obtain ⟨n, hn, hle⟩ := Ideal.exists_le_maximal _ hne
    have hnI : I ≤ n := le_sup_left.trans hle
    have hyspan : y ∈ Ideal.span ({y} : Set B) := Ideal.subset_span (Set.mem_singleton y)
    have hy : y ∈ n := (show Ideal.span {y} ≤ n from le_sup_right.trans hle) hyspan
    rw [hunique n hn hnI] at hy
    change pointEval M B α hα (algebraMap (Polynomial k) B g) = 0 at hy
    rw [pointEval_algebraMap] at hy
    exact hg hy
  apply le_antisymm hI
  rw [pointEval_ker_eq_map, Ideal.map_span, Set.image_singleton]
  rw [Ideal.span_singleton_le_iff_mem]
  have hone : (1 : B) ∈ I ⊔ Ideal.span {y} := by rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hone
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
  change x ∈ I
  rw [← mul_one x, ← hab, mul_add, ← mul_assoc]
  exact I.add_mem (I.mul_mem_left x ha) (I.mul_mem_right c hxy)

/-- Geometric separation and cleared simple-zero tangent witnesses compute
all maximal fibres of a finite subalgebra extension. -/
theorem maximal_fibre_eq_pointEval_ker [IsAlgClosed k]
    (hinj : Function.Injective (algebraMap (Polynomial k) B))
    (α₀ : k) (hα₀ : Retained M α₀) (A : Subalgebra k B) [Module.Finite A B]
    (hsep : ∀ α β : k, ∀ hα : Retained M α, ∀ hβ : Retained M β, α ≠ β →
      ∃ a : A, pointEval M B α hα a ≠ pointEval M B β hβ a)
    (htangent : ∀ α : k, ∀ hα : Retained M α, ∃ a : A, ∃ f q : Polynomial k,
      algebraMap (Polynomial k) B f = algebraMap (Polynomial k) B q *
        ((a : B) - algebraMap k B (pointEval M B α hα a)) ∧ f.derivative.eval α ≠ 0)
    (m : Ideal A) (hm : m.IsMaximal) :
    ∃ α : k, ∃ hα : Retained M α,
      m.map (algebraMap A B) = RingHom.ker (pointEval M B α hα).toRingHom := by
  let _ : m.IsMaximal := hm
  obtain ⟨n, hn, hnunder⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m
    (show RingHom.ker (algebraMap A B) ≤ m from by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (show Function.Injective (algebraMap A B) from Subtype.val_injective)]
      exact bot_le)
  obtain ⟨α, hα, hnα⟩ := maximal_eq_pointEval_ker M B hinj α₀ hα₀ n hn
  have hαunder : (RingHom.ker (pointEval M B α hα).toRingHom).under A = m := by
    rw [← hnα]
    exact hnunder
  have hle : m.map (algebraMap A B) ≤ RingHom.ker (pointEval M B α hα).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    exact hαunder.symm.le
  have huniq : ∀ n' : Ideal B, n'.IsMaximal → m.map (algebraMap A B) ≤ n' →
      n' = RingHom.ker (pointEval M B α hα).toRingHom := by
    intro n' hn' hmn'
    obtain ⟨β, hβ, hnβ⟩ := maximal_eq_pointEval_ker M B hinj α₀ hα₀ n' hn'
    have hβunder : n'.under A = m := by
      symm
      apply hm.eq_of_le
      · exact Ideal.comap_ne_top (algebraMap A B) hn'.ne_top
      · exact Ideal.map_le_iff_le_comap.mp hmn'
    have hβα : β = α := point_eq_of_under_eq M B A hsep β α hβ hα (by
      rw [← hnβ, hβunder, hαunder])
    subst β
    exact hnβ
  obtain ⟨a, f, q, hf, hdf⟩ := htangent α hα
  have hmemA : a - algebraMap k A (pointEval M B α hα a) ∈ m := by
    rw [← hαunder]
    change pointEval M B α hα ((a : B) - algebraMap k B (pointEval M B α hα a)) = 0
    simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hmemB : (a : B) - algebraMap k B (pointEval M B α hα a) ∈
      m.map (algebraMap A B) := Ideal.mem_map_of_mem _ hmemA
  have hfmem : algebraMap (Polynomial k) B f ∈ m.map (algebraMap A B) := by
    rw [hf]
    exact Ideal.mul_mem_left _ _ hmemB
  exact ⟨α, hα, ideal_eq_pointEval_ker_of_simple_zero M B _ α hα hle huniq f hfmem hdf⟩

theorem quotient_surjective_of_eq_pointEval_ker (A : Subalgebra k B)
    (I : Ideal B) (α : k) (hα : Retained M α)
    (hI : I = RingHom.ker (pointEval M B α hα).toRingHom) :
    Function.Surjective (algebraMap A (B ⧸ I)) := by
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨algebraMap k A (pointEval M B α hα b), ?_⟩
  change Ideal.Quotient.mk I (algebraMap k B (pointEval M B α hα b)) = Ideal.Quotient.mk I b
  apply Ideal.Quotient.eq.mpr
  rw [hI]
  change pointEval M B α hα (algebraMap k B (pointEval M B α hα b) - b) = 0
  simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

/-- A finite subalgebra of a polynomial localization is the whole ring when
it separates retained points and has a cleared simple-zero tangent at each. -/
theorem subalgebra_eq_top_of_separation_and_cleared_tangents [IsAlgClosed k]
    (hinj : Function.Injective (algebraMap (Polynomial k) B))
    (α₀ : k) (hα₀ : Retained M α₀) (A : Subalgebra k B) [Module.Finite A B]
    (hsep : ∀ α β : k, ∀ hα : Retained M α, ∀ hβ : Retained M β, α ≠ β →
      ∃ a : A, pointEval M B α hα a ≠ pointEval M B β hβ a)
    (htangent : ∀ α : k, ∀ hα : Retained M α, ∃ a : A, ∃ f q : Polynomial k,
      algebraMap (Polynomial k) B f = algebraMap (Polynomial k) B q *
        ((a : B) - algebraMap k B (pointEval M B α hα a)) ∧ f.derivative.eval α ≠ 0) :
    A = ⊤ := by
  apply subalgebra_eq_top_of_all_maximal_fibres
  intro m hm
  obtain ⟨α, hα, heq⟩ := maximal_fibre_eq_pointEval_ker M B hinj α₀ hα₀ A hsep htangent m hm
  exact quotient_surjective_of_eq_pointEval_ker M B A _ α hα heq

section PoleAlgebra

variable (S : Set (Polynomial k))

theorem retained_closure_iff (α : k) :
    Retained (Submonoid.closure S) α ↔ ∀ p ∈ S, p.eval α ≠ 0 := by
  constructor
  · intro h p hp
    exact h ⟨p, Submonoid.subset_closure hp⟩
  · intro h p
    have hall : ∀ q : Polynomial k, q ∈ Submonoid.closure S → q.eval α ≠ 0 := by
      intro q hq
      induction hq using Submonoid.closure_induction with
      | mem q hq => exact h q hq
      | one => simp
      | mul p q _ _ hp hq => simpa only [eval_mul] using mul_ne_zero hp hq
    exact hall p p.property

theorem denom_eval_ne_zero (hS : ∀ p ∈ S, p ≠ 0)
    (a : PoleAlgebra.generated S) (α : k) (hα : Retained (Submonoid.closure S) α) :
    (a : RatFunc k).denom.eval α ≠ 0 := by
  obtain ⟨q, hq, hden⟩ := (PoleAlgebra.mem_generated_iff_denom_dvd S hS (a : RatFunc k)).mp a.property
  obtain ⟨r, hr⟩ := hden
  have hh := hα ⟨q, hq⟩
  change q.eval α ≠ 0 at hh
  rw [hr, eval_mul] at hh
  exact left_ne_zero_of_mul hh

theorem num_eq_mul_denom (a : PoleAlgebra.generated S) :
    algebraMap (Polynomial k) (PoleAlgebra.generated S) (a : RatFunc k).num =
      a * algebraMap (Polynomial k) (PoleAlgebra.generated S) (a : RatFunc k).denom := by
  apply Subtype.ext
  exact (div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (a : RatFunc k)))).mp
    (RatFunc.num_div_denom (a : RatFunc k))

variable [IsLocalization (Submonoid.closure S) (PoleAlgebra.generated S)]

theorem pointEval_eq_ratFunc_eval (hS : ∀ p ∈ S, p ≠ 0)
    (a : PoleAlgebra.generated S) (α : k) (hα : Retained (Submonoid.closure S) α) :
    pointEval (Submonoid.closure S) (PoleAlgebra.generated S) α hα a =
      RatFunc.eval (RingHom.id k) α (a : RatFunc k) := by
  have hn := congrArg (pointEval (Submonoid.closure S) (PoleAlgebra.generated S) α hα)
    (num_eq_mul_denom S a)
  simp only [map_mul, pointEval_algebraMap] at hn
  change _ = (a : RatFunc k).num.eval α / (a : RatFunc k).denom.eval α
  exact (eq_div_iff (denom_eval_ne_zero S hS a α hα)).mpr hn.symm

/-- Evaluation of the usual quotient-rule formal derivative, using the
canonical reduced numerator and denominator. At retained points the denominator
is nonzero by `denom_eval_ne_zero`. -/
noncomputable def ratFuncDerivativeAt (a : RatFunc k) (α : k) : k :=
  (a.num.derivative.eval α * a.denom.eval α - a.num.eval α * a.denom.derivative.eval α) /
    (a.denom.eval α) ^ 2

theorem cleared_tangent_of_derivative_ne_zero
    (a : PoleAlgebra.generated S) (α : k) (hα : Retained (Submonoid.closure S) α)
    (hd : ratFuncDerivativeAt (a : RatFunc k) α ≠ 0) :
    ∃ f q : Polynomial k,
      algebraMap (Polynomial k) (PoleAlgebra.generated S) f =
        algebraMap (Polynomial k) (PoleAlgebra.generated S) q *
          (a - algebraMap k (PoleAlgebra.generated S)
            (pointEval (Submonoid.closure S) (PoleAlgebra.generated S) α hα a)) ∧
      f.derivative.eval α ≠ 0 := by
  let c := pointEval (Submonoid.closure S) (PoleAlgebra.generated S) α hα a
  let p := (a : RatFunc k).num
  let q := (a : RatFunc k).denom
  have hn := congrArg (pointEval (Submonoid.closure S) (PoleAlgebra.generated S) α hα)
    (num_eq_mul_denom S a)
  simp only [map_mul, pointEval_algebraMap] at hn
  have hcross : p.derivative.eval α * q.eval α - p.eval α * q.derivative.eval α ≠ 0 := by
    intro hzero
    apply hd
    change (p.derivative.eval α * q.eval α - p.eval α * q.derivative.eval α) /
      (q.eval α) ^ 2 = 0
    rw [hzero, zero_div]
  refine ⟨p - C c * q, q, ?_, ?_⟩
  · rw [map_sub, map_mul]
    change algebraMap (Polynomial k) (PoleAlgebra.generated S) p -
      algebraMap k (PoleAlgebra.generated S) c * algebraMap (Polynomial k) (PoleAlgebra.generated S) q = _
    rw [show algebraMap (Polynomial k) (PoleAlgebra.generated S) p =
      a * algebraMap (Polynomial k) (PoleAlgebra.generated S) q from num_eq_mul_denom S a]
    ring
  · intro hzero
    have hz : p.derivative.eval α - c * q.derivative.eval α = 0 := by simpa using hzero
    apply hcross
    calc
      p.derivative.eval α * q.eval α - p.eval α * q.derivative.eval α =
        q.eval α * (p.derivative.eval α - c * q.derivative.eval α) := by
          change p.eval α = c * q.eval α at hn
          rw [hn]
          ring
      _ = 0 := by rw [hz, mul_zero]

end PoleAlgebra

/-- The concrete algebraically closed curve recognition step for the actual pole algebra.
Point separation and the ordinary quotient-rule derivative are expressed on
actual rational functions. Finiteness of the extension remains explicit and is
provided by the monogenic pole-at-infinity step. -/
theorem pole_subalgebra_eq_top [IsAlgClosed k]
    (S : Set (Polynomial k)) (hS : ∀ p ∈ S, p ≠ 0)
    (α₀ : k) (hα₀ : ∀ p ∈ S, p.eval α₀ ≠ 0)
    (A : Subalgebra k (PoleAlgebra.generated S)) [Module.Finite A (PoleAlgebra.generated S)]
    (hsep : ∀ α β : k, (∀ p ∈ S, p.eval α ≠ 0) → (∀ p ∈ S, p.eval β ≠ 0) →
      α ≠ β → ∃ a : A,
        RatFunc.eval (RingHom.id k) α ((a : PoleAlgebra.generated S) : RatFunc k) ≠
          RatFunc.eval (RingHom.id k) β ((a : PoleAlgebra.generated S) : RatFunc k))
    (htangent : ∀ α : k, (∀ p ∈ S, p.eval α ≠ 0) → ∃ a : A,
      ratFuncDerivativeAt ((a : PoleAlgebra.generated S) : RatFunc k) α ≠ 0) : A = ⊤ := by
  let : IsLocalization (Submonoid.closure S) (PoleAlgebra.generated S) :=
    PoleAlgebra.isLocalization_generated S hS
  have hinj : Function.Injective (algebraMap (Polynomial k) (PoleAlgebra.generated S)) := by
    intro p q hpq
    apply RatFunc.algebraMap_injective k
    exact congrArg (fun x : PoleAlgebra.generated S => (x : RatFunc k)) hpq
  apply subalgebra_eq_top_of_separation_and_cleared_tangents
    (Submonoid.closure S) (PoleAlgebra.generated S) hinj α₀
      ((retained_closure_iff S α₀).mpr hα₀) A
  · intro α β hα hβ hne
    obtain ⟨a, ha⟩ := hsep α β ((retained_closure_iff S α).mp hα)
      ((retained_closure_iff S β).mp hβ) hne
    refine ⟨a, ?_⟩
    simpa only [pointEval_eq_ratFunc_eval S hS] using ha
  · intro α hα
    obtain ⟨a, ha⟩ := htangent α ((retained_closure_iff S α).mp hα)
    obtain ⟨f, q, hf, hd⟩ := cleared_tangent_of_derivative_ne_zero S (a : PoleAlgebra.generated S) α hα ha
    exact ⟨a, f, q, hf, hd⟩

end UnconditionalCounterexample.CurveFibres
