import UnconditionalCounterexample.CurveFibres
import UnconditionalCounterexample.CurveMonogenic
import UnconditionalCounterexample.ScalarExtension

/-!
# Recovery of a pole algebra from geometric separation

Denominator witnesses yield B = A[t], and a pole at infinity makes B finite over A.
After extending the scalars, point separation and nonzero derivatives identify the
geometric fibres. Faithful base change gives A = B over the original field.

The main theorem `subalgebra_eq_top_of_geometric_poles` retains only explicit
source hypotheses: a set of nonzero omitted polynomials, a retained geometric
point, denominator witnesses in A, one pole at infinity, and point/tangent
separation by actual members of A. Finiteness, scalar-extension injectivity,
maximal-fibre identification, and descent are conclusions of its proof.
No finite generation of A or degree restriction on omitted polynomials is
assumed. Producing these geometric inputs from the simultaneous construction
and escaping words is separate work.
-/

namespace UnconditionalCounterexample.CurveRecovery

open Polynomial

universe u v
variable {k : Type u} [Field k]

/-- The integral equation only needs its multiplicative relation; the ambient
ring need not itself be a field. -/
theorem integral_of_degree_gt_relation {R : Type v} [CommRing R] [Nontrivial R] [Algebra k R]
    (A : Subalgebra k R) (x : R) (s : A) (P Q : Polynomial k)
    (hdeg : Q.natDegree < P.natDegree)
    (hrel : aeval x P = (s : R) * aeval x Q) : IsIntegral A x := by
  let g : Polynomial A := P.map (algebraMap k A) - C s * Q.map (algebraMap k A)
  have hP : P ≠ 0 := by
    intro h
    simp [h] at hdeg
  have hd : (C s * Q.map (algebraMap k A)).degree <
      (P.map (algebraMap k A)).degree := by
    apply degree_lt_degree
    exact (natDegree_C_mul_le _ _).trans_lt (by simpa using hdeg)
  have hlc : g.leadingCoeff = algebraMap k A P.leadingCoeff := by
    dsimp [g]
    rw [leadingCoeff_sub_of_degree_lt hd, leadingCoeff_map]
  have hg : aeval x g = 0 := by
    dsimp [g]
    simp only [aeval_sub, aeval_mul, aeval_C, aeval_map_algebraMap]
    change aeval x P - (s : R) * aeval x Q = 0
    exact sub_eq_zero.mpr hrel
  have hint : IsIntegral A ((algebraMap k R P.leadingCoeff) * x) := by
    simpa only [hlc, Algebra.smul_def, ← IsScalarTower.algebraMap_apply k A R] using
      isIntegral_leadingCoeff_smul g x hg
  apply IsIntegral.of_mul_unit (r := algebraMap k A P.leadingCoeff⁻¹)
      (y := algebraMap k R P.leadingCoeff)
  · rw [← IsScalarTower.algebraMap_apply k A R, ← map_mul,
      inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hP), map_one]
  · simpa only [mul_comm] using hint

variable (S : Set (Polynomial k))

/-- The literal polynomial variable in the actual pole algebra. -/
noncomputable def coordinate : PoleAlgebra.generated S := algebraMap (Polynomial k) (PoleAlgebra.generated S) X

@[simp] theorem coe_coordinate : (coordinate S : RatFunc k) = RatFunc.X := rfl

@[simp] theorem aeval_coordinate (p : Polynomial k) :
    aeval (coordinate S) p = algebraMap (Polynomial k) (PoleAlgebra.generated S) p := by
  change aeval ((IsScalarTower.toAlgHom k (Polynomial k) (PoleAlgebra.generated S)) X) p = _
  rw [aeval_algHom_apply, aeval_X_left_apply]
  rfl

theorem integral_coordinate_of_pole_at_infinity
    (A : Subalgebra k (PoleAlgebra.generated S)) (s : A)
    (hdeg : (((s : PoleAlgebra.generated S) : RatFunc k).denom.natDegree) <
      (((s : PoleAlgebra.generated S) : RatFunc k).num.natDegree)) :
    IsIntegral A (coordinate S) := by
  apply integral_of_degree_gt_relation A (coordinate S) s
    ((s : PoleAlgebra.generated S) : RatFunc k).num
    ((s : PoleAlgebra.generated S) : RatFunc k).denom hdeg
  rw [aeval_coordinate, aeval_coordinate]
  exact CurveFibres.num_eq_mul_denom S s

theorem adjoin_coordinate_eq_top
    (A : Subalgebra k (PoleAlgebra.generated S))
    (hS : ∀ p ∈ S, ∃ a : A, p ∣ ((a : PoleAlgebra.generated S) : RatFunc k).denom) :
    Algebra.adjoin A ({coordinate S} : Set (PoleAlgebra.generated S)) = ⊤ := by
  let E := Algebra.adjoin A ({coordinate S} : Set (PoleAlgebra.generated S))
  let A' : Subalgebra k (RatFunc k) := A.map (PoleAlgebra.generated S).val
  have hA' : A' ≤ PoleAlgebra.generated S := by
    rintro x ⟨a, _, rfl⟩
    exact a.property
  have hden : ∀ p ∈ S, ∃ s ∈ A', p ∣ RatFunc.denom s := by
    intro p hp
    obtain ⟨a, ha⟩ := hS p hp
    exact ⟨((a : PoleAlgebra.generated S) : RatFunc k),
      ⟨(a : PoleAlgebra.generated S), a.property, rfl⟩, ha⟩
  have hfield := CurveMonogenic.adjoin_X_eq_pole_algebra A' S hA' hden
  have hmap : (E.restrictScalars k).map (PoleAlgebra.generated S).val =
      (Algebra.adjoin A' ({RatFunc.X} : Set (RatFunc k))).restrictScalars k := by
    dsimp [E]
    rw [Algebra.restrictScalars_adjoin, AlgHom.map_adjoin, Algebra.restrictScalars_adjoin]
    congr 1
    rw [Set.image_union, Set.image_singleton]
    rfl
  apply top_unique
  intro b _
  have hb : (b : RatFunc k) ∈ (E.restrictScalars k).map (PoleAlgebra.generated S).val := by
    rw [hmap, hfield]
    exact b.property
  obtain ⟨b', hb', heq⟩ := hb
  have heq' : b' = b := Subtype.ext heq
  subst b'
  exact hb'

theorem finite_of_poles
    (A : Subalgebra k (PoleAlgebra.generated S))
    (hS : ∀ p ∈ S, ∃ a : A, p ∣ ((a : PoleAlgebra.generated S) : RatFunc k).denom)
    (s : A) (hdeg : (((s : PoleAlgebra.generated S) : RatFunc k).denom.natDegree) <
      (((s : PoleAlgebra.generated S) : RatFunc k).num.natDegree)) :
    Module.Finite A (PoleAlgebra.generated S) := by
  let E := Algebra.adjoin A ({coordinate S} : Set (PoleAlgebra.generated S))
  let : Module.Finite A E := Algebra.finite_adjoin_simple_of_isIntegral
    (integral_coordinate_of_pole_at_infinity S A s hdeg)
  apply Module.Finite.of_surjective E.val.toLinearMap
  intro b
  have hb : b ∈ E := by
    change b ∈ Algebra.adjoin A ({coordinate S} : Set (PoleAlgebra.generated S))
    rw [adjoin_coordinate_eq_top S A hS]
    trivial
  exact ⟨⟨b, hb⟩, rfl⟩

/-- Curve recognition over an algebraically closed field with finiteness derived from actual poles.
Every selected denominator occurs in an actual member, and one actual member
has a pole at infinity. Separation and nonzero derivatives then recover B. -/
theorem pole_subalgebra_eq_top_of_poles [IsAlgClosed k]
    (hS : ∀ p ∈ S, p ≠ 0) (α₀ : k) (hα₀ : ∀ p ∈ S, p.eval α₀ ≠ 0)
    (A : Subalgebra k (PoleAlgebra.generated S))
    (hpoles : ∀ p ∈ S, ∃ a : A, p ∣ ((a : PoleAlgebra.generated S) : RatFunc k).denom)
    (s : A) (hdeg : (((s : PoleAlgebra.generated S) : RatFunc k).denom.natDegree) <
      (((s : PoleAlgebra.generated S) : RatFunc k).num.natDegree))
    (hsep : ∀ α β : k, (∀ p ∈ S, p.eval α ≠ 0) → (∀ p ∈ S, p.eval β ≠ 0) →
      α ≠ β → ∃ a : A,
        RatFunc.eval (RingHom.id k) α ((a : PoleAlgebra.generated S) : RatFunc k) ≠
          RatFunc.eval (RingHom.id k) β ((a : PoleAlgebra.generated S) : RatFunc k))
    (htangent : ∀ α : k, (∀ p ∈ S, p.eval α ≠ 0) → ∃ a : A,
      CurveFibres.ratFuncDerivativeAt ((a : PoleAlgebra.generated S) : RatFunc k) α ≠ 0) :
    A = ⊤ := by
  let : Module.Finite A (PoleAlgebra.generated S) := finite_of_poles S A hpoles s hdeg
  exact CurveFibres.pole_subalgebra_eq_top S hS α₀ hα₀ A hsep htangent

section ScalarExtension

open TensorProduct

variable (K : Type u) [Field K] [Algebra k K]

/-- The actual scalar image of a pole-algebra element. -/
noncomputable def baseElement (hS : ∀ p ∈ S, p ≠ 0) (b : PoleAlgebra.generated S) :
    PoleAlgebra.generated (ScalarExtension.extendedSet k K S) :=
  ScalarExtension.tensorEquiv k K S hS (1 ⊗ₜ[k] b)

/-- Retained geometric points use the original polynomial coefficients. -/
theorem retained_extendedSet_iff (α : K) :
    CurveFibres.Retained (Submonoid.closure (ScalarExtension.extendedSet k K S)) α ↔
      ∀ p ∈ S, p.eval₂ (algebraMap k K) α ≠ 0 := by
  rw [CurveFibres.retained_closure_iff]
  constructor
  · intro h p hp
    have hh := h (p.map (algebraMap k K)) ⟨p, hp, rfl⟩
    simpa only [eval_map] using hh
  · intro h p hp
    obtain ⟨p, hp, rfl⟩ := hp
    simpa only [eval_map] using h p hp

theorem geometric_denom_ne_zero (hS : ∀ p ∈ S, p ≠ 0)
    (b : PoleAlgebra.generated S) (α : K)
    (hα : ∀ p ∈ S, p.eval₂ (algebraMap k K) α ≠ 0) :
    (b : RatFunc k).denom.eval₂ (algebraMap k K) α ≠ 0 := by
  have hall : ∀ q : Polynomial k, q ∈ Submonoid.closure S → q.eval₂ (algebraMap k K) α ≠ 0 := by
    intro q hq
    induction hq using Submonoid.closure_induction with
    | mem p hp => exact hα p hp
    | one => simp
    | mul p q _ _ hp hq => simpa only [eval₂_mul] using mul_ne_zero hp hq
  obtain ⟨q, hq, r, hr⟩ := (PoleAlgebra.mem_generated_iff_denom_dvd S hS (b : RatFunc k)).mp b.property
  have hh := hall q hq
  rw [hr, eval₂_mul] at hh
  exact left_ne_zero_of_mul hh

theorem baseElement_num_relation (hS : ∀ p ∈ S, p ≠ 0) (b : PoleAlgebra.generated S) :
    algebraMap (Polynomial K) (PoleAlgebra.generated (ScalarExtension.extendedSet k K S))
      ((b : RatFunc k).num.map (algebraMap k K)) =
    baseElement S K hS b *
      algebraMap (Polynomial K) (PoleAlgebra.generated (ScalarExtension.extendedSet k K S))
        ((b : RatFunc k).denom.map (algebraMap k K)) := by
  apply Subtype.ext
  change algebraMap (Polynomial K) (RatFunc K) ((b : RatFunc k).num.map (algebraMap k K)) =
    ScalarExtension.embedding k K S hS (1 ⊗ₜ[k] b) *
      algebraMap (Polynomial K) (RatFunc K) ((b : RatFunc k).denom.map (algebraMap k K))
  rw [ScalarExtension.embedding_one_tmul_fraction k K S hS b _ _ (b : RatFunc k).denom_ne_zero
      (RatFunc.num_div_denom (b : RatFunc k)).symm,
    div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero
      ((Polynomial.map_ne_zero_iff (algebraMap k K).injective).mpr (b : RatFunc k).denom_ne_zero))]

variable [IsLocalization (Submonoid.closure (ScalarExtension.extendedSet k K S))
  (PoleAlgebra.generated (ScalarExtension.extendedSet k K S))]

theorem pointEval_baseElement (hS : ∀ p ∈ S, p ≠ 0)
    (b : PoleAlgebra.generated S) (α : K)
    (hα : CurveFibres.Retained (Submonoid.closure (ScalarExtension.extendedSet k K S)) α) :
    CurveFibres.pointEval (Submonoid.closure (ScalarExtension.extendedSet k K S))
      (PoleAlgebra.generated (ScalarExtension.extendedSet k K S)) α hα (baseElement S K hS b) =
      RatFunc.eval (algebraMap k K) α (b : RatFunc k) := by
  have hn := congrArg (CurveFibres.pointEval
    (Submonoid.closure (ScalarExtension.extendedSet k K S))
      (PoleAlgebra.generated (ScalarExtension.extendedSet k K S)) α hα)
        (baseElement_num_relation S K hS b)
  simp only [map_mul, CurveFibres.pointEval_algebraMap, eval_map] at hn
  exact (eq_div_iff (geometric_denom_ne_zero S K hS b α
    ((retained_extendedSet_iff S K α).mp hα))).mpr hn.symm

/-- The ordinary quotient-rule derivative evaluated at a geometric point. -/
noncomputable def geometricDerivativeAt (b : RatFunc k) (α : K) : K :=
  (b.num.derivative.eval₂ (algebraMap k K) α * b.denom.eval₂ (algebraMap k K) α -
    b.num.eval₂ (algebraMap k K) α * b.denom.derivative.eval₂ (algebraMap k K) α) /
      (b.denom.eval₂ (algebraMap k K) α) ^ 2

end ScalarExtension

/-- Clearing a nonzero derivative uses only the numerator relation in the
actual localization; reduction of the fraction is unnecessary. -/
theorem cleared_tangent_of_fraction_relation
    {F : Type*} [Field F] (M : Submonoid (Polynomial F)) (R : Type*) [CommRing R]
    [Algebra F R] [Algebra (Polynomial F) R] [IsScalarTower F (Polynomial F) R]
    [IsLocalization M R] (a : R) (α : F) (hα : CurveFibres.Retained M α)
    (P Q : Polynomial F)
    (hrel : algebraMap (Polynomial F) R P = a * algebraMap (Polynomial F) R Q)
    (hcross : P.derivative.eval α * Q.eval α - P.eval α * Q.derivative.eval α ≠ 0) :
    ∃ f : Polynomial F,
      algebraMap (Polynomial F) R f = algebraMap (Polynomial F) R Q *
        (a - algebraMap F R (CurveFibres.pointEval M R α hα a)) ∧ f.derivative.eval α ≠ 0 := by
  let c := CurveFibres.pointEval M R α hα a
  have hn := congrArg (CurveFibres.pointEval M R α hα) hrel
  simp only [map_mul, CurveFibres.pointEval_algebraMap] at hn
  refine ⟨P - C c * Q, ?_, ?_⟩
  · rw [map_sub, map_mul]
    rw [show algebraMap (Polynomial F) R (C c) = algebraMap F R c from
      (IsScalarTower.algebraMap_apply F (Polynomial F) R c).symm]
    rw [hrel]
    ring
  · intro hzero
    have hz : P.derivative.eval α - c * Q.derivative.eval α = 0 := by simpa using hzero
    apply hcross
    calc
      P.derivative.eval α * Q.eval α - P.eval α * Q.derivative.eval α =
        Q.eval α * (P.derivative.eval α - c * Q.derivative.eval α) := by
          change P.eval α = c * Q.eval α at hn
          rw [hn]
          ring
      _ = 0 := by rw [hz, mul_zero]

theorem baseElement_mem_mappedBaseChange
    (K : Type u) [Field K] [Algebra k K] (hS : ∀ p ∈ S, p ≠ 0)
    (A : Subalgebra k (PoleAlgebra.generated S)) (a : A) :
    baseElement S K hS (a : PoleAlgebra.generated S) ∈
      (ScalarExtension.subalgebraBaseChange k K A).map
        (ScalarExtension.tensorEquiv k K S hS).toAlgHom := by
  apply Subalgebra.mem_map.mpr
  refine ⟨(1 : K) ⊗ₜ[k] (a : PoleAlgebra.generated S), ?_, rfl⟩
  refine ⟨(1 : K) ⊗ₜ[k] a, ?_⟩
  rfl

/-- Curve recognition over the original field, with every geometric input stated on
actual members of A and descent along an algebraically closed extension.
Finiteness, maximal-fibre recovery, and faithful descent are proved internally. -/
theorem subalgebra_eq_top_of_geometric_poles
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    (hS : ∀ p ∈ S, p ≠ 0)
    (α₀ : K) (hα₀ : ∀ p ∈ S, p.eval₂ (algebraMap k K) α₀ ≠ 0)
    (A : Subalgebra k (PoleAlgebra.generated S))
    (hpoles : ∀ p ∈ S, ∃ a : A, p ∣ ((a : PoleAlgebra.generated S) : RatFunc k).denom)
    (s : A) (hdeg : (((s : PoleAlgebra.generated S) : RatFunc k).denom.natDegree) <
      (((s : PoleAlgebra.generated S) : RatFunc k).num.natDegree))
    (hsep : ∀ α β : K,
      (∀ p ∈ S, p.eval₂ (algebraMap k K) α ≠ 0) →
      (∀ p ∈ S, p.eval₂ (algebraMap k K) β ≠ 0) → α ≠ β → ∃ a : A,
        RatFunc.eval (algebraMap k K) α ((a : PoleAlgebra.generated S) : RatFunc k) ≠
          RatFunc.eval (algebraMap k K) β ((a : PoleAlgebra.generated S) : RatFunc k))
    (htangent : ∀ α : K, (∀ p ∈ S, p.eval₂ (algebraMap k K) α ≠ 0) → ∃ a : A,
      geometricDerivativeAt K ((a : PoleAlgebra.generated S) : RatFunc k) α ≠ 0) : A = ⊤ := by
  let E := ScalarExtension.extendedSet k K S
  let B := PoleAlgebra.generated E
  let e := ScalarExtension.tensorEquiv k K S hS
  let A' : Subalgebra K B := (ScalarExtension.subalgebraBaseChange k K A).map e.toAlgHom
  let : Module.Finite A (PoleAlgebra.generated S) := finite_of_poles S A hpoles s hdeg
  let : Module.Finite A' B := ScalarExtension.finite_mapped_subalgebraBaseChange k K A e
  let : IsLocalization (Submonoid.closure E) B :=
    PoleAlgebra.isLocalization_generated E (ScalarExtension.extendedSet_nonzero k K S hS)
  apply ScalarExtension.subalgebra_eq_top_of_mapped_baseChange_eq_top k K A e
  change A' = ⊤
  have hinj : Function.Injective (algebraMap (Polynomial K) B) := by
    intro p q hpq
    apply RatFunc.algebraMap_injective K
    exact congrArg (fun b : B => (b : RatFunc K)) hpq
  apply CurveFibres.subalgebra_eq_top_of_separation_and_cleared_tangents
    (Submonoid.closure E) B hinj α₀ ((retained_extendedSet_iff S K α₀).mpr hα₀) A'
  · intro α β hα hβ hne
    obtain ⟨a, ha⟩ := hsep α β ((retained_extendedSet_iff S K α).mp hα)
      ((retained_extendedSet_iff S K β).mp hβ) hne
    let a' : A' := ⟨baseElement S K hS a, baseElement_mem_mappedBaseChange S K hS A a⟩
    refine ⟨a', ?_⟩
    change CurveFibres.pointEval (Submonoid.closure E) B α hα (baseElement S K hS a) ≠
      CurveFibres.pointEval (Submonoid.closure E) B β hβ (baseElement S K hS a)
    intro heq
    apply ha
    exact (pointEval_baseElement S K hS a α hα).symm.trans
      (heq.trans (pointEval_baseElement S K hS a β hβ))
  · intro α hα
    obtain ⟨a, ha⟩ := htangent α ((retained_extendedSet_iff S K α).mp hα)
    let a' : A' := ⟨baseElement S K hS a, baseElement_mem_mappedBaseChange S K hS A a⟩
    let P := (((a : PoleAlgebra.generated S) : RatFunc k).num).map (algebraMap k K)
    let Q := (((a : PoleAlgebra.generated S) : RatFunc k).denom).map (algebraMap k K)
    have hcross : P.derivative.eval α * Q.eval α - P.eval α * Q.derivative.eval α ≠ 0 := by
      intro hz
      have hz' :
          (((a : PoleAlgebra.generated S) : RatFunc k).num.derivative.eval₂ (algebraMap k K) α) *
            (((a : PoleAlgebra.generated S) : RatFunc k).denom.eval₂ (algebraMap k K) α) -
          (((a : PoleAlgebra.generated S) : RatFunc k).num.eval₂ (algebraMap k K) α) *
            (((a : PoleAlgebra.generated S) : RatFunc k).denom.derivative.eval₂ (algebraMap k K) α) = 0 := by
        simpa only [P, Q, derivative_map, eval_map] using hz
      exact ha (by simp only [geometricDerivativeAt, hz', zero_div])
    obtain ⟨f, hf, hd⟩ := cleared_tangent_of_fraction_relation (Submonoid.closure E) B
      (baseElement S K hS a) α hα P Q (baseElement_num_relation S K hS a) hcross
    exact ⟨a', f, Q, hf, hd⟩

end UnconditionalCounterexample.CurveRecovery
