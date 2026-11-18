import HereditaryAtomicity.DVRBase.SourceConstruction
import HereditaryAtomicity.DVRBase.BaseValues
import HereditaryAtomicity.DVRBase.ModelMembership

/-!
# Finite source Laurent expressions and their actual evaluation

Coefficients live in the fraction field of the original coefficient subring.
Evaluation uses its canonical field embedding and the actual source ratios.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal

variable {k K : Type*} [Field k] [Field K] {n : ℕ}

/-- Evaluation of a Laurent exponent vector at nonzero field elements. -/
def exponentEvaluation (y : Fin n → K) (hy : ∀ i, y i ≠ 0) :
    Multiplicative (Fin n → ℤ) →* K where
  toFun β := ∏ i, y i ^ β.toAdd i
  map_one' := by simp
  map_mul' β γ := by
    change (∏ i, y i ^ (β.toAdd i + γ.toAdd i)) = _
    simp_rw [zpow_add₀ (hy _)]
    exact Finset.prod_mul_distrib

/-- The literal evaluation ring homomorphism, retaining a specified coefficient map. -/
def laurentEvaluation (f : k →+* K) (y : Fin n → K) (hy : ∀ i, y i ≠ 0) :
    Laurent k n →+* K :=
  AddMonoidAlgebra.liftNCRingHom f (exponentEvaluation y hy) (fun _ _ => Commute.all _ _)

@[simp] theorem laurentEvaluation_single (f : k →+* K)
    (y : Fin n → K) (hy : ∀ i, y i ≠ 0) (β : Fin n → ℤ) (c : k) :
    laurentEvaluation f y hy (AddMonoidAlgebra.single β c) = f c * ∏ i, y i ^ β i := by
  exact AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _

@[simp] theorem laurentEvaluation_constant (f : k →+* K)
    (y : Fin n → K) (hy : ∀ i, y i ≠ 0) (c : k) :
    laurentEvaluation f y hy (AddMonoidAlgebra.single 0 c) = f c := by simp

@[simp] theorem laurentEvaluation_variable (f : k →+* K)
    (y : Fin n → K) (hy : ∀ i, y i ≠ 0) (i : Fin n) :
    laurentEvaluation f y hy (variableMonomial i) = y i := by
  classical
  simp [variableMonomial, Pi.single_apply]

/-- The exact step equation of the finite endpoint monomials. -/
theorem endpointMonomial_step (π : k) (κ : ℕ) {j : ℕ} (hj : j < n) :
    endpointMonomial π κ j =
      endpointMonomial π κ (j + 1) * variableMonomial (⟨j, hj⟩ : Fin n) := by
  classical
  simp only [endpointMonomial, variableMonomial, AddMonoidAlgebra.single_mul_single, mul_one]
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

namespace SourceBlockData
variable {R : Subring K} (D : SourceBlockData R)

/-- Evaluation over the original coefficient fraction field. -/
def evaluation (O : Subring K) (n : ℕ) : Laurent (FractionRing O) n →+* K :=
  laurentEvaluation (coefficientFractionEmbedding O) (fun i => (D.ratio i.val : K))
    (fun i => Subtype.coe_ne_coe.mpr (D.ratio_ne_zero i.val))

@[simp] theorem evaluation_variable (O : Subring K) (i : Fin n) :
    D.evaluation O n (variableMonomial i) = (D.ratio i.val : K) :=
  laurentEvaluation_variable _ _ _ i

@[simp] theorem evaluation_coefficient (O : Subring K) (a : O) :
    D.evaluation O n (AddMonoidAlgebra.single 0 (algebraMap O (FractionRing O) a)) = (a : K) := by
  simp [evaluation]

/-- Every finite formal endpoint evaluates to the original source endpoint. -/
theorem evaluation_endpoint (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) (j : ℕ) (hj : j ≤ n) :
    D.evaluation O n (endpointMonomial (algebraMap O (FractionRing O) π) D.exponent j) =
      (D.endpoint j : K) := by
  induction j with
  | zero =>
      simp only [endpointMonomial, Nat.not_lt_zero, ite_false]
      simp [evaluation, hπ, D.top]
  | succ j ih =>
      have hjn : j < n := by omega
      apply mul_right_cancel₀ (Subtype.coe_ne_coe.mpr (D.ratio_ne_zero j))
      calc
        _ = D.evaluation O n (endpointMonomial (algebraMap O (FractionRing O) π) D.exponent j) := by
          rw [endpointMonomial_step _ _ hjn, map_mul, D.evaluation_variable]
        _ = (D.endpoint j : K) := ih (by omega)
        _ = _ := congrArg R.subtype (D.step j)

variable {D}

/-- The finite formal first-dead quotient, written as the prescribed product
of coordinate generators over the original coefficient fraction field. -/
def FirstDead.formal (O : Subring K) (π : O) (h : D.FirstDead) (hn : h.length ≤ n) :
    Laurent (FractionRing O) n :=
  AddMonoidAlgebra.single 0
    ((algebraMap O (FractionRing O) π) ^ h.coefficientExponent /
      (algebraMap O (FractionRing O) π) ^ D.exponent) *
    ∏ i : Fin h.length, variableMonomial (⟨i.val, i.isLt.trans_le hn⟩ : Fin n) ^ (h.powers i + 1)

@[simp] theorem FirstDead.evaluation_formal (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) (h : D.FirstDead) (hn : h.length ≤ n) :
    D.evaluation O n (h.formal O π hn) = h.value := by
  simp only [FirstDead.formal, map_mul, map_prod, map_pow, D.evaluation_variable]
  simp [evaluation, hπ, FirstDead.value]

/-- The exact exponent vector of a first-dead quotient in a larger stage. -/
def FirstDead.formalExponent (h : D.FirstDead) (hn : h.length ≤ n) : Fin n → ℤ :=
  ∑ i : Fin h.length, (h.powers i + 1) • Pi.single (⟨i.val, i.isLt.trans_le hn⟩ : Fin n) 1

/-- The vector records μ_i+1 precisely below the first-dead level. -/
theorem FirstDead.formalExponent_apply (h : D.FirstDead) (hn : h.length ≤ n) (i : Fin n) :
    h.formalExponent hn i = if hi : i.val < h.length then (h.powers ⟨i.val, hi⟩ : ℤ) + 1 else 0 := by
  classical
  unfold FirstDead.formalExponent
  rw [Finset.sum_apply]
  by_cases hi : i.val < h.length
  · rw [dite_eq_left hi, Finset.sum_eq_single (⟨i.val, hi⟩ : Fin h.length)]
    · simp
    · intro j _ hj
      have hji : (⟨j.val, j.isLt.trans_le hn⟩ : Fin n) ≠ i := by
        intro he
        apply hj
        exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
      simp [hji]
    · simp
  · rw [dite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j _
    have hji : (⟨j.val, j.isLt.trans_le hn⟩ : Fin n) ≠ i := by
      intro he
      exact hi ((congrArg (fun x : Fin n => x.val) he) ▸ j.isLt)
    simp [hji]

/-- The prescribed product is exactly one Laurent monomial with its original
coefficient. This is an algebraic equality before evaluation. -/
theorem FirstDead.formal_eq_single (O : Subring K) (π : O)
    (h : D.FirstDead) (hn : h.length ≤ n) :
    h.formal O π hn = AddMonoidAlgebra.single (h.formalExponent hn)
      ((algebraMap O (FractionRing O) π) ^ h.coefficientExponent /
        (algebraMap O (FractionRing O) π) ^ D.exponent) := by
  simp only [FirstDead.formal, variableMonomial, AddMonoidAlgebra.single_pow,
    one_pow, AddMonoidAlgebra.prod_single, Finset.prod_const_one,
    AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  rfl

variable (D)

/-- The actual finite source-generator list: original DVR coefficients,
coordinates, endpoints, and first-dead quotients. -/
inductive FormalGenerator (O : Subring K) (π : O) (n : ℕ) :
    Laurent (FractionRing O) n → Prop
  | coefficient (a : O) : FormalGenerator O π n
      (AddMonoidAlgebra.single 0 (algebraMap O (FractionRing O) a))
  | coordinate (i : Fin n) : FormalGenerator O π n (variableMonomial i)
  | endpoint (j : ℕ) (hj : j ≤ n) : FormalGenerator O π n
      (endpointMonomial (algebraMap O (FractionRing O) π) D.exponent j)
  | firstDead (h : D.FirstDead) (hn : h.length ≤ n) : FormalGenerator O π n (h.formal O π hn)

/-- E_n is a concrete subring of the finite Laurent algebra. -/
def formalRing (O : Subring K) (π : O) (n : ℕ) : Subring (Laurent (FractionRing O) n) :=
  Subring.closure {f | D.FormalGenerator O π n f}

/-- Evaluation of E_n is exactly the n-th source-generator stage. -/
theorem formalRing_map_evaluation (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) (n : ℕ) :
    (D.formalRing O π n).map (D.evaluation O n) = generatedOver O (D.generatorsAt n) := by
  apply le_antisymm
  · rw [formalRing, RingHom.map_closure]
    apply Subring.closure_le.mpr
    rintro x ⟨f, hf, rfl⟩
    cases hf with
    | coefficient a =>
        rw [D.evaluation_coefficient]
        exact coefficient_le_generatedOver O _ a.property
    | coordinate i =>
        rw [D.evaluation_variable]
        exact generators_subset_generatedOver O _ (Or.inl (Or.inr ⟨i.val, i.isLt, rfl⟩))
    | endpoint j hj =>
        rw [D.evaluation_endpoint O π hπ j hj]
        exact generators_subset_generatedOver O _ (Or.inl (Or.inl ⟨j, hj, rfl⟩))
    | firstDead h hn =>
        rw [FirstDead.evaluation_formal O π hπ h hn]
        exact generators_subset_generatedOver O _ (Or.inr ⟨h, hn, rfl⟩)
  · apply generatedOver_le
    · intro a ha
      exact ⟨_, Subring.subset_closure (FormalGenerator.coefficient ⟨a, ha⟩),
        D.evaluation_coefficient O ⟨a, ha⟩⟩
    · rintro x ((⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨h, hn, rfl⟩)
      · exact ⟨_, Subring.subset_closure (FormalGenerator.endpoint j hj),
          D.evaluation_endpoint O π hπ j hj⟩
      · exact ⟨_, Subring.subset_closure (FormalGenerator.coordinate ⟨i, hi⟩),
          D.evaluation_variable O ⟨i, hi⟩⟩
      · exact ⟨_, Subring.subset_closure (FormalGenerator.firstDead h hn),
          FirstDead.evaluation_formal O π hπ h hn⟩

/-- Every actual source-ring element has a finite formal lift over the original
coefficient fraction field, with exact evaluation. -/
theorem exists_formal_lift (O : Subring K) (π : O)
    (hπ : (π : K) = (D.uniformizer : K)) {x : K} (hx : x ∈ D.sourceRing O) :
    ∃ n : ℕ, ∃ f : Laurent (FractionRing O) n,
      f ∈ D.formalRing O π n ∧ D.evaluation O n f = x := by
  obtain ⟨n, hn⟩ := (D.mem_sourceRing_iff_finite_stage O x).mp hx
  rw [← D.formalRing_map_evaluation O π hπ n] at hn
  obtain ⟨f, hf, he⟩ := hn
  exact ⟨n, f, hf, he⟩

end SourceBlockData
end HereditaryAtomicity.DVRBase
