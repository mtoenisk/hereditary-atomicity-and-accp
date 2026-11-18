import HereditaryAtomicity.DVRBase.ModelMembership
import HereditaryAtomicity.DVRBase.KernelNumerics

/-!
# The literal kernel-error ideal

The evaluation kernel is tested against the additive image Z₁J₀. Its support
description and the numerical quotient test come from division by the Laurent monomial
Z₁Z_N.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}

/-- The actual additive image Z₁J₀ in the ambient Laurent algebra. -/
def modelKernelJunk (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n) :
    AddSubgroup (Laurent K n) :=
  (modelJunk v π P).map (AddMonoidHom.mulLeft (endpointMonomial π P.kappa 1))

@[simp] theorem mem_modelKernelJunk (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (f : Laurent K n) :
    f ∈ modelKernelJunk v π P ↔
      ∃ g ∈ modelJunk v π P, endpointMonomial π P.kappa 1 * g = f := Iff.rfl

/-- Flattening the two actual principal images gives Z₁Z_N R₀. -/
theorem mem_modelKernelJunk_iff_exists_ring (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (f : Laurent K n) :
    f ∈ modelKernelJunk v π P ↔ ∃ g ∈ modelRing v π P,
      (endpointMonomial π P.kappa 1 * terminalMonomial π P.kappa) * g = f := by
  constructor
  · rintro ⟨j, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, mul_assoc _ _ _⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨terminalMonomial π P.kappa * g, ⟨g, hg, rfl⟩, (mul_assoc _ _ _).symm⟩

theorem modelKernelJunk_le_modelJunk (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) : modelKernelJunk v π P ≤ modelJunk v π P := by
  rintro f ⟨g, hg, rfl⟩
  exact modelJunk_mul_left v π P
    (modelJunk_le_modelRing v π P (endpointMonomial_mem_modelJunk v π P 1)) hg

theorem modelKernelJunk_mul_left (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) {f g : Laurent K n}
    (hf : f ∈ modelRing v π P) (hg : g ∈ modelKernelJunk v π P) :
    f * g ∈ modelKernelJunk v π P := by
  obtain ⟨j, hj, rfl⟩ := hg
  refine ⟨f * j, modelJunk_mul_left v π P hf hj, ?_⟩
  change endpointMonomial π P.kappa 1 * (f * j) = f * (endpointMonomial π P.kappa 1 * j)
  ring

/-- The translated support class is derived from the two literal monomial images. -/
def kernelJunkClass (P : ModelParameters n) : MonomialClass n :=
  (P.ringClass.translate (fun _ => -1) P.kappa).translate
    (fun i => if i.val < 1 then -1 else 0) P.kappa

theorem modelKernelJunk_eq_supported (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n) :
    modelKernelJunk v π P = (kernelJunkClass P).supported v := by
  ext f
  rw [mem_modelKernelJunk]
  have horder : realValuationOrder v (π ^ P.kappa) = P.kappa := by
    simp [realValuationOrder_pow, hπ]
  have ht := MonomialClass.mem_translate_iff_exists v
    (P.ringClass.translate (fun _ => -1) P.kappa)
    (fun i => if i.val < 1 then -1 else 0) (pow_ne_zero P.kappa hπ0) f
  rw [horder] at ht
  simpa only [kernelJunkClass, modelJunk_eq_supported v π hπ0 hπ P, endpointMonomial] using ht.symm

/-- Membership in the exact kernel target can be checked on collected terms. -/
theorem mem_modelKernelJunk_iff_single (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (f : Laurent K n) :
    f ∈ modelKernelJunk v π P ↔
      ∀ β, AddMonoidAlgebra.single β (f.coeff β) ∈ modelKernelJunk v π P := by
  rw [modelKernelJunk_eq_supported v π hπ0 hπ P]
  exact MonomialClass.mem_supported_iff_single v _ f

/-- The two inverse endpoint exponent shifts are exactly the correction of X. -/
theorem kernelJunkClass_contains_iff (P : ModelParameters n) (β : Fin n → ℤ)
    (e : ℝ) (first : Fin n) (hfirst : first.val = 0) :
    (kernelJunkClass P).contains β e ↔
      MeetsLevel P.weights P.kappa P.thresholds (kernelCorrectionExponent β first)
        (e - 2 * P.kappa) := by
  classical
  simp only [kernelJunkClass, MonomialClass.translate_contains, ModelParameters.ringClass]
  change MeetsLevel P.weights P.kappa P.thresholds
    (-(fun _ : Fin n => (-1 : ℤ)) +
      (-(fun i : Fin n => if i.val < 1 then (-1 : ℤ) else 0) + β))
    ((e - (P.kappa : ℝ)) - (P.kappa : ℝ)) ↔
    MeetsLevel P.weights P.kappa P.thresholds (kernelCorrectionExponent β first)
      (e - 2 * (P.kappa : ℝ))
  have hexp : -(fun _ : Fin n => (-1 : ℤ)) +
      (-(fun i => if i.val < 1 then -1 else 0) + β) = kernelCorrectionExponent β first := by
    funext i
    have hzero : i.val < 1 ↔ i = first := by
      constructor
      · intro h
        exact Fin.ext (by omega)
      · rintro rfl
        omega
    simp only [kernelCorrectionExponent, Pi.add_apply, Pi.neg_apply, Pi.single_apply, hzero]
    split_ifs <;> ring
  rw [hexp, show (e - P.kappa) - P.kappa = e - 2 * P.kappa by ring]

/-- Exact Lemma 6.5(b) test for a nonzero monomial in the actual Z₁J₀ image. -/
theorem modelKernelJunk_single_iff (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0) (first : Fin n) (hfirst : first.val = 0) :
    AddMonoidAlgebra.single β c ∈ modelKernelJunk v π P ↔
      MeetsLevel P.weights P.kappa P.thresholds (kernelCorrectionExponent β first)
        (realValuationOrder v c - 2 * P.kappa) := by
  rw [modelKernelJunk_eq_supported v π hπ0 hπ P, MonomialClass.single_mem_supported,
    or_iff_right hc, kernelJunkClass_contains_iff P β _ first hfirst]

/-- The correction is a literal Laurent quotient by Z₁Z_N, with coefficient
c / π^(2κ), and multiplying back recovers the original monomial. -/
theorem kernelCorrection_quotient_mul (π : K) (hπ0 : π ≠ 0) (κ : ℕ)
    (β : Fin n → ℤ) (c : K) (first : Fin n) (hfirst : first.val = 0) :
    (endpointMonomial π κ 1 * terminalMonomial π κ) *
        AddMonoidAlgebra.single (kernelCorrectionExponent β first) (c / π ^ (2 * κ)) =
      AddMonoidAlgebra.single β c := by
  classical
  have hexp : (fun i : Fin n => if i.val < 1 then (-1 : ℤ) else 0) + (fun _ => -1) +
      kernelCorrectionExponent β first = β := by
    funext i
    have hzero : i.val < 1 ↔ i = first := by
      constructor
      · intro h
        exact Fin.ext (by omega)
      · rintro rfl
        omega
    simp only [kernelCorrectionExponent, Pi.add_apply, Pi.single_apply, hzero]
    split_ifs <;> ring
  have hcoeff : π ^ κ * π ^ κ * (c / π ^ (2 * κ)) = c := by
    rw [show 2 * κ = κ + κ by omega, pow_add]
    field_simp
  simp only [endpointMonomial, terminalMonomial, AddMonoidAlgebra.single_mul_single, hexp, hcoeff]

/-- The numerical test is equivalent to actual quotient membership in R₀. -/
theorem modelKernelJunk_single_div_iff (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0) (first : Fin n) (hfirst : first.val = 0) :
    AddMonoidAlgebra.single β c ∈ modelKernelJunk v π P ↔
      AddMonoidAlgebra.single (kernelCorrectionExponent β first) (c / π ^ (2 * P.kappa)) ∈
        modelRing v π P := by
  rw [modelKernelJunk_single_iff v π hπ0 hπ P β c hc first hfirst,
    modelRing_single_iff v π hπ0 hπ P _ _ (div_ne_zero hc (pow_ne_zero _ hπ0))]
  simp only [realValuationOrder_div v hc (pow_ne_zero _ hπ0), realValuationOrder_pow, hπ,
    mul_one, Nat.cast_mul, Nat.cast_ofNat]

/-- The exact criterion of X implies membership in the literal target Z₁J₀. -/
theorem modelKernelJunk_single_of_criterion (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0) (first : Fin n) (hfirst : first.val = 0)
    {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (hcriterion : P.thresholds k + remainingValue P.weights P.kappa k +
      remainingValue P.weights P.kappa 1 ≤
      levelValue P.weights P.kappa (realValuationOrder v c) β k) :
    AddMonoidAlgebra.single β c ∈ modelKernelJunk v π P := by
  apply (modelKernelJunk_single_iff v π hπ0 hπ P β c hc first hfirst).mpr
  exact kernelCorrection_meetsLevel P.weights P.kappa (realValuationOrder v c)
    P.thresholds β first hfirst hk hkn (P.remaining_pos k hkn).le hcriterion

/-- Applying the criterion to each actual nonzero coefficient handles all
cancellations before the finite sum is assembled. -/
theorem modelKernelJunk_of_termwise_criterion (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (f : Laurent K n) (first : Fin n) (hfirst : first.val = 0)
    (h : ∀ β, f.coeff β ≠ 0 → ∃ k, 0 < k ∧ k ≤ n ∧
      P.thresholds k + remainingValue P.weights P.kappa k + remainingValue P.weights P.kappa 1 ≤
        levelValue P.weights P.kappa (realValuationOrder v (f.coeff β)) β k) :
    f ∈ modelKernelJunk v π P := by
  apply (mem_modelKernelJunk_iff_single v π hπ0 hπ P f).mpr
  intro β
  by_cases hβ : f.coeff β = 0
  · simpa only [hβ, AddMonoidAlgebra.single_zero] using (modelKernelJunk v π P).zero_mem
  · obtain ⟨k, hk, hkn, hcriterion⟩ := h β hβ
    exact modelKernelJunk_single_of_criterion v π hπ0 hπ P β _ hβ first hfirst hk hkn hcriterion

theorem modelKernelJunk_sum {ι : Type*} (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (s : Finset ι) (f : ι → Laurent K n)
    (hf : ∀ i ∈ s, f i ∈ modelKernelJunk v π P) :
    ∑ i ∈ s, f i ∈ modelKernelJunk v π P := (modelKernelJunk v π P).sum_mem hf

end HereditaryAtomicity.DVRBase
