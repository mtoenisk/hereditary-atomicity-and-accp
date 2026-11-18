import HereditaryAtomicity.DVRBase.ModelProductShape
import HereditaryAtomicity.DVRBase.ModelNearJunk
import HereditaryAtomicity.DVRBase.ModelDecomposition
import HereditaryAtomicity.DVRBase.GeometricMatching
import HereditaryAtomicity.DVRBase.ModelObstructionFinal

/-!
# The finite factorization obstruction

In the generator-defined finite model, divide the part of the exceptional factor
outside the distinguished ideal by the endpoint monomial. Matching its least terms
against the selected terms contradicts the finite-order bound, giving semilocal
Theorem 6.9.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}

/-- The actual Laurent inverse of the final endpoint monomial. -/
def terminalInverse (π : K) (κ : ℕ) : Laurent K n :=
  AddMonoidAlgebra.single (fun _ => 1) (π ^ κ)⁻¹

@[simp] theorem terminalMonomial_mul_terminalInverse (π : K) (κ : ℕ) (hπ0 : π ≠ 0) :
    terminalMonomial π κ * (terminalInverse π κ : Laurent K n) = 1 := by
  have he : (fun _ : Fin n => (-1 : ℤ)) + (fun _ => 1) = 0 := by ext; simp
  simp only [terminalMonomial, terminalInverse, AddMonoidAlgebra.single_mul_single,
    he, mul_inv_cancel₀ (pow_ne_zero κ hπ0)]
  rfl

@[simp] theorem terminalInverse_mul_terminalMonomial (π : K) (κ : ℕ) (hπ0 : π ≠ 0) :
    (terminalInverse π κ : Laurent K n) * terminalMonomial π κ = 1 := by
  rw [mul_comm, terminalMonomial_mul_terminalInverse π κ hπ0]

@[simp] theorem maskMonomial_mul_inverse (L : Finset (Fin n)) :
    (maskMonomial L : Laurent K n) * AddMonoidAlgebra.single (-maskExponent L) 1 = 1 := by
  simp only [maskMonomial, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
  rfl

/-- Removing terms preserves membership after multiplication by any monomial. -/
theorem single_mul_outsideTerms_mem_supported (v : Valuation K ℝ≥0)
    (M N : MonomialClass n) (β : Fin n → ℤ) {c : K} (hc : c ≠ 0)
    {f : Laurent K n} (hf : AddMonoidAlgebra.single β c * f ∈ N.supported v) :
    AddMonoidAlgebra.single β c * outsideTerms v M f ∈ N.supported v := by
  rw [single_mul_mem_supported_iff v N β hc] at hf ⊢
  exact outsideTerms_mem_supported v M _ hf

/-- Dividing an actual nonjunk part by Zₙ leaves every term outside R₀. -/
theorem terminalInverse_nonjunk_terms (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (f : Laurent K n) (γ : Fin n → ℤ)
    (hγ : (terminalInverse π P.kappa * nonjunkPart v P f).coeff γ ≠ 0) :
    ¬ P.ringClass.contains γ
      (realValuationOrder v ((terminalInverse π P.kappa * nonjunkPart v P f).coeff γ)) := by
  let a := nonjunkPart v P f
  let β : Fin n → ℤ := -(fun _ => 1) + γ
  have hcoeff : (terminalInverse π P.kappa * a).coeff γ = (π ^ P.kappa)⁻¹ * a.coeff β := by
    simp [terminalInverse, AddMonoidAlgebra.coeff_single_mul_apply, β]
  have ha : a.coeff β ≠ 0 := by
    intro hz
    change (terminalInverse π P.kappa * a).coeff γ ≠ 0 at hγ
    simp [hcoeff, hz] at hγ
  have hnot := nonjunkPart_term_not_mem_junk v π hπ0 hπ P f β ha
  intro hm
  have hsingle : AddMonoidAlgebra.single γ
      ((terminalInverse π P.kappa * a).coeff γ) ∈ modelRing v π P := by
    exact (modelRing_single_iff v π hπ0 hπ P γ _ hγ).mpr hm
  have hz : terminalMonomial π P.kappa ∈ modelJunk v π P :=
    (mem_modelJunk v π P _).mpr ⟨1, (modelRing v π P).one_mem, by simp⟩
  have hprod := modelJunk_mul_left v π P hsingle hz
  apply hnot
  change AddMonoidAlgebra.single β (a.coeff β) ∈ modelJunk v π P
  convert hprod using 1
  rw [terminalMonomial, AddMonoidAlgebra.single_mul_single, hcoeff]
  have he : γ + (fun _ : Fin n => (-1 : ℤ)) = β := by ext; simp [β]; ring
  rw [he]
  congr 1
  field_simp

/-- The literal quotient and normalized complement satisfy the finite
geometric equation used in F, Step 2. -/
theorem modelProduct_geometric_equation (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (P : ModelParameters n) (Λ : Finset (Fin n))
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → Laurent K n}
    (H : ModelProductShape v π P Λ s f) (a ρ j : Laurent K n)
    (hA : AddMonoidAlgebra.single 0 H.coefficient * f H.exceptional =
      a + terminalMonomial π P.kappa * ρ)
    (hprod : (∏ i ∈ s, f i) = endpointMonomial π P.kappa 1 * (1 + j)) :
    (terminalInverse π P.kappa * a + ρ) * (1 - H.error) =
      maskMonomial H.right * (1 + j) := by
  let Z : Laurent K n := terminalMonomial π P.kappa
  let Y : Laurent K n := maskMonomial H.left
  have hZi : Z * terminalInverse π P.kappa = 1 :=
    terminalMonomial_mul_terminalInverse π P.kappa hπ0
  have hYi : Y * AddMonoidAlgebra.single (-maskExponent H.left) 1 = 1 :=
    maskMonomial_mul_inverse H.left
  have hnorm : Y * (1 - H.error) = H.normalized := by
    have h := H.shifted_error_eq
    change Y * H.error = Y - H.normalized at h
    linear_combination -h
  have hpart : Z * Y * maskMonomial H.right = endpointMonomial π P.kappa 1 := by
    have h := endpointMonomial_partition π P.kappa H.left H.right H.disjoint H.partition
    have hz : endpointMonomial π P.kappa n = (terminalMonomial π P.kappa : Laurent K n) := by
      simp [endpointMonomial, terminalMonomial]
    simpa only [hz, maskMonomial, Z, Y] using h
  have he : Z * Y * ((terminalInverse π P.kappa * a + ρ) * (1 - H.error)) =
      Z * Y * (maskMonomial H.right * (1 + j)) := by
    calc
      _ = (a + Z * ρ) * (Y * (1 - H.error)) := by
        calc
          _ = (Z * terminalInverse π P.kappa * a + Z * ρ) * (Y * (1 - H.error)) := by ring
          _ = _ := by rw [hZi, one_mul]
      _ = (AddMonoidAlgebra.single 0 H.coefficient * f H.exceptional) * H.normalized := by
        rw [hnorm, ← hA]
      _ = ∏ i ∈ s, f i := H.product_eq
      _ = _ := by rw [hprod, ← hpart]; ring
  let I := terminalInverse π P.kappa * AddMonoidAlgebra.single (-maskExponent H.left) 1
  have hI : I * (Z * Y) = 1 := by
    calc
      _ = (Z * terminalInverse π P.kappa) *
          (Y * AddMonoidAlgebra.single (-maskExponent H.left) 1) := by dsimp [I]; ring
      _ = 1 := by rw [hZi, hYi, one_mul]
  have h := congrArg (fun x => I * x) he
  simpa only [← mul_assoc, hI, one_mul] using h

/-- The bad terms selected outside U₀ remain outside R₀ after multiplication
by Y_D, using the disjoint-mask implication of Lemma 6.8(b). -/
theorem mask_mul_outside_near_terms (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (Λ L D : Finset (Fin n)) (hLD : Disjoint L D) (hn : 0 < n)
    (hL0 : (⟨0, hn⟩ : Fin n) ∉ L) (hD0 : (⟨0, hn⟩ : Fin n) ∉ D)
    (d : Laurent K n) (hLd : maskMonomial L * d ∈ modelSourceRing v π P Λ)
    (γ : Fin n → ℤ)
    (hγ : (maskMonomial D * outsideTerms v (P.nearClass (maskExponent D) 0) d).coeff γ ≠ 0) :
    ¬ P.ringClass.contains γ
      (realValuationOrder v ((maskMonomial D *
        outsideTerms v (P.nearClass (maskExponent D) 0) d).coeff γ)) := by
  let b := outsideTerms v (P.nearClass (maskExponent D) 0) d
  let δ := -maskExponent D + γ
  have hcoeff : (maskMonomial D * b).coeff γ = b.coeff δ := by
    simp [maskMonomial, AddMonoidAlgebra.coeff_single_mul_apply, δ]
  have hb : b.coeff δ ≠ 0 := by
    change (maskMonomial D * b).coeff γ ≠ 0 at hγ
    rwa [hcoeff] at hγ
  have hLb : maskMonomial L * b ∈ modelSourceRing v π P Λ := by
    change maskMonomial L * b ∈ (modelSourceRing v π P Λ).toAddSubgroup
    rw [modelSourceRing_eq_supported v π hπ0 hπ P Λ]
    apply single_mul_outsideTerms_mem_supported v _ _ _ one_ne_zero
    rw [← modelSourceRing_eq_supported v π hπ0 hπ P Λ]
    exact hLd
  have hLterm : maskMonomial L * AddMonoidAlgebra.single δ (b.coeff δ) ∈ modelRing v π P := by
    have hh := modelSourceRing_le_modelRing v π P Λ hLb
    have hs := modelRing_le_supported v π hπ P hh
    have ht := (MonomialClass.mem_supported_iff_single v P.ringClass _).mp hs
      (maskExponent L + δ)
    have he : AddMonoidAlgebra.single (maskExponent L + δ)
        ((maskMonomial L * b).coeff (maskExponent L + δ)) =
        maskMonomial L * AddMonoidAlgebra.single δ (b.coeff δ) := by
      simp [maskMonomial, AddMonoidAlgebra.single_mul_single]
    rw [he] at ht
    rw [modelRing_eq_supported v π hπ0 hπ P, MonomialClass.mem_supportedSubring]
    exact ht
  intro hm
  have hDterm : maskMonomial D * AddMonoidAlgebra.single δ (b.coeff δ) ∈ modelRing v π P := by
    have hδ : maskExponent D + δ = γ := by dsimp [δ]; abel
    have hm' : P.ringClass.contains γ (realValuationOrder v (b.coeff δ)) := by
      change P.ringClass.contains γ (realValuationOrder v ((maskMonomial D * b).coeff γ)) at hm
      rwa [hcoeff] at hm
    simpa [maskMonomial, AddMonoidAlgebra.single_mul_single, hδ] using
      (modelRing_single_iff v π hπ0 hπ P γ (b.coeff δ) hb).mpr hm'
  have hu := modelNearJunk_of_disjoint_masks v π hπ0 hπ P L D hLD hn hL0 hD0 hLterm hDterm
  have hclass := (modelNearJunk_single_iff v π hπ0 hπ P D δ (b.coeff δ)).mp hu
  exact outsideTerms_term_not_mem v _ d δ hb (hclass.resolve_left hb)

end HereditaryAtomicity.DVRBase

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K] {n : ℕ}

/-- A product of factors outside the model ideal cannot equal Z₁ times one plus a member
of that ideal, in the sense of Z₁(1+h). The assertion also holds for an empty family
of factors. -/
theorem model_factorization_obstruction (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (hn : 0 < n) (Λ : Finset (Fin n))
    (hΛ : 2 * ∑ l ∈ Λ.filter (fun l => 0 < l.val), P.weights l ≤
      remainingValue P.weights P.kappa 1)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Laurent K n)
    (hf : ∀ i ∈ s, f i ∈ modelSourceRing v π P Λ)
    (hnj : ∀ i ∈ s, f i ∉ modelJunk v π P)
    {j' : Laurent K n} (hj' : j' ∈ modelJunk v π P) :
    (∏ i ∈ s, f i) ≠ endpointMonomial π P.kappa 1 * (1 + j') := by
  intro hprod
  obtain ⟨H⟩ := modelProduct_shape v π hπ0 hπ P hn Λ s f hf hj' hprod
  let A := AddMonoidAlgebra.single 0 H.coefficient * f H.exceptional
  let a := nonjunkPart v P A
  let ψ := terminalInverse π P.kappa * a
  let M := P.nearClass (maskExponent H.right) 0
  let b := outsideTerms v M H.error
  let j := H.error - b
  have hAmem : A ∈ modelSourceRing v π P Λ :=
    H.scaled_exceptional_mem v π P Λ (hf H.exceptional H.exceptional_mem)
  have hAnj : A ∉ modelJunk v π P :=
    H.scaled_exceptional_not_junk v π P Λ (hnj H.exceptional H.exceptional_mem)
  have ha : a ∈ modelSourceRing v π P Λ :=
    nonjunkPart_mem_source v π hπ0 hπ P Λ hAmem
  have ha0 : a ≠ 0 := by
    intro hz
    exact hAnj ((nonjunkPart_eq_zero_iff v π hπ0 hπ P A).mp hz)
  have haeq : a = terminalMonomial π P.kappa * ψ := by
    dsimp only [ψ]
    rw [← mul_assoc, terminalMonomial_mul_terminalInverse π P.kappa hπ0, one_mul]
  have hψ : ψ ≠ 0 := by
    intro hz
    exact ha0 (by rw [haeq, hz, mul_zero])
  obtain ⟨ρ, hρ, hA⟩ := exists_modelRing_remainder v π hπ0 hπ P A
  have heq : (ψ + ρ) * (1 - H.error) = maskMonomial H.right * (1 + j') :=
    modelProduct_geometric_equation v π hπ0 P Λ H a ρ j' hA hprod
  have hU : j ∈ modelNearJunkRing v π hπ0 hπ P H.right := by
    change j ∈ (modelNearJunkRing v π hπ0 hπ P H.right).toAddSubgroup
    rw [modelNearJunkRing_eq_supported v π hπ0 hπ P H.right]
    exact sub_outsideTerms_mem v M H.error
  have hjbound : laurentGaussValue v P.weights j ≤ laurentGaussValue v P.weights H.error :=
    laurentGaussValue_sub_outsideTerms_le v P.weights M H.error
  have hdpos : laurentGaussValue v P.weights H.error < 1 := by
    have h := (laurentGaussValue_lt_exp_iff v P.weights H.error 0).mpr H.error_positive
    simpa using h
  have hjpos : laurentGaussValue v P.weights j' < 1 := by
    have h := (laurentGaussValue_lt_exp_iff v P.weights j' 0).mpr
      (fun β hβ => modelJunk_termOrder_pos v π hπ0 hπ P hj' β hβ)
    simpa using h
  have hR : (modelRing v π P).toAddSubgroup = P.ringClass.supported v := by
    rw [modelRing_eq_supported v π hπ0 hπ P]
    rfl
  have hL0 : (⟨0, hn⟩ : Fin n) ∉ H.left := by
    intro h
    have hh : (⟨0, hn⟩ : Fin n) ∈ H.left ∪ H.right := Finset.mem_union_left _ h
    rw [H.partition] at hh
    simp at hh
  have hD0 : (⟨0, hn⟩ : Fin n) ∉ H.right := by
    intro h
    have hh : (⟨0, hn⟩ : Fin n) ∈ H.left ∪ H.right := Finset.mem_union_right _ h
    rw [H.partition] at hh
    simp at hh
  have hLd : maskMonomial H.left * H.error ∈ modelSourceRing v π P Λ := H.shifted_error_mem
  have hψM : ∀ β, ψ.coeff β ≠ 0 →
      ¬ P.ringClass.contains β (realValuationOrder v (ψ.coeff β)) :=
    terminalInverse_nonjunk_terms v π hπ0 hπ P A
  have hbM : ∀ β, (maskMonomial H.right * b).coeff β ≠ 0 →
      ¬ P.ringClass.contains β (realValuationOrder v ((maskMonomial H.right * b).coeff β)) :=
    mask_mul_outside_near_terms v π hπ0 hπ P Λ H.left H.right H.disjoint hn hL0 hD0 H.error hLd
  obtain ⟨_, _, hmatch⟩ := geometric_same_least_terms v P.weights P.ringClass
    (modelRing v π P) (modelNearJunkRing v π hπ0 hπ P H.right) hR
    ψ ρ (maskMonomial H.right) j' H.error j b hψ hρ
    (maskMonomial_mem_modelRing v π P H.right) (modelJunk_le_modelRing v π P hj')
    (fun x hx => modelNearJunk_mul_mem_modelRing v π hπ0 hπ P H.right hx)
    hU (by dsimp only [j]; ring) hjbound hdpos hjpos heq hψM hbM
  have hLb : maskMonomial H.left * b ∈ modelSourceRing v π P Λ := by
    change maskMonomial H.left * b ∈ (modelSourceRing v π P Λ).toAddSubgroup
    rw [modelSourceRing_eq_supported v π hπ0 hπ P Λ]
    apply single_mul_outsideTerms_mem_supported v M _ _ one_ne_zero
    rw [← modelSourceRing_eq_supported v π hπ0 hπ P Λ]
    exact hLd
  exact model_obstruction_of_least_term_matching v π hπ0 hπ P hn Λ H.left H.right
    H.disjoint H.partition (H.left_weight_bound v π P Λ hΛ) a ψ b haeq hψ ha
    (nonjunkPart_term_not_mem_junk v π hπ0 hπ P A) hLb hmatch

end HereditaryAtomicity.DVRBase
