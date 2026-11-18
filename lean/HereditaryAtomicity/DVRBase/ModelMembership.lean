import HereditaryAtomicity.DVRBase.Model

/-!
# The principal model ideal and polynomial-plus-ideal subring

The ideal J₀ is defined as the actual image ZₙR₀ in the ambient Laurent ring.
The coefficient-support characterization is derived from that definition.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

open scoped BigOperators NNReal

variable {K : Type*} [Field K] {n : ℕ}

/-- The actual additive image ZₙR₀ in the ambient Laurent algebra. -/
def modelJunk (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n) :
    AddSubgroup (Laurent K n) :=
  (modelRing v π P).toAddSubgroup.map (AddMonoidHom.mulLeft (terminalMonomial π P.kappa))

@[simp] theorem mem_modelJunk (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    (f : Laurent K n) :
    f ∈ modelJunk v π P ↔ ∃ g ∈ modelRing v π P, terminalMonomial π P.kappa * g = f := Iff.rfl

theorem modelJunk_le_modelRing (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n) :
    modelJunk v π P ≤ (modelRing v π P).toAddSubgroup := by
  rintro f ⟨g, hg, rfl⟩
  exact (modelRing v π P).mul_mem (modelRing_terminal v π P) hg

theorem modelJunk_mul_left (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n)
    {f g : Laurent K n} (hf : f ∈ modelRing v π P) (hg : g ∈ modelJunk v π P) :
    f * g ∈ modelJunk v π P := by
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨f * h, (modelRing v π P).mul_mem hf hh, ?_⟩
  change terminalMonomial π P.kappa * (f * h) = f * (terminalMonomial π P.kappa * h)
  ring

/-- The actual ideal of R₀ whose ambient image is J₀. -/
def modelJunkIdeal (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n) :
    Ideal (modelRing v π P) where
  carrier := {f | f.val ∈ modelJunk v π P}
  zero_mem' := (modelJunk v π P).zero_mem
  add_mem' := (modelJunk v π P).add_mem
  smul_mem' a _b hb := modelJunk_mul_left v π P a.property hb

theorem modelJunkIdeal_eq_span (v : Valuation K ℝ≥0) (π : K) (P : ModelParameters n) :
    modelJunkIdeal v π P = Ideal.span
      { (⟨terminalMonomial π P.kappa, modelRing_terminal v π P⟩ : modelRing v π P) } := by
  ext f
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, hg, he⟩
    exact ⟨⟨g, hg⟩, Subtype.ext he.symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g.val, g.property, congrArg Subtype.val hg.symm⟩

/-- Lemma 6.6(a): the principal image ideal has the translated termwise support. -/
theorem modelJunk_eq_supported (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n) :
    modelJunk v π P =
      (P.ringClass.translate (fun _ => -1) P.kappa).supported v := by
  ext f
  rw [mem_modelJunk]
  have horder : realValuationOrder v (π ^ P.kappa) = P.kappa := by
    simp [realValuationOrder_pow, hπ]
  rw [← horder, MonomialClass.mem_translate_iff_exists v P.ringClass _ (pow_ne_zero _ hπ0)]
  simp only [modelRing_eq_supported v π hπ0 hπ P, MonomialClass.mem_supportedSubring,
    terminalMonomial]

theorem modelJunk_single_iff (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0) :
    AddMonoidAlgebra.single β c ∈ modelJunk v π P ↔
      MeetsLevel P.weights P.kappa P.thresholds (fun i => β i + 1)
        (realValuationOrder v c - P.kappa) := by
  rw [modelJunk_eq_supported v π hπ0 hπ P, MonomialClass.single_mem_supported,
    or_iff_right hc]
  change MeetsLevel P.weights P.kappa P.thresholds (-(fun _ => -1) + β)
      (realValuationOrder v c - P.kappa) ↔ _
  have he : -(fun _ : Fin n => (-1 : ℤ)) + β = (fun i => β i + 1) := by
    funext i
    simp [add_comm]
  rw [he]

/-- Membership in J₀ is termwise after the exact endpoint quotient shift. -/
theorem modelJunk_term_meetsLevel (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    {f : Laurent K n} (hf : f ∈ modelJunk v π P)
    (β : Fin n → ℤ) (hβ : f.coeff β ≠ 0) :
    MeetsLevel P.weights P.kappa P.thresholds (fun i => β i + 1)
      (realValuationOrder v (f.coeff β) - P.kappa) := by
  rw [modelJunk_eq_supported v π hπ0 hπ P] at hf
  have hs := (MonomialClass.mem_supported_iff_single v
    (P.ringClass.translate (fun _ => -1) P.kappa) f).mp hf β
  rw [← modelJunk_eq_supported v π hπ0 hπ P] at hs
  exact (modelJunk_single_iff v π hπ0 hπ P β _ hβ).mp hs

/-- Every nonzero term of J₀ has order at least the positive endpoint order. -/
theorem modelJunk_termOrder_lower (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    {f : Laurent K n} (hf : f ∈ modelJunk v π P)
    (β : Fin n → ℤ) (hβ : f.coeff β ≠ 0) :
    remainingValue P.weights P.kappa n ≤ termOrder v P.weights β (f.coeff β) := by
  have h := (modelJunk_term_meetsLevel v π hπ0 hπ P hf β hβ).nonneg_total
    (fun i => (P.weights_pos i).le) (fun k hk => (P.remaining_pos k hk).le) P.threshold_nonneg
  rw [totalOrder_endpoint_quotient] at h
  exact sub_nonneg.mp h

theorem modelJunk_termOrder_pos (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    {f : Laurent K n} (hf : f ∈ modelJunk v π P)
    (β : Fin n → ℤ) (hβ : f.coeff β ≠ 0) :
    0 < termOrder v P.weights β (f.coeff β) :=
  (P.remaining_pos n le_rfl).trans_le (modelJunk_termOrder_lower v π hπ0 hπ P hf β hβ)

/-- Lemma 6.6(b): for a nonnegative exponent, membership in the actual ideal is
equivalent to crossing one of the dead-monomial thresholds. -/
theorem modelJunk_single_dead_iff (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (hβ : ∀ i, 0 ≤ β i) (c : K) (hc : c ≠ 0) :
    AddMonoidAlgebra.single β c ∈ modelJunk v π P ↔
      ∃ k ≤ n, P.thresholds k + remainingValue P.weights P.kappa k ≤
        partialValue P.weights (realValuationOrder v c) β k := by
  rw [modelJunk_single_iff v π hπ0 hπ P β c hc,
    meetsLevel_endpoint_quotient_iff P.weights P.kappa (realValuationOrder v c) P.thresholds β hβ]

/-- Lemma 6.6(d): low-order ideal monomials have coefficient order at least κ. -/
theorem modelJunk_low_coefficient (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0)
    (hmem : AddMonoidAlgebra.single β c ∈ modelJunk v π P)
    (hsmall : termOrder v P.weights β c < 2 * (P.kappa : ℝ)) :
    (P.kappa : ℝ) ≤ realValuationOrder v c :=
  endpoint_coefficient_ge_anchor (fun i => (P.weights_pos i).le)
    (fun k hk => (P.remaining_pos k hk).le) (Nat.cast_nonneg _)
    P.threshold_zero P.threshold_large β
    ((modelJunk_single_iff v π hπ0 hπ P β c hc).mp hmem) hsmall

/-- Equality in the low-order coefficient bound makes the endpoint quotient
an ordinary nonnegative monomial. -/
theorem modelJunk_low_exponent (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0)
    (hmem : AddMonoidAlgebra.single β c ∈ modelJunk v π P)
    (he : realValuationOrder v c = P.kappa)
    (hsmall : termOrder v P.weights β c < 2 * (P.kappa : ℝ)) :
    ∀ i, 0 ≤ β i + 1 := by
  have hm := (modelJunk_single_iff v π hπ0 hπ P β c hc).mp hmem
  rw [he, sub_self] at hm
  apply endpoint_exponent_nonneg_of_coefficient_eq_anchor
    (fun i => (P.weights_pos i).le) (fun k hk => (P.remaining_pos k hk).le)
    (by exact_mod_cast P.kappa_pos) P.threshold_zero P.threshold_large β hm
  simpa [termOrder, he] using hsmall

/-- The endpoint Zₖ, with inverse variables only before the cut. -/
def endpointMonomial (π : K) (κ : ℕ) (k : ℕ) : Laurent K n :=
  AddMonoidAlgebra.single (fun i => if i.val < k then -1 else 0) (π ^ κ)

/-- Every finite endpoint is an actual multiple of Zₙ inside R₀. -/
theorem endpointMonomial_mem_modelJunk (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (k : ℕ) : endpointMonomial π P.kappa k ∈ modelJunk v π P := by
  classical
  let β : Fin n → ℤ := fun i => if i.val < k then 0 else 1
  have hβ : ∀ i, 0 ≤ β i := by intro i; dsimp [β]; split_ifs <;> norm_num
  refine ⟨AddMonoidAlgebra.single β 1, modelRing_nonneg_monomial v π P β hβ 1 (by simp), ?_⟩
  change terminalMonomial π P.kappa * AddMonoidAlgebra.single β 1 = endpointMonomial π P.kappa k
  simp only [terminalMonomial, endpointMonomial, AddMonoidAlgebra.single_mul_single, mul_one]
  congr 1
  funext i
  simp only [Pi.add_apply, β]
  split_ifs <;> norm_num

theorem endpointMonomial_mul_mem_modelJunk (v : Valuation K ℝ≥0) (π : K)
    (P : ModelParameters n) (k : ℕ) {f : Laurent K n} (hf : f ∈ modelRing v π P) :
    endpointMonomial π P.kappa k * f ∈ modelJunk v π P := by
  rw [mul_comm]
  exact modelJunk_mul_left v π P hf (endpointMonomial_mem_modelJunk v π P k)

/-- Actual division by the terminal monomial realizes the numerical shift. -/
theorem modelJunk_single_div_iff (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0) :
    AddMonoidAlgebra.single β c ∈ modelJunk v π P ↔
      AddMonoidAlgebra.single (fun i => β i + 1) (c / π ^ P.kappa) ∈ modelRing v π P := by
  rw [modelJunk_single_iff v π hπ0 hπ P β c hc,
    modelRing_single_iff v π hπ0 hπ P _ _ (div_ne_zero hc (pow_ne_zero _ hπ0))]
  simp [realValuationOrder_div v hc (pow_ne_zero _ hπ0), realValuationOrder_pow, hπ]

/-- The equality case of Lemma 6.6(d), as a literal monomial factorization. -/
theorem modelJunk_low_shape (v : Valuation K ℝ≥0) (π : K)
    (hπ0 : π ≠ 0) (hπ : realValuationOrder v π = 1) (P : ModelParameters n)
    (β : Fin n → ℤ) (c : K) (hc : c ≠ 0)
    (hmem : AddMonoidAlgebra.single β c ∈ modelJunk v π P)
    (he : realValuationOrder v c = P.kappa)
    (hsmall : termOrder v P.weights β c < 2 * (P.kappa : ℝ)) :
    ∃ d : K, d ≠ 0 ∧ realValuationOrder v d = 0 ∧
      ∃ γ : Fin n → ℤ, (∀ i, 0 ≤ γ i) ∧
        AddMonoidAlgebra.single β c =
          AddMonoidAlgebra.single 0 d * terminalMonomial π P.kappa *
            AddMonoidAlgebra.single γ 1 := by
  refine ⟨c / π ^ P.kappa, div_ne_zero hc (pow_ne_zero _ hπ0), ?_,
    (fun i => β i + 1), modelJunk_low_exponent v π hπ0 hπ P β c hc hmem he hsmall, ?_⟩
  · simp [realValuationOrder_div v hc (pow_ne_zero _ hπ0), realValuationOrder_pow, hπ, he]
  · simp only [terminalMonomial, AddMonoidAlgebra.single_mul_single, zero_add,
      div_mul_cancel₀ _ (pow_ne_zero _ hπ0), mul_one]
    congr 1
    funext i
    simp

end HereditaryAtomicity.DVRBase
