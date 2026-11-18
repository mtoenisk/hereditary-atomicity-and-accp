import HereditaryAtomicity.DVRBase.CanonicalCoefficientTransfer
import HereditaryAtomicity.DVRBase.IntersectionCertificate
import HereditaryAtomicity.DVRBase.SourceSupportSelection
import HereditaryAtomicity.DVRBase.UniformFamilyReturn

/-!
# Original-chain certificates for common support

The common source is the literal intersection of the selected maximal stalks.
Power scaling and radical ratio returns produce the source chain internally.
Canonical coefficient transfer then gives the literal intersection with the original domain.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K]

/-- The actual intersection of all specified maximal stalks. -/
abbrev commonSupportRing (D : Subring K) [IsFractionRing D K]
    (places : Set (MaximalSpectrum D)) : Subring K :=
  ⨅ Q : places, sourceMaximalStalk D Q.val

theorem source_le_commonSupportRing (D : Subring K) [IsFractionRing D K]
    (places : Set (MaximalSpectrum D)) : D ≤ commonSupportRing D places :=
  le_iInf fun Q => le_sourceMaximalStalk D Q.val

theorem commonSupportRing_le_stalk (D : Subring K) [IsFractionRing D K]
    (places : Set (MaximalSpectrum D)) (Q : MaximalSpectrum D) (hQ : Q ∈ places) :
    commonSupportRing D places ≤ sourceMaximalStalk D Q :=
  iInf_le (fun Q : places => sourceMaximalStalk D Q.val) ⟨Q, hQ⟩

/-- Power scaling plus radical returns constructs the exact uniformizer chain,
without locality, dimension or algebraicity assumptions. -/
theorem exists_uniformizerChainData_of_power_scaling
    {A : Type*} [CommRing A] [IsDomain A] (π : A) (hπ0 : π ≠ 0)
    (x t : ℕ → A) (hx : ∀ n, x n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (k : ℕ) (b : A) (hb : π ^ k = x 0 * b)
    (hr : ∀ n, ∃ e : ℕ, 0 < e ∧ π ∣ t n ^ e) :
    ∃ C : UniformizerChainData π t, C.exponent = k + 1 ∧
      ∀ n, C.endpoint n = π * b * x n := by
  have hb0 : b ≠ 0 := by
    intro hz
    exact pow_ne_zero k hπ0 (by simpa [hz] using hb)
  refine ⟨{
    exponent := k + 1
    exponent_pos := Nat.succ_pos k
    endpoint := fun n => π * b * x n
    endpoint_ne_zero := fun n => mul_ne_zero (mul_ne_zero hπ0 hb0) (hx n)
    top := by rw [pow_succ, hb]; ring
    step := fun n => by rw [hxt n]; ring
    ratio_power := ?_ }, rfl, fun _ => rfl⟩
  intro n
  obtain ⟨e, he, hdiv⟩ := hr n
  refine ⟨e * (k + 1), Nat.mul_pos he (Nat.succ_pos k), ?_⟩
  simpa only [pow_mul] using pow_dvd_pow_of_dvd hdiv (k + 1)

/-- A uniformizer-power top and original ratios supported on the selected
places force every endpoint back into the original source. -/
theorem UniformizerChainData.endpoints_mem_source_of_support
    (D A : Subring K) [IsFractionRing D K] (hDA : D ≤ A)
    (places : Set (MaximalSpectrum D))
    (hA : ∀ Q ∈ places, A ≤ sourceMaximalStalk D Q)
    (π : A) (t : ℕ → D)
    (C : UniformizerChainData π (fun n => Subring.inclusion hDA (t n)))
    (htopD : (π : K) ^ C.exponent ∈ D)
    (hsupport : ∀ n (Q : MaximalSpectrum D), t n ∈ Q.asIdeal → Q ∈ places) :
    ∀ n, (C.endpoint n : K) ∈ D := by
  intro n
  induction n with
  | zero => simpa only [C.top, Subring.coe_pow] using htopD
  | succ n ih =>
      have ht0 : (t n : K) ≠ 0 := by
        intro hz
        exact C.ratio_ne_zero n (Subtype.ext hz)
      have heq : (C.endpoint n : K) / (t n : K) = (C.endpoint (n + 1) : K) := by
        have he := congrArg A.subtype (C.step n)
        change (C.endpoint n : K) = (C.endpoint (n + 1) : K) * (t n : K) at he
        rw [he, mul_div_cancel_right₀ _ ht0]
      rw [← heq]
      apply source_div_mem_of_stalks_and_units D places ih (t n)
      · intro Q hQ
        rw [heq]
        exact hA Q hQ (C.endpoint (n + 1)).property
      · intro Q hQ
        exact (isUnit_sourceMaximalMap_iff D Q (t n)).mpr
          (fun hmem => hQ (hsupport n Q hmem))

/-- Coefficient transfer on common support from the original chain and its the uniformizer-scaling hypothesis scaling. All blocks,
completions, kernel control and source-intersection return are constructed. -/
theorem common_support_exists_shrunk_certificate_of_scaling
    (D B O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra.IsAlgebraic O K] (places : Set (MaximalSpectrum D))
    (hBO : B ≤ O) (hBA : B ≤ commonSupportRing D places)
    (π : B) (hπ : Irreducible (Subring.inclusion hBO π))
    (x t : ℕ → D) (hx : ∀ n, x n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n)
    (hsupport : ∀ n (Q : MaximalSpectrum D), t n ∈ Q.asIdeal → Q ∈ places)
    (k : ℕ) (b : commonSupportRing D places)
    (hb : (π : K) ^ k = (x 0 : K) * (b : K))
    (htopD : (π : K) ^ (k + 1) ∈ D)
    (hr : ∀ n, ∃ e : ℕ, 0 < e ∧
      (t n : K) ^ e / (π : K) ∈ commonSupportRing D places)
    (w : Valuation K ℝ≥0) (hO : ∀ a : O, w (a : K) ≤ 1)
    (hA : ∀ a : commonSupportRing D places, w (a : K) ≤ 1)
    (hnorm : realValuationOrder w (π : K) = 1)
    (hAF : UniformizerDivisionClosed B π w)
    (htpos : ∀ n, 0 < realValuationOrder w (t n : K)) :
    ∃ (F : SourceBlockData (commonSupportRing D places)) (a l : ℕ → ℕ),
      (F.uniformizer : K) = (π : K) ∧ F.exponent = k + 1 ∧ F.valuation = w ∧
      StrictMono a ∧ a 0 = 0 ∧ (∀ n, a (n + 1) = a n + l n + 1) ∧
      (∀ n, (F.endpoint n : K) = (π : K) * (b : K) * (x (a n) : K)) ∧
      (∀ n, (F.endpoint n : K) ∈ D) ∧
      (∀ n, (F.ratio n : K) = ((sourceBlock t (a n) (l n) : D) : K)) ∧
      ∀ Λ : Set ℕ, F.AdmissibleTail Λ →
        F.NoOutsideJunkFactorization B Λ ∧
        F.sourceSubring B Λ ≤ commonSupportRing D places ∧
        F.IntersectionCertificate D B Λ := by
  let A := commonSupportRing D places
  let hDA : D ≤ A := source_le_commonSupportRing D places
  let πA : A := Subring.inclusion hBA π
  let xA : ℕ → A := fun n => Subring.inclusion hDA (x n)
  let tA : ℕ → A := fun n => Subring.inclusion hDA (t n)
  have hπK : (π : K) ≠ 0 := by
    intro hz
    exact hπ.ne_zero (Subtype.ext hz)
  have hπA : πA ≠ 0 := fun hz => hπK (congrArg A.subtype hz)
  have hrA : ∀ n, ∃ e : ℕ, 0 < e ∧ πA ∣ tA n ^ e := by
    intro n
    obtain ⟨e, he, hmem⟩ := hr n
    exact ⟨e, he, ⟨⟨(t n : K) ^ e / (π : K), hmem⟩,
      Subtype.ext (by change (t n : K) ^ e = (π : K) * ((t n : K) ^ e / (π : K)); field_simp)⟩⟩
  obtain ⟨C, hCexp, hCc⟩ := exists_uniformizerChainData_of_power_scaling πA hπA xA tA
    (fun n hz => hx n (Subtype.ext (congrArg A.subtype hz)))
    (fun n => Subtype.ext (congrArg D.subtype (hxt n))) k b (Subtype.ext hb) hrA
  have hcval : ∀ n, 1 ≤ realValuationOrder w (C.endpoint n : K) :=
    C.one_le_endpoint_order (fun n => ⟨b * xA n, by rw [hCc n]; ring⟩)
      A.subtype Subtype.val_injective w hA hnorm
  have hcD : ∀ n, (C.endpoint n : K) ∈ D :=
    C.endpoints_mem_source_of_support D A hDA places (commonSupportRing_le_stalk D places)
      πA t (by rw [hCexp]; exact htopD) hsupport
  obtain ⟨F, a, l, hFπ, hFexp, hFw, ha, ha0, hasucc, hFc, hFt, hcert⟩ :=
    C.exists_completed_shrunk_source_certificate B O A hBO hBA π hπ w hO hnorm hAF htpos hcval
  have hrati (n : ℕ) : (F.ratio n : K) = ((sourceBlock t (a n) (l n) : D) : K) := by
    rw [hFt n]
    simp only [sourceBlock, SubmonoidClass.coe_finsetProd, tA, Subring.coe_inclusion]
  refine ⟨F, a, l, congrArg A.subtype hFπ, hFexp.trans hCexp, hFw, ha, ha0, hasucc,
    ?_, ?_, hrati, ?_⟩
  · intro n
    rw [hFc n, hCc (a n)]
    rfl
  · intro n
    rw [hFc n]
    exact hcD (a n)
  · intro Λ hΛ
    have hcertB := (hcert Λ hΛ).2.2
    have hFB : ∀ z : B, F.valuation (z : K) ≤ 1 := by
      intro z
      rw [hFw]
      exact hO (Subring.inclusion hBO z)
    have hsub := F.sourceSubring_le B hBA Λ
    refine ⟨hcertB.no_outside_junk_factorization, hsub, ?_⟩
    apply F.intersectionCertificate_of_no_factorization D places B hFB Λ hΛ.cofinal
      (fun Q hQ => hsub.trans (commonSupportRing_le_stalk D places Q hQ))
      (fun n => sourceBlock t (a n) (l n)) (fun n => (hrati n).symm)
      (SourceBlockData.selected_ratio_unit_elsewhere D places t a l hsupport) ?_
      hcertB.no_outside_junk_factorization
    rw [hFc 1]
    exact hcD (a 1)

end HereditaryAtomicity.DVRBase
