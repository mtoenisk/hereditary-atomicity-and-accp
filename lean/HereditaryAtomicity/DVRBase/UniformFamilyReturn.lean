import HereditaryAtomicity.DVRBase.Radical
import HereditaryAtomicity.DVRBase.SemilocalReduction
import HereditaryAtomicity.PrueferOverring
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Uniform power return in families of local source rings

An intersection of local rings retains the Jacobson property of an element
lying in every selected maximal ideal. Dimension at most one then puts that
element in the radical of every nonzero ideal of the intersection. Thus one
power works in every selected stalk; the family need not be finite.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase

/-- In dimension at most one, every Jacobson element lies in the radical of
any nonzero ideal. The source need not be local. -/
theorem jacobson_le_radical_of_dimensionLE_one
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (I : Ideal A) (hI : I ≠ ⊥) : (⊥ : Ideal A).jacobson ≤ I.radical := by
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  rintro P ⟨hIP, hP⟩
  have hP0 : P ≠ ⊥ := fun heq => hI (bot_unique (heq ▸ hIP))
  exact sInf_le ⟨bot_le, hP.isMaximal_of_ne_bot hP0⟩

/-- The uniform exponent is positive even when the ideal is the whole ring. -/
theorem exists_pos_pow_mem_of_mem_jacobson
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (I : Ideal A) (hI : I ≠ ⊥) {x : A} (hx : x ∈ (⊥ : Ideal A).jacobson) :
    ∃ n : ℕ, 0 < n ∧ x ^ n ∈ I := by
  by_cases ht : I = ⊤
  · exact ⟨1, Nat.zero_lt_one, by simp [ht]⟩
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp
    (jacobson_le_radical_of_dimensionLE_one I hI hx)
  refine ⟨n, Nat.pos_of_ne_zero ?_, hn⟩
  intro hz
  apply ht
  exact Ideal.eq_top_of_isUnit_mem I (by simpa [hz] using hn) isUnit_one

variable {K ι : Type*} [Field K]

/-- A nonzero element which is a unit in every member is a unit in their
literal intersection; its inverse is the same field element at all places. -/
theorem isUnit_iInf_of_isUnit (R : ι → Subring K) (x : ↥(⨅ i, R i))
    (hx : (x : K) ≠ 0)
    (hu : ∀ i, IsUnit (⟨x, (iInf_le R i) x.property⟩ : R i)) : IsUnit x := by
  have hinv : (x : K)⁻¹ ∈ ⨅ i, R i := by
    exact Subring.mem_iInf.mpr (fun i => Submonoid.inv_mem_of_isUnit (hu i))
  apply isUnit_iff_exists_inv.mpr
  exact ⟨⟨(x : K)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx)⟩

/-- Membership in every selected local maximal ideal implies membership in
the Jacobson radical of the intersection. -/
theorem mem_jacobson_iInf_of_mem_maximal [Nonempty ι]
    (R : ι → Subring K) [∀ i, IsLocalRing (R i)] (x : ↥(⨅ i, R i))
    (hx : ∀ i, (⟨x, (iInf_le R i) x.property⟩ : R i) ∈ IsLocalRing.maximalIdeal (R i)) :
    x ∈ (⊥ : Ideal ↥(⨅ i, R i)).jacobson := by
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hu (i : ι) : IsUnit (⟨x * y + 1, (iInf_le R i) (x * y + 1).property⟩ : R i) := by
    let xi : R i := ⟨x, (iInf_le R i) x.property⟩
    let yi : R i := ⟨y, (iInf_le R i) y.property⟩
    have hxy : -(xi * yi) ∈ IsLocalRing.maximalIdeal (R i) :=
      (IsLocalRing.maximalIdeal (R i)).neg_mem
        ((IsLocalRing.maximalIdeal (R i)).mul_mem_right yi (hx i))
    have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(xi * yi)) hxy
    change IsUnit (xi * yi + 1)
    simpa only [sub_neg_eq_add, add_comm] using hunit
  apply isUnit_iInf_of_isUnit R (x * y + 1) ?_ hu
  let i : ι := Classical.choice inferInstance
  exact Subtype.coe_ne_coe.mpr (hu i).ne_zero

/-- Uniform positive-power return over an arbitrary nonempty family of local
rings containing the same DVR and source fraction ring. -/
theorem exists_pos_pow_div_mem_family [Nonempty ι]
    (O S : Subring K) [IsDiscreteValuationRing O] [IsFractionRing S K]
    [Algebra.IsAlgebraic O K]
    (R : ι → Subring K) [∀ i, IsLocalRing (R i)]
    (hSR : ∀ i, S ≤ R i) (hOR : ∀ i, O ≤ R i)
    (π : O) (hπ : Irreducible π) (κ : ℕ) (x : K)
    (hx : ∀ i, x ∈ R i)
    (hxm : ∀ i, (⟨x, hx i⟩ : R i) ∈ IsLocalRing.maximalIdeal (R i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, x ^ n / (π : K) ^ κ ∈ R i := by
  let A : Subring K := ⨅ i, R i
  have hSA : S ≤ A := le_iInf hSR
  have hOA : O ≤ A := le_iInf hOR
  let : IsFractionRing A K := isFractionRing_of_subring_le S A hSA
  let : Ring.KrullDimLE 1 A := embedded_dimensionLE_one_of_algebraic_dvr O A hOA
  let xA : A := ⟨x, Subring.mem_iInf.mpr hx⟩
  let πA : A := Subring.inclusion hOA π
  have hπA : πA ^ κ ≠ 0 := pow_ne_zero κ (by
    intro hz
    apply hπ.ne_zero
    exact Subtype.ext (congrArg A.subtype hz))
  have hI : Ideal.span ({πA ^ κ} : Set A) ≠ ⊥ :=
    fun he => hπA (Ideal.span_singleton_eq_bot.mp he)
  have hxJ : xA ∈ (⊥ : Ideal A).jacobson :=
    mem_jacobson_iInf_of_mem_maximal R xA hxm
  obtain ⟨n, hn, hmem⟩ := exists_pos_pow_mem_of_mem_jacobson _ hI hxJ
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
  have heq : x ^ n = (π : K) ^ κ * (b : K) := congrArg A.subtype hb
  refine ⟨n, hn, fun i => ?_⟩
  rw [heq, mul_div_cancel_left₀ _ (pow_ne_zero κ (Subtype.coe_ne_coe.mpr hπ.ne_zero))]
  exact (iInf_le R i) b.property

/-- The return exponent works simultaneously at every selected stalk where
`x` is a nonunit. The selected set and the nonunit locus may be infinite or empty. -/
theorem exists_pos_pow_div_mem_at_nonunit_stalks
    (D O : Subring K) [IsFractionRing D K] [IsDiscreteValuationRing O]
    [Algebra.IsAlgebraic O K] (places : Set (MaximalSpectrum D))
    (hO : ∀ Q ∈ places, O ≤ sourceMaximalStalk D Q)
    (π : O) (hπ : Irreducible π) (κ : ℕ) (x : D) :
    ∃ n : ℕ, 0 < n ∧ ∀ Q ∈ places, x ∈ Q.asIdeal →
      (x : K) ^ n / (π : K) ^ κ ∈ sourceMaximalStalk D Q := by
  classical
  let I := {Q : MaximalSpectrum D // Q ∈ places ∧ x ∈ Q.asIdeal}
  by_cases hi : Nonempty I
  · let : Nonempty I := hi
    let R : I → Subring K := fun Q => sourceMaximalStalk D Q.val
    let : ∀ Q : I, IsLocalRing (R Q) := fun Q => by
      let S := Localization.subalgebra.ofField K Q.val.asIdeal.primeCompl
        Q.val.asIdeal.primeCompl_le_nonZeroDivisors
      let : Algebra D (R Q) := inferInstanceAs (Algebra D S)
      let : IsLocalization.AtPrime (R Q) Q.val.asIdeal :=
        inferInstanceAs (IsLocalization.AtPrime S Q.val.asIdeal)
      exact IsLocalization.AtPrime.isLocalRing (R Q) Q.val.asIdeal
    have hmax (Q : I) : (sourceMaximalMap D Q.val x) ∈
        IsLocalRing.maximalIdeal (R Q) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact ((isUnit_sourceMaximalMap_iff D Q.val x).mp hu) Q.property.2
    obtain ⟨n, hn, hret⟩ := exists_pos_pow_div_mem_family O D R
      (fun Q => le_sourceMaximalStalk D Q.val) (fun Q => hO Q.val Q.property.1)
      π hπ κ (x : K) (fun Q => (le_sourceMaximalStalk D Q.val) x.property) hmax
    exact ⟨n, hn, fun Q hQ hx => hret ⟨Q, hQ, hx⟩⟩
  · refine ⟨1, Nat.zero_lt_one, fun Q hQ hx => ?_⟩
    exact False.elim (hi ⟨⟨Q, hQ, hx⟩⟩)

end HereditaryAtomicity.DVRBase
