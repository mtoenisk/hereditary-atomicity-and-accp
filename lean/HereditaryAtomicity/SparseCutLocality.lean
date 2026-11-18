import HereditaryAtomicity.FiniteBranchCut
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Locality and fraction fields of actual sparse cuts

A finite geometric sum inverts a unit coefficient plus an everywhere-positive
remainder, because a sufficiently high power of that remainder enters the
actual open tail. No completion or formal power-series inverse is used.
-/

open scoped NNReal BigOperators
noncomputable section
namespace HereditaryAtomicity

section Locality

variable {K : Type*} [Field K] {ι : Type*} [Finite ι] [Nonempty ι]
    (v : ι → Valuation K ℝ≥0) (B : Subring K)
    (hB : ∀ (x : B), x ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) x)
    (c : ℝ) (hc : 0 ≤ c)
    (hBmem : ∀ x : K, (∀ i, v i x ≤ 1) → x ∈ B)

/-- A finite power of an everywhere-positive element crosses every cutoff. -/
theorem exists_power_order_gt {h : K} (hpos : ∀ i, 0 < realValuationOrder (v i) h) :
    ∃ n : ℕ, ∀ i, c < realValuationOrder (v i) (h^n) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image
    (fun i => realValuationOrder (v i) h) (Finset.univ_nonempty)
  obtain ⟨n, hn⟩ := exists_nat_gt (c / realValuationOrder (v j) h)
  refine ⟨n, fun i => ?_⟩
  rw [realValuationOrder_pow]
  have hjn : c < (n : ℝ) * realValuationOrder (v j) h :=
    (div_lt_iff₀ (hpos j)).mp hn
  exact hjn.trans_le (mul_le_mul_of_nonneg_left (hj i (Finset.mem_univ _)) (Nat.cast_nonneg _))

include hc hBmem in
/-- The inverse of `1+h`, for positive h, is a finite polynomial plus an actual
open-tail element. The proof constructs an intrinsic unit of the cut. -/
theorem isUnit_one_add_of_positive_tail (S : Subring B)
    (hIS : (realValuationTail v B hB c : Set B) ⊆ S)
    (h : S) (hpos : ∀ i, 0 < realValuationOrder (v i) ((h : B) : K)) :
    IsUnit (1 + h) := by
  classical
  let hK : K := ((h : B) : K)
  have hh0 : hK ≠ 0 := by
    intro hz
    have hh := hpos (Classical.arbitrary ι)
    change 0 < realValuationOrder (v (Classical.arbitrary ι)) hK at hh
    rw [hz, realValuationOrder_zero] at hh
    exact lt_irrefl _ hh
  have hy : ∀ i, (1+hK ≠ 0) ∧ realValuationOrder (v i) (1+hK) = 0 := by
    intro i
    have heq := realValuationOrder_add_eq_min (v i) one_ne_zero hh0
      (by simpa only [realValuationOrder_one] using (ne_of_lt (hpos i)))
    rw [realValuationOrder_one, min_eq_left (show 0 ≤ realValuationOrder (v i) hK from (hpos i).le)] at heq
    exact heq
  have hy0 : 1+hK ≠ 0 := (hy (Classical.arbitrary ι)).1
  obtain ⟨n, hn⟩ := exists_power_order_gt v c hpos
  let r : K := (-hK)^n / (1+hK)
  have hr0 : r ≠ 0 := div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hh0)) hy0
  have hrval : ∀ i, c < realValuationOrder (v i) r := by
    intro i
    dsimp only [r]
    rw [realValuationOrder_div (v i) (pow_ne_zero _ (neg_ne_zero.mpr hh0)) hy0,
      (hy i).2, sub_zero, realValuationOrder_pow, realValuationOrder_neg]
    simpa only [realValuationOrder_pow] using hn i
  have hrB : r ∈ B := hBmem r fun i =>
    (realValuationOrder_nonneg_iff (v i) hr0).mp (hc.trans (hrval i).le)
  let rB : B := ⟨r, hrB⟩
  have hrS : rB ∈ S := hIS (Or.inr hrval)
  let w : S := (∑ i ∈ Finset.range n, (-h)^i) + ⟨rB, hrS⟩
  apply IsUnit.of_mul_eq_one (a := 1+h) w
  apply Subtype.ext
  apply Subtype.ext
  simp only [w, Subring.coe_mul, Subring.coe_add, Subring.coe_one,
    AddSubmonoidClass.coe_finsetSum, Subring.coe_pow, Subring.coe_neg]
  change (1+hK) * ((∑ i ∈ Finset.range n, (-hK)^i) + r) = 1
  have hg := geom_sum_mul_neg (-hK) n
  simp only [sub_neg_eq_add] at hg
  calc
    (1+hK) * ((∑ i ∈ Finset.range n, (-hK)^i) + r) =
        (∑ i ∈ Finset.range n, (-hK)^i) * (1+hK) + (-hK)^n := by
      rw [mul_add, mul_comm (1+hK), show (1+hK)*r = (-hK)^n from
        mul_div_cancel₀ _ hy0]
    _ = 1 := by rw [hg]; ring

include hc hBmem in
/-- A coefficient unit plus an everywhere-positive remainder is an intrinsic
unit of any intermediate cut containing the open tail. -/
theorem isUnit_of_coefficient_plus_positive (S : Subring B)
    (hIS : (realValuationTail v B hB c : Set B) ⊆ S)
    (A : Subring B) (hAS : A ≤ S) (x : S) (a : A) (ha : IsUnit a)
    (hpos : (x : B) - (a : B) ∈ realValuationTail v B hB 0) : IsUnit x := by
  obtain ⟨u, rfl⟩ := ha
  let uS : Sˣ := Units.map (Subring.inclusion hAS).toMonoidHom u
  have hucoe : ((uS : S) : B) = ((u : A) : B) := rfl
  rcases hpos with hzero | hpos
  · have hx : x = (uS : S) := by
      apply Subtype.ext
      exact sub_eq_zero.mp hzero
    exact hx ▸ uS.isUnit
  · let t : S := (x - (uS : S)) * (↑(uS⁻¹) : S)
    have htpos : ∀ i, 0 < realValuationOrder (v i) ((t : B) : K) := by
      intro i
      have hdiff0 : (((x : B) : K) - (((u : A) : B) : K)) ≠ 0 := by
        intro hz
        have hh := hpos i
        change 0 < realValuationOrder (v i) ((((x : B) : K) - (((u : A) : B) : K))) at hh
        rw [hz, realValuationOrder_zero] at hh
        exact lt_irrefl _ hh
      have hinv0 : (((↑(uS⁻¹) : S) : B) : K) ≠ 0 :=
        Subtype.coe_ne_coe.mpr (Subtype.coe_ne_coe.mpr uS⁻¹.ne_zero)
      change 0 < realValuationOrder (v i)
        ((((x : B) : K) - (((uS : S) : B) : K)) * (((↑(uS⁻¹) : S) : B) : K))
      rw [hucoe, realValuationOrder_mul (v i) hdiff0 hinv0]
      have hval := realValuationOrder_eq_zero_of_isUnit (v i) B
        (fun z hz => hB z hz i) (uS⁻¹.isUnit.map S.subtype)
      change realValuationOrder (v i) (((↑(uS⁻¹) : S) : B) : K) = 0 at hval
      rw [hval, add_zero]
      exact hpos i
    have hu := uS.isUnit.mul (isUnit_one_add_of_positive_tail v B hB c hc hBmem S hIS t htpos)
    convert hu using 1
    dsimp only [t]
    have heq : (uS : S) * (1 + (x - (uS : S)) * (↑(uS⁻¹) : S)) = x := by
      calc
        _ = (uS : S) + (x - (uS : S)) * ((uS : S) * (↑(uS⁻¹) : S)) := by ring
        _ = x := by simp
    exact heq.symm

omit [Finite ι] [Nonempty ι] in
include hc in
/-- Every polynomial-plus-tail element has a coefficient representative modulo
the actual everywhere-positive ideal. -/
theorem polynomialTailRing_le_coefficient_positive (A : Subring B) (a : ℕ → B)
    (hpos : ∀ n i, 0 < realValuationOrder (v i) (a n)) :
    polynomialTailRing v B hB A a c ≤ subringPlusIdeal A (realValuationTail v B hB 0) := by
  intro x hx
  obtain ⟨p, z, hz, rfl⟩ := (mem_polynomialTailRing v B hB A a c x).mp hx
  apply (subringPlusIdeal A (realValuationTail v B hB 0)).add_mem
  · apply MvPolynomial.eval₂_mem
    · intro d _
      exact subring_le_subringPlusIdeal A _ (p.coeff d).property
    · intro n
      exact ideal_subset_subringPlusIdeal A _ (Or.inr (hpos n))
  · apply ideal_subset_subringPlusIdeal A _
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · exact Or.inr (fun i => hc.trans_lt (hz i))

include hc hBmem in
/-- With local coefficient ring and positive generators, the actual polynomial
plus open-tail cut is local. No coefficient discreteness hypothesis is needed
for this clause. -/
theorem polynomialTailRing_isLocalRing (A : Subring B) [IsLocalRing A]
    (a : ℕ → B) (hpos : ∀ n i, 0 < realValuationOrder (v i) (a n)) :
    IsLocalRing (polynomialTailRing v B hB A a c) := by
  let S := polynomialTailRing v B hB A a c
  have hAS : A ≤ S := by
    intro a ha
    apply (mem_polynomialTailRing v B hB A _ c a).mpr
    exact ⟨MvPolynomial.C ⟨a, ha⟩, 0, (realValuationTail v B hB c).zero_mem, by simp⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  obtain ⟨a, ha, h, hh, heq⟩ := polynomialTailRing_le_coefficient_positive v B hB c hc A _ hpos x.property
  have hxa : (x : B) - a ∈ realValuationTail v B hB 0 := by
    rw [heq]
    simpa using hh
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, ha⟩ : A) with hu | hu
  · left
    exact isUnit_of_coefficient_plus_positive v B hB c hc hBmem S
      (tail_subset_polynomialTailRing v B hB A _ c) A hAS x ⟨a, ha⟩ hu hxa
  · right
    apply isUnit_of_coefficient_plus_positive v B hB c hc hBmem S
      (tail_subset_polynomialTailRing v B hB A _ c) A hAS (1-x) (1-(⟨a, ha⟩ : A)) hu
    change (1 - (x : B)) - (1-a) ∈ realValuationTail v B hB 0
    convert (realValuationTail v B hB 0).neg_mem hxa using 1
    ring

end Locality

/-- A literal subring containing a nonzero ideal has the ambient domain's
specified fraction field; the inherited nested algebra map is used. -/
theorem isFractionRing_of_subring_common_nonzeroIdeal
    {K : Type*} [Field K] (B : Subring K) [IsFractionRing B K]
    (S : Subring B) (I : Ideal B) (hI : I ≠ ⊥) (hIS : (I : Set B) ⊆ S) :
    IsFractionRing S K := by
  obtain ⟨z, hzI, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hzK : (z : K) ≠ 0 := Subtype.coe_ne_coe.mpr hz0
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective B x
  refine ⟨⟨a*z, hIS (I.mul_mem_left a hzI)⟩,
    ⟨b*z, hIS (I.mul_mem_left b hzI)⟩, ?_⟩
  change (a : K)/(b : K) = ((a : K)*(z : K))/((b : K)*(z : K))
  exact (mul_div_mul_right (a : K) (b : K) hzK).symm

/-- Full concrete sparse cut: a local nonatomic subring with the original
fraction field and the actual nonzero common open tail. -/
theorem exists_local_nonatomic_polynomial_tail
    {K : Type*} [Field K] {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → Valuation K ℝ≥0) (B : Subring K) [IsFractionRing B K]
    (hB : ∀ (x : B), x ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) x)
    (hBmem : ∀ x : K, (∀ i, v i x ≤ 1) → x ∈ B)
    (C : Subring B) (A : Subring B) [IsLocalRing A] (hAC : A ≤ C)
    (hcoeff : ∀ x : A, x ≠ 0 → ∃ r : ℕ, ∀ i,
      realValuationOrder (v i) ((x : B) : K) = r)
    (π : B) (hπ : π ≠ 0) (hπval : ∀ i, realValuationOrder (v i) π = 1)
    (c : ℕ) (hc : 0 < c)
    (hIC : (realValuationTail v B hB c : Set B) ⊆ C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ x : B, x ∈ C ∧ x ≠ 0 ∧
      ∀ i, 0 < realValuationOrder (v i) x ∧ realValuationOrder (v i) x < ε) :
    ∃ S : Subring B, S ≤ C ∧ IsLocalRing S ∧ ¬ Factorization.IsAtomicDomain S ∧
      (realValuationTail v B hB c : Set B) ⊆ S ∧
      realValuationTail v B hB c ≠ ⊥ ∧ IsFractionRing S K := by
  classical
  let CK : Subring K := C.map B.subtype
  let ν : ι → K → ℝ := fun i => realValuationOrder (v i)
  have hsmallK : ∀ ε : ℝ, 0 < ε → ∃ x : K, x ∈ CK ∧ x ≠ 0 ∧
      ∀ i, 0 < ν i x ∧ ν i x < ε := by
    intro ε hε
    obtain ⟨x, hxC, hx0, hx⟩ := hsmall ε hε
    exact ⟨x, ⟨x, hxC, rfl⟩, Subtype.coe_ne_coe.mpr hx0, hx⟩
  obtain ⟨i₀, hfixed⟩ := exists_coinitial_minimum_branch CK ν hsmallK
  obtain ⟨b, hbC, hb0, hb⟩ := hfixed 1 zero_lt_one
  have hbB : b ∈ B := by
    obtain ⟨x, _, rfl⟩ := hbC
    exact x.property
  let x : B := π^c * ⟨b, hbB⟩
  have hx0 : x ≠ 0 := mul_ne_zero (pow_ne_zero c hπ) (by
    intro h
    exact hb0 (congrArg Subtype.val h))
  have hxval : ∀ i, realValuationOrder (v i) x = (c : ℝ) + ν i b := by
    intro i
    change realValuationOrder (v i) ((π : K)^c*b) = _
    rw [realValuationOrder_mul (v i) (pow_ne_zero _ (Subtype.coe_ne_coe.mpr hπ)) hb0,
      realValuationOrder_pow, hπval i, mul_one]
  have hxI : x ∈ realValuationTail v B hB c := by
    right
    intro i
    rw [hxval i]
    linarith [(hb i).1]
  let β : ℝ := realValuationOrder (v i₀) x
  have hβ : ∀ r : ℕ, (r : ℝ) ≠ β := by
    intro r heq
    have hrlo : (c : ℝ) < r := by rw [heq]; dsimp only [β]; rw [hxval i₀]; linarith [(hb i₀).1]
    have hrhi : (r : ℝ) < c+1 := by rw [heq]; dsimp only [β]; rw [hxval i₀]; linarith [(hb i₀).2.1]
    have hrlo' : c < r := by exact_mod_cast hrlo
    have hrhi' : r < c+1 := by exact_mod_cast hrhi
    omega
  obtain ⟨aK, haK, htie, havoid⟩ := exists_sparse_source_sequence CK ν i₀
    (fun i x y hx hy => realValuationOrder_mul (v i) hx hy) hfixed c β hβ
  have haKB (n : ℕ) : aK n ∈ B := by
    obtain ⟨x, _, hx⟩ := (haK n).1
    rw [← hx]
    exact x.property
  let a : ℕ → B := fun n => ⟨aK n, haKB n⟩
  have haC : ∀ n, a n ∈ C := by
    intro n
    obtain ⟨x, hxC, hx⟩ := (haK n).1
    have heq : a n = x := Subtype.ext hx.symm
    exact heq ▸ hxC
  have ha0 : ∀ n, a n ≠ 0 := by
    intro n h
    exact (haK n).2.1 (congrArg Subtype.val h)
  have hapos : ∀ n i, 0 < realValuationOrder (v i) (a n) := fun n i => (haK n).2.2 i |>.1
  have hamin : ∀ n i, realValuationOrder (v i₀) (a n) ≤ realValuationOrder (v i) (a n) :=
    fun n i => (haK n).2.2 i |>.2.2
  have hasmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ i,
      realValuationOrder (v i) (a n) < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, fun i => ((haK n).2.2 i).2.1.trans hn⟩
  let M := sparseValueMonoid (fun n => ν i₀ (aK n))
  have hxM : realValuationOrder (v i₀) x ∉ M := by
    rintro ⟨r, d, heq⟩
    exact havoid r d heq.symm
  let S := polynomialTailRing v B hB A a c
  have hI0 : realValuationTail v B hB c ≠ ⊥ := by
    intro hzero
    exact hx0 (Ideal.mem_bot.mp (hzero ▸ hxI))
  refine ⟨S, polynomialTailRing_le v B hB A a c C hAC haC hIC,
    polynomialTailRing_isLocalRing v B hB c (Nat.cast_nonneg c) hBmem A a hapos, ?_,
    tail_subset_polynomialTailRing v B hB A a c, hI0,
    isFractionRing_of_subring_common_nonzeroIdeal B S _ hI0
      (tail_subset_polynomialTailRing v B hB A a c)⟩
  · exact not_isAtomicDomain_polynomialTailRing v B hB A a ha0 i₀ c hcoeff hamin
      (le_of_lt (Nat.cast_pos.mpr hc)) hBmem hapos hasmall (fun r s d e hd he heq => (htie r s d e hd he heq).2)
      M (one_mem_sparseValueMonoid _) (generator_mem_sparseValueMonoid _)
      x hx0 hxI hxM


/-- Separate positive-source coinitiality at each actual branch supplies the
full local nonatomic common-ideal cut with its original fraction field. -/
theorem exists_local_nonatomic_cut_of_branchwise_coinitial
    {K : Type*} [Field K] {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → Valuation K ℝ≥0) (B : Subring K) [IsFractionRing B K]
    (hB : ∀ (x : B), x ≠ 0 → ∀ i, 0 ≤ realValuationOrder (v i) x)
    (hBmem : ∀ x : K, (∀ i, v i x ≤ 1) → x ∈ B)
    (C : Subring B) (A : Subring B) [IsLocalRing A] (hAC : A ≤ C)
    (hcoeff : ∀ x : A, x ≠ 0 → ∃ r : ℕ, ∀ i,
      realValuationOrder (v i) ((x : B) : K) = r)
    (π : B) (hπ : π ≠ 0) (hπval : ∀ i, realValuationOrder (v i) π = 1)
    (c : ℕ) (hc : 0 < c)
    (hIC : (realValuationTail v B hB c : Set B) ⊆ C)
    (hbranch : ∀ i (ε : ℝ), 0 < ε → ∃ x : B, x ∈ C ∧ x ≠ 0 ∧
      (∀ j, 0 < realValuationOrder (v j) x) ∧ realValuationOrder (v i) x < ε) :
    ∃ S : Subring B, S ≤ C ∧ IsLocalRing S ∧ ¬ Factorization.IsAtomicDomain S ∧
      (realValuationTail v B hB c : Set B) ⊆ S ∧
      realValuationTail v B hB c ≠ ⊥ ∧ IsFractionRing S K := by
  apply exists_local_nonatomic_polynomial_tail v B hB hBmem C A hAC hcoeff π hπ hπval c hc hIC
  intro ε hε
  let CK : Subring K := C.map B.subtype
  let ν : ι → K → ℝ := fun i => realValuationOrder (v i)
  have hb : ∀ i (δ : ℝ), 0 < δ → ∃ x : K, x ∈ CK ∧ x ≠ 0 ∧
      (∀ j, 0 < ν j x) ∧ ν i x < δ := by
    intro i δ hδ
    obtain ⟨x, hxC, hx0, hxpos, hxsmall⟩ := hbranch i δ hδ
    exact ⟨x, ⟨x, hxC, rfl⟩, Subtype.coe_ne_coe.mpr hx0, hxpos, hxsmall⟩
  obtain ⟨y, hyC, hy0, hy⟩ := exists_simultaneously_small_source CK ν
    (fun i x y hx hy => realValuationOrder_mul (v i) hx hy)
    (fun i x y hx hy hne => realValuationOrder_add_eq_min (v i) hx hy hne)
    hb ε hε
  obtain ⟨x, hxC, hxy⟩ := hyC
  change (x : K) = y at hxy
  refine ⟨x, hxC, ?_, ?_⟩
  · intro hx0
    exact hy0 (hxy.symm.trans (by rw [hx0]; rfl))
  · intro i
    change 0 < ν i (x : K) ∧ ν i (x : K) < ε
    rw [hxy]
    exact hy i

end HereditaryAtomicity
