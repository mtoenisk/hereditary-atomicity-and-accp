import UnconditionalCounterexample.PaperGenericRecovery
import UnconditionalCounterexample.SequenceExactTransfer
import UnconditionalCounterexample.SharpPrimaryBound
import Mathlib.Order.Filter.AtTopBot.Finite
/-!
# Sharp divisor extraction with the manuscript's exact primary supremum

For the fixed nonzero top in the original subring, r is literally the supremum
of its primary orders. The same divisor carries its pure escaping profile,
signed finite normalized word, exponent bound 2r and positive latest exponent.
The resulting original-subring divisors form a strictly increasing sequence of
listed stages. At every prescribed positive integer n with nt in the original
subring, the exact power L_p^(2r) lies in the integral local image.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperSharpExtraction

open Polynomial Filter NormalizedWords PrincipalProfiles
open PaperConstruction

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- The paper's exact finite supremum of the primary values of the fixed top. -/
abbrev primaryBound (x : domain) : ℕ := valuationProfiles.primarySup x

theorem primaryBound_eq (x : domain) :
    primaryBound x = sSup (Set.range (fun j => valuationProfiles.value (.primary j) x)) := rfl

theorem primaryBound_pos (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) : 0 < primaryBound x :=
  valuationProfiles.primarySup_pos_of_unbounded T (subring_reflects_units T) x hx hunbounded

/-- One actual divisor simultaneously carries its sharp profile bound, its
signed normalized word, and a positive latest construction exponent. -/
theorem exists_divisor_word_beyond (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) (N M : ℕ) :
    ∃ y : T, IsEscapingPrimaryDivisor valuationProfiles T x y (primaryBound x) N ∧
      ∃ e : ℕ →₀ ℤ,
      (((y : domain) : RatFunc ℚ) = word (CompleteProfiles.generators raw exponent) e ∨
        ((y : domain) : RatFunc ℚ) = -word (CompleteProfiles.generators raw exponent) e) ∧
      (∀ j, |e j| ≤ (2 * primaryBound x : ℕ)) ∧
      ∃ n : ℕ, M < n ∧ 0 < e n ∧ ∀ j, n < j → e j = 0 := by
  let r := primaryBound (x : domain)
  let K := max N (2 * M + 2)
  obtain ⟨y, hy⟩ := valuationProfiles.exists_escaping_primary_divisor_sup
    T (subring_reflects_units T) x hx hunbounded K
  have hyD : (y : domain) ≠ 0 := fun h => hy.ne_zero (Subtype.ext h)
  have hyK : ((y : domain) : RatFunc ℚ) ≠ 0 := fun h => hyD (Subtype.ext h)
  have hl : DiscreteOrders.order (CompleteProfiles.valuations poles places .limit)
      ((y : domain) : RatFunc ℚ) = 0 := by
    rw [← valuationProfiles_cast _ y hyD, hy.limit_zero]
    rfl
  have ho (i : CompleteProfiles.Outside poles) :
      DiscreteOrders.order (CompleteProfiles.valuations poles places (.outside i))
        ((y : domain) : RatFunc ℚ) = 0 := by
    rw [← valuationProfiles_cast _ y hyD, hy.outside_zero]
    rfl
  obtain ⟨e, he, hrep⟩ := CompleteProfiles.exists_signed_word raw
    (fun i => ⟨construction.chain.raw_monic i, construction.chain.raw_irreducible i⟩)
    (fun _ _ h => construction.chain.raw_degree_strict.injective (congrArg natDegree h))
    exponent places generatorProfiles ((y : domain) : RatFunc ℚ) hyK hl ho
  let g : ℕ → ℤ := fun j => valuationProfiles.value (.primary j) (y : domain)
  have hg (j : ℕ) : DiscreteOrders.order
      (CompleteProfiles.valuations poles places (.primary j)) ((y : domain) : RatFunc ℚ) = g j :=
    (valuationProfiles_cast _ y hyD).symm
  have hrep' : Represents (StageExponents.bExponents e) (StageExponents.qExponents e) g := by
    simpa only [hg] using hrep
  have hb (j : ℕ) : 0 ≤ g j ∧ g j ≤ r := by
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (hy.primary_bound j)⟩
  have hn : ∃ j, g j ≠ 0 := by
    obtain ⟨j, hj⟩ := hy.nonempty_support
    exact ⟨j, Int.natCast_ne_zero.mpr (Nat.ne_of_gt hj)⟩
  have hz (j : ℕ) (hj : j < 2 * M + 2) : g j = 0 := by
    change (valuationProfiles.value (.primary j) (y : domain) : ℤ) = 0
    rw [hy.prefix_zero j (hj.trans_le (le_max_right N (2 * M + 2))), Nat.cast_zero]
  obtain ⟨n, hnM, hen, _, heb, hlate⟩ :=
    StageExponents.exists_bounded_latest_beyond e g hrep' hb hn M hz
  refine ⟨y, ?_, e, he, ?_, n, hnM, hen, hlate⟩
  · exact { hy with prefix_zero := fun j hj => hy.prefix_zero j (hj.trans_le (le_max_left N (2 * M + 2))) }
  · intro j
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using heb j

/-- Actual divisors in the original subring can be chosen as listed words
with strictly increasing last stages and the exact common budget 2 sup v_j(x).
Signs are absorbed inside T, which preserves divisibility by the same top. -/
theorem exists_sharp_listed_sequence (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ y : ℕ → T, ∃ stage : ℕ → ℕ,
      ∃ w : ∀ i, RawWords.StageWord (stage i) (stage i + 1),
      StrictMono stage ∧ Tendsto stage atTop atTop ∧
      (∀ i, y i ∣ x) ∧ (∀ i, ¬ IsUnit (y i)) ∧
      (∀ i, (w i).latestExponent ≤ 2 * primaryBound x) ∧
      (∀ i j, |(w i).oldExponent j| ≤ (2 * primaryBound x : ℕ)) ∧
      ∀ i, (((y i : T) : domain) : RatFunc ℚ) =
        CompleteProfiles.generators raw exponent (stage i) ^ (w i).latestExponent *
          (∏ j ∈ Finset.range (stage i),
            CompleteProfiles.generators raw exponent j ^ (w i).oldExponent j) := by
  classical
  let r := primaryBound (x : domain)
  have hchoose (i : ℕ) : ∃ y : T, y ∣ x ∧ ¬ IsUnit y ∧ ∃ n : ℕ,
      i < n ∧ ∃ w : RawWords.StageWord n (n + 1),
      w.latestExponent ≤ 2 * r ∧
      (∀ j, |w.oldExponent j| ≤ (2 * r : ℕ)) ∧
      ((y : domain) : RatFunc ℚ) =
        CompleteProfiles.generators raw exponent n ^ w.latestExponent *
          (∏ j ∈ Finset.range n,
            CompleteProfiles.generators raw exponent j ^ w.oldExponent j) := by
    obtain ⟨y, hy, e, he, hb, n, hn, hpos, hlate⟩ :=
      exists_divisor_word_beyond T x hx hunbounded i (max i (2 * r))
    obtain ⟨w, hw, hwa⟩ := StageExponents.exists_stageWord_of_latest e n (2 * r)
      hpos hb (by omega)
    have hp := StageExponents.prod_eq_listed_word
      (CompleteProfiles.generators raw exponent) e n (n + 1) w hw hwa hlate
    have hbound : w.latestExponent ≤ 2 * r := by
      have h := abs_le.mp (hb n)
      omega
    have hold (j : ℕ) : |w.oldExponent j| ≤ (2 * r : ℕ) := by
      by_cases hj : j < n
      · rw [hw j hj]
        exact hb j
      · simp only [RawWords.StageWord.oldExponent, dite_eq_right hj, abs_zero]
        positivity
    rcases he with he | he
    · exact ⟨y, hy.dvd_top, hy.nonunit_source, n, by omega, w, hbound, hold, he.trans hp⟩
    · refine ⟨-y, hy.dvd_top.neg_left, ?_, n, by omega, w, hbound, hold, ?_⟩
      · intro hunit
        apply hy.nonunit_source
        simpa only [neg_neg] using hunit.neg
      · change -((y : domain) : RatFunc ℚ) = _
        rw [he, neg_neg]
        exact hp
  choose y hy hunit stage hlarge w hbound hold hword using hchoose
  obtain ⟨φ, _, hmono⟩ := strictMono_subseq_of_id_le (fun i => (hlarge i).le)
  exact ⟨y ∘ φ, stage ∘ φ, fun i => w (φ i), hmono, hmono.tendsto_atTop,
    fun i => hy (φ i), fun i => hunit (φ i), fun i => hbound (φ i),
    fun i j => hold (φ i) j, fun i => hword (φ i)⟩

/-- The exact-radius words in the literal pole-algebra image are ready for the
existing local transfer theorem, with no loss of the original divisor data. -/
theorem exists_sharp_image_sequence (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ y : ℕ → T.map PaperInclusion.inclusion, ∃ stage : ℕ → ℕ,
      ∃ w : ∀ i, ConstructionWords.Word (stage i),
      StrictMono stage ∧ Tendsto stage atTop atTop ∧
      (∀ i, (w i).latestExponent ≤ 2 * primaryBound x) ∧
      ∀ i, ((y i : PaperInclusion.poleAlgebra) : RatFunc ℚ) =
        ScheduledRecovery.generators raw exponent (stage i) ^ (w i).latestExponent *
          (∏ j ∈ Finset.range (stage i),
            ScheduledRecovery.generators raw exponent j ^ (w i).oldExponent j) := by
  obtain ⟨y, stage, w, hm, ht, _, _, hb, _, hw⟩ :=
    exists_sharp_listed_sequence T x hx hunbounded
  let z (i : ℕ) : T.map PaperInclusion.inclusion :=
    ⟨PaperInclusion.inclusion (y i), ⟨y i, (y i).property, rfl⟩⟩
  exact ⟨z, stage, w, hm, ht, hb, hw⟩

/-- The exact source exponent R=2 sup_j v_j(x) works at the p-part of every
prescribed positive n with nt in the original T, without enlarging the radius. -/
theorem sharp_power_ideal_subset_at_prescribed_scale
    (T : Subring domain) (x : T) (hx : x ≠ 0)
    (hunbounded : ¬ Factorization.HasBoundedFactorizations x)
    (n : ℕ) (hn : 0 < n) (hnt : (n : domain) * PaperInclusion.coordinate ∈ T) (j : ℕ) :
    ∀ z ∈ Ideal.span {algebraMap ℚ_[(PrimaryChoices.primes j).val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[(PrimaryChoices.primes j).val] poles))
        (((X - C (SequenceLocalTransfer.branch construction j false)) *
          (X - C (SequenceLocalTransfer.branch construction j true))) ^ (2 * primaryBound x))},
      z ∈ PoleTensorConductor.image (PrimaryChoices.primes j).val poles
        (SequenceExactTransfer.raw_nonzero construction) (T.map PaperInclusion.inclusion) := by
  obtain ⟨y, stage, w, _, ht, hb, hw⟩ := exists_sharp_image_sequence T x hx hunbounded
  have hntB : (n : PaperInclusion.poleAlgebra) *
      algebraMap ℚ[X] PaperInclusion.poleAlgebra X ∈ T.map PaperInclusion.inclusion := by
    exact ⟨_, hnt, by rw [map_mul, map_natCast, PaperInclusion.inclusion_coordinate]; rfl⟩
  exact SequenceExactTransfer.power_ideal_subset_at_prescribed_scale construction
    (T.map PaperInclusion.inclusion) y stage ht w (2 * primaryBound x)
    (Filter.Eventually.of_forall hb) hw n hn hntB j

end UnconditionalCounterexample.PaperSharpExtraction
