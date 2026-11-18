import UnconditionalCounterexample.EscapingProfiles
import UnconditionalCounterexample.EscapingWords

/-!
# From intrinsic unbounded factorizations to actual bounded words

Apply the checked escaping-divisor theorem in the original T, then identify its
profile coordinates with the actual primary/guard/horizontal data. The produced
sequence lies in the literal image of T in the pole algebra and retains one
positive common exponent budget. No escaping sequence or word representation is
assumed. Realization compatibility hypotheses remain explicit.
-/

namespace UnconditionalCounterexample.UnboundedWords

open Polynomial Filter NormalizedWords RawWords WithZero

noncomputable local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance primeFact (p : {p : ℕ // p.Prime}) : Fact p.val.Prime := ⟨p.property⟩

/-- The actual extraction from unbounded factorizations supplies the sequence
inside the image of the original subring in B. The realization hypotheses
identify its abstract profile coordinates with actual primary/guard/horizontal
valuation facts; no signed representation or escaping sequence is assumed. -/
theorem exists_listed_sequence_of_unbounded {ι : Type*}
    (F : ℕ → ℚ[X]) (hF : ∀ i, (F i).Monic ∧ Irreducible (F i))
    (hinj : Function.Injective F) (E : ℕ → ℕ)
    (primary : ℕ → Valuation (RatFunc ℚ) ℤᵐ⁰)
    (guard : ∀ p : {p : ℕ // p.Prime}, RatFunc ℚ →+* ℚ_[p.val])
    (hb : ∀ n j, primary j (normalizedFactor
      (fun i => algebraMap ℚ[X] (RatFunc ℚ) (F i)) E (Generator.b n).stage) =
        exp (-PrimaryWordProfiles.bWeight n j))
    (hq : ∀ n j, primary j (normalizedFactor
      (fun i => algebraMap ℚ[X] (RatFunc ℚ) (F i)) E (Generator.q n).stage) =
        exp (-PrimaryWordProfiles.qWeight n j))
    (hguard : ∀ p i, @Padic.mulValuation p.val ⟨p.property⟩
      (guard p (normalizedFactor (fun j => algebraMap ℚ[X] (RatFunc ℚ) (F j)) E i)) = 1)
    (D : Subring (PoleAlgebra.generated (Set.range F))) (v : ValuationProfiles D ι)
    (hprimary : ∀ z : D, z ≠ 0 → ∀ j,
      primary j ((z : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) =
        exp (-(v.value (.primary j) z : ℤ)))
    (hguards : ∀ z : D, z ≠ 0 → (∀ i, v.value (.outside i) z = 0) → ∀ p,
      @Padic.mulValuation p.val ⟨p.property⟩
        (guard p ((z : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ)) = 1)
    (hhorizontal : ∀ z : D, z ≠ 0 → v.value .limit z = 0 →
      (∀ i, v.value (.outside i) z = 0) →
      (((z : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ)⁻¹ ∈
        PoleAlgebra.generated (Set.range F)))
    (T : Subring D) (hunit : ∀ y : T, IsUnit (y : D) → IsUnit y)
    (x : T) (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ r : ℕ, 0 < r ∧ ∃ y : ℕ → T.map D.subtype, ∃ stage : ℕ → ℕ,
      ∃ w : ∀ i, StageWord (stage i) (stage i + 1),
      (∀ i, i < stage i) ∧ Tendsto stage atTop atTop ∧
      (∀ i, (w i).latestExponent ≤ 2 * r) ∧
      (∀ i j, |(w i).oldExponent j| ≤ (2 * r : ℕ)) ∧ ∀ i,
        ((y i : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) =
          normalizedFactor (fun j => algebraMap ℚ[X] (RatFunc ℚ) (F j)) E (stage i) ^
            (w i).latestExponent *
          (∏ j ∈ Finset.range (stage i),
            normalizedFactor (fun k => algebraMap ℚ[X] (RatFunc ℚ) (F k)) E j ^
              (w i).oldExponent j) := by
  obtain ⟨r, hr, hextract⟩ := v.exists_escaping_primary_divisors T hunit hx hunbounded
  refine ⟨r, hr, ?_⟩
  apply EscapingWords.exists_listed_sequence_of_valuation_data F hF hinj E primary guard
    hb hq hguard (T.map D.subtype) r
  intro N
  obtain ⟨z, hz⟩ := hextract (2 * N + 2)
  let z' : T.map D.subtype := ⟨(z : D), ⟨z, z.property, rfl⟩⟩
  have hzD : (z : D) ≠ 0 := fun h => hz.ne_zero (Subtype.ext h)
  have hzB : ((z : D) : PoleAlgebra.generated (Set.range F)) ≠ 0 :=
    fun h => hzD (Subtype.ext h)
  have hzK : (((z : D) : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) ≠ 0 :=
    fun h => hzB (Subtype.ext h)
  refine ⟨z', (fun j => (v.value (.primary j) (z : D) : ℤ)), hzK,
    hhorizontal z hzD hz.limit_zero hz.outside_zero,
    hguards z hzD hz.outside_zero, hprimary z hzD, ?_, ?_, ?_⟩
  · intro j
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (hz.primary_bound j)⟩
  · obtain ⟨j, hj⟩ := hz.nonempty_support
    refine ⟨j, ?_⟩
    change (v.value (.primary j) (z : D) : ℤ) ≠ 0
    exact_mod_cast Nat.ne_of_gt hj
  · intro j hj
    simp only [hz.prefix_zero j hj, Nat.cast_zero]

end UnconditionalCounterexample.UnboundedWords



namespace UnconditionalCounterexample.UnboundedWords
open Polynomial Filter NormalizedWords RawWords WithZero
noncomputable local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance primeFactMap (p : {p : ℕ // p.Prime}) : Fact p.val.Prime := ⟨p.property⟩

/-- The actual extraction from unbounded factorizations supplies the sequence
inside the image of the original subring in B. The realization hypotheses
identify its abstract profile coordinates with actual primary/guard/horizontal
valuation facts; no signed representation or escaping sequence is assumed. -/
theorem exists_listed_sequence_of_unbounded_map {ι : Type*}
    (F : ℕ → ℚ[X]) (hF : ∀ i, (F i).Monic ∧ Irreducible (F i))
    (hinj : Function.Injective F) (E : ℕ → ℕ)
    (primary : ℕ → Valuation (RatFunc ℚ) ℤᵐ⁰)
    (guard : ∀ p : {p : ℕ // p.Prime}, RatFunc ℚ →+* ℚ_[p.val])
    (hb : ∀ n j, primary j (normalizedFactor
      (fun i => algebraMap ℚ[X] (RatFunc ℚ) (F i)) E (Generator.b n).stage) =
        exp (-PrimaryWordProfiles.bWeight n j))
    (hq : ∀ n j, primary j (normalizedFactor
      (fun i => algebraMap ℚ[X] (RatFunc ℚ) (F i)) E (Generator.q n).stage) =
        exp (-PrimaryWordProfiles.qWeight n j))
    (hguard : ∀ p i, @Padic.mulValuation p.val ⟨p.property⟩
      (guard p (normalizedFactor (fun j => algebraMap ℚ[X] (RatFunc ℚ) (F j)) E i)) = 1)
    {D : Type*} [CommRing D] [IsDomain D]
    (f : D →+* PoleAlgebra.generated (Set.range F)) (hf : Function.Injective f)
    (v : ValuationProfiles D ι)
    (hprimary : ∀ z : D, z ≠ 0 → ∀ j,
      primary j (f z : RatFunc ℚ) =
        exp (-(v.value (.primary j) z : ℤ)))
    (hguards : ∀ z : D, z ≠ 0 → (∀ i, v.value (.outside i) z = 0) → ∀ p,
      @Padic.mulValuation p.val ⟨p.property⟩
        (guard p (f z : RatFunc ℚ)) = 1)
    (hhorizontal : ∀ z : D, z ≠ 0 → v.value .limit z = 0 →
      (∀ i, v.value (.outside i) z = 0) →
      ((f z : RatFunc ℚ)⁻¹ ∈
        PoleAlgebra.generated (Set.range F)))
    (T : Subring D) (hunit : ∀ y : T, IsUnit (y : D) → IsUnit y)
    (x : T) (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    ∃ r : ℕ, 0 < r ∧ ∃ y : ℕ → T.map f, ∃ stage : ℕ → ℕ,
      ∃ w : ∀ i, StageWord (stage i) (stage i + 1),
      (∀ i, i < stage i) ∧ Tendsto stage atTop atTop ∧
      (∀ i, (w i).latestExponent ≤ 2 * r) ∧
      (∀ i j, |(w i).oldExponent j| ≤ (2 * r : ℕ)) ∧ ∀ i,
        ((y i : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) =
          normalizedFactor (fun j => algebraMap ℚ[X] (RatFunc ℚ) (F j)) E (stage i) ^
            (w i).latestExponent *
          (∏ j ∈ Finset.range (stage i),
            normalizedFactor (fun k => algebraMap ℚ[X] (RatFunc ℚ) (F k)) E j ^
              (w i).oldExponent j) := by
  obtain ⟨r, hr, hextract⟩ := v.exists_escaping_primary_divisors T hunit hx hunbounded
  refine ⟨r, hr, ?_⟩
  apply EscapingWords.exists_listed_sequence_of_valuation_data F hF hinj E primary guard
    hb hq hguard (T.map f) r
  intro N
  obtain ⟨z, hz⟩ := hextract (2 * N + 2)
  let z' : T.map f := ⟨f (z : D), ⟨z, z.property, rfl⟩⟩
  have hzD : (z : D) ≠ 0 := fun h => hz.ne_zero (Subtype.ext h)
  have hzB : f (z : D) ≠ 0 :=
    fun h => hzD (hf (h.trans f.map_zero.symm))
  have hzK : (f (z : D) : RatFunc ℚ) ≠ 0 :=
    fun h => hzB (Subtype.ext h)
  refine ⟨z', (fun j => (v.value (.primary j) (z : D) : ℤ)), hzK,
    hhorizontal z hzD hz.limit_zero hz.outside_zero,
    hguards z hzD hz.outside_zero, hprimary z hzD, ?_, ?_, ?_⟩
  · intro j
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (hz.primary_bound j)⟩
  · obtain ⟨j, hj⟩ := hz.nonempty_support
    refine ⟨j, ?_⟩
    change (v.value (.primary j) (z : D) : ℤ) ≠ 0
    exact_mod_cast Nat.ne_of_gt hj
  · intro j hj
    simp only [hz.prefix_zero j hj, Nat.cast_zero]


end UnconditionalCounterexample.UnboundedWords
