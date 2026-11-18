import UnconditionalCounterexample.RationalSigns
import UnconditionalCounterexample.StageExponents
import UnconditionalCounterexample.PrimaryWordProfiles

/-!
# Actual bounded listed words from valuation data

Principal factorization and guard values produce the actual signed normalized
word. Actual primary generator valuations produce its profile formulas, and
StageExponents selects one actual sequence in the original subring. The fixed
bounds latest<=2r and |oldExponent|<=2r are retained for the conductor argument.
-/

namespace UnconditionalCounterexample.EscapingWords

open Polynomial Filter NormalizedWords RawWords WithZero

noncomputable local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

local instance primeFact (p : {p : ℕ // p.Prime}) : Fact p.val.Prime := ⟨p.property⟩

/-- Actual pole-algebra units with zero guard values and bounded effective
primary valuations produce one actual subring sequence of listed words. Neither
a principal representation nor its profile formulas are assumed for the elements. -/
theorem exists_listed_sequence_of_valuation_data
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
    (T : Subring (PoleAlgebra.generated (Set.range F))) (r : ℕ)
    (hextract : ∀ N : ℕ, ∃ y : T, ∃ g : ℕ → ℤ,
      ((y : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) ≠ 0 ∧
      (((y : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ)⁻¹ ∈
        PoleAlgebra.generated (Set.range F)) ∧
      (∀ p, @Padic.mulValuation p.val ⟨p.property⟩
        (guard p ((y : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ)) = 1) ∧
      (∀ j, primary j ((y : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) = exp (-g j)) ∧
      (∀ j, 0 ≤ g j ∧ g j ≤ r) ∧ (∃ j, g j ≠ 0) ∧
      ∀ j, j < 2 * N + 2 → g j = 0) :
    ∃ y : ℕ → T, ∃ stage : ℕ → ℕ, ∃ w : ∀ i, StageWord (stage i) (stage i + 1),
      (∀ i, i < stage i) ∧ Tendsto stage atTop atTop ∧
      (∀ i, (w i).latestExponent ≤ 2 * r) ∧
      (∀ i j, |(w i).oldExponent j| ≤ (2 * r : ℕ)) ∧ ∀ i,
        ((y i : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) =
          normalizedFactor (fun j => algebraMap ℚ[X] (RatFunc ℚ) (F j)) E (stage i) ^
            (w i).latestExponent *
          (∏ j ∈ Finset.range (stage i),
            normalizedFactor (fun k => algebraMap ℚ[X] (RatFunc ℚ) (F k)) E j ^
              (w i).oldExponent j) := by
  let W := normalizedFactor (fun j => algebraMap ℚ[X] (RatFunc ℚ) (F j)) E
  apply StageExponents.exists_bounded_escaping_listed_sequence
    (PoleAlgebra.generated (Set.range F)).toSubring.subtype T W r
  intro N
  obtain ⟨y, g, hy0, hyinv, hyguard, hyvalue, hybound, hynonempty, hyprefix⟩ := hextract N
  obtain ⟨e, he⟩ := RationalSigns.exists_signed_normalized_factorization F hF hinj E
    ((y : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) hy0
    (y : PoleAlgebra.generated (Set.range F)).property hyinv guard hyguard hguard
  refine ⟨y, e, g, he, ?_, hybound, hynonempty, hyprefix⟩
  exact PrimaryWordProfiles.represents_of_generator_profiles primary W hb hq e
    ((y : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) g he hyvalue

end UnconditionalCounterexample.EscapingWords
