import UnconditionalCounterexample.Variations.PrivateGuardsFamily
import UnconditionalCounterexample.Variations.PrivateGuardsWords
import UnconditionalCounterexample.Variations.MultiDomainLowWords

/-!
# Isolation of auxiliary inverted factors in the genuine punctured pole algebra

Unique factorization in the multivariate polynomial ring gives the raw word
for a unit of the actual localization. Triangular normalization incorporates
all earlier punctures in each denominator. The constructed paired valuations
then remove the auxiliary exponents of a unit with equal guard orders.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial GuardSupport DiscreteOrders PrincipalProfiles WithZero
open scoped nonZeroDivisors

variable {r d : ℕ}
local notation "A" => PolynomialRing (r+1)
local notation "K" => FractionRing (PolynomialRing (r+1))

variable {c : Fin (r+1) → ℚ} {raw : ℕ → PolynomialRing (r+1)}
  {tests : ℕ → Finset (PolynomialRing (r+1))}

private theorem regular (F : Family c d (Set.range raw) tests) (hraw : ∀ n, Irreducible (raw n)) :
    inverted (Set.range raw) F.puncture ≤ A⁰ := by
  apply Submonoid.closure_le.mpr
  rintro _ (⟨n,rfl⟩ | ⟨n,rfl⟩)
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (hraw n).ne_zero
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (F.irreducible n).ne_zero

/-- The enlarged localization embedded in the one rational function field. -/
abbrev Family.poleAlgebra (F : Family c d (Set.range raw) tests) (hraw : ∀ n, Irreducible (raw n)) :
    Subalgebra A K := Localization.subalgebra.ofField K (inverted (Set.range raw) F.puncture) (regular F hraw)

theorem Family.pole_dimension (F : Family c d (Set.range raw) tests) (hraw : ∀ n, Irreducible (raw n)) :
    ringKrullDim (F.poleAlgebra hraw) = d := by
  let M := inverted (Set.range raw) F.puncture
  exact (ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv M (F.poleAlgebra hraw)
    (Localization M)).toRingEquiv).trans F.dimension

/-- The normalized main generators in the enlarged field. -/
abbrev Family.generator (F : Family c d (Set.range raw) tests) (E : ℕ → ℕ) (n : ℕ) : K :=
  normalizedMain (fun j => algebraMap A K (raw j)) (fun j => algebraMap A K (F.puncture j)) E n

theorem Family.unit_word (F : Family c d (Set.range raw) tests) (hraw : ∀ n, Irreducible (raw n))
    (E : ℕ → ℕ) (u : (F.poleAlgebra hraw)ˣ) :
    ∃ q : ℚ, q ≠ 0 ∧ ∃ a b : ℕ →₀ ℤ, ((u : F.poleAlgebra hraw) : K) =
      (q : K) * word (F.generator E) a * word (fun j => algebraMap A K (F.puncture j)) b := by
  let all := Sum.elim raw F.puncture
  have he : Set.range all = Set.range raw ∪ Set.range F.puncture := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      cases i with
      | inl n => exact Or.inl ⟨n,rfl⟩
      | inr n => exact Or.inr ⟨n,rfl⟩
    · rintro (⟨n,rfl⟩ | ⟨n,rfl⟩)
      · exact ⟨.inl n,rfl⟩
      · exact ⟨.inr n,rfl⟩
  let : IsLocalization (Submonoid.closure (Set.range all)) (F.poleAlgebra hraw) := by
    rw [he]
    exact inferInstanceAs (IsLocalization (inverted (Set.range raw) F.puncture) (F.poleAlgebra hraw))
  have ha : ∀ i, Irreducible (all i) := by rintro (i|i); exacts [hraw i,F.irreducible i]
  obtain ⟨q,hq,e,hword⟩ := MultiDomain.pole_unit_raw_word_of_isLocalization all (F.poleAlgebra hraw) ha u
  let f (i : ℕ) := algebraMap A K (raw i)
  let g (i : ℕ) := algebraMap A K (F.puncture i)
  have hfg : MultiDomain.fieldPolynomial all = Sum.elim f g := by funext i; cases i <;> rfl
  have hinj := IsFractionRing.injective A K
  obtain ⟨a,b,hab⟩ := normalize_mixed_word f g
    (fun i => (map_ne_zero_iff _ hinj).mpr (hraw i).ne_zero)
    (fun i => (map_ne_zero_iff _ hinj).mpr (F.irreducible i).ne_zero) E e
  refine ⟨q, hq, a, b, ?_⟩
  rw [hfg, hab, ← mul_assoc] at hword
  exact hword

/-- For a genuine horizontal unit with equal values at the paired guards, no
puncture occurs. This requires the normalized main factors to be units at all
the private pairs, including those defined before each main birth. -/
theorem Family.unit_main_word (F : Family c d (Set.range raw) tests) (hraw : ∀ n, Irreducible (raw n))
    (E : ℕ → ℕ) (u : (F.poleAlgebra hraw)ˣ)
    (hm : ∀ n j, F.places.auxiliary n (F.generator E j) = 1 ∧ F.places.ordinary n (F.generator E j) = 1)
    (he : ∀ n, order (F.places.auxiliary n) ((u : F.poleAlgebra hraw) : K) =
      order (F.places.ordinary n) ((u : F.poleAlgebra hraw) : K)) :
    ∃ q : ℚ, q ≠ 0 ∧ ∃ a : ℕ →₀ ℤ, ((u : F.poleAlgebra hraw) : K) = (q : K) * word (F.generator E) a := by
  obtain ⟨q,hq,a,b,h⟩ := F.unit_word hraw E u
  exact ⟨q,hq,a, (eliminate F.places (F.generator E) a b (Rat.cast_ne_zero.mpr hq) h
    (fun n => F.same_constant n q) (fun n j => (hm n j).1) (fun n j => (hm n j).2) he).2⟩

end UnconditionalCounterexample.Variations.PrivateGuards
