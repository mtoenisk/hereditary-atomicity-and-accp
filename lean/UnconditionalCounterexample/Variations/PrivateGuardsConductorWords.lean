import UnconditionalCounterexample.Variations.PrivateGuardsGenericTable
import UnconditionalCounterexample.Variations.PrivateGuardsEvaluated
import UnconditionalCounterexample.LocalAlgebra.TorsionDescent

/-! # The actual cleared words for the integral conductor on a punctured table -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultivariateSelection LocalAlgebra

variable {r d n : ℕ} {M : ℕ → Type*} {c : Fin (r+1) → ℚ} (C : Config r d) (R : Rule r M c)

abbrev actualDenominators := inverted (Set.range (main C R)) (puncture C R)

abbrev actualPole := (family C R).poleAlgebra (fun n => (event C R n).irreducible)

theorem wordDen_before (w : BoundedWord n) :
    wordDen (before C R n) w = mixedDenominator (main C R) (puncture C R) w := by
  unfold wordDen mixedDenominator denominator
  apply Finset.prod_congr rfl
  intro j hj
  have hlt := Finset.mem_range.mp hj
  have he : interleave (prefixMain (before C R n)) (prefixPuncture (before C R n)) j =
      interleave (main C R) (puncture C R) j := by
    unfold interleave
    split <;> simp [prefixMain,prefixPuncture,show j/2 < n by omega,before,main,puncture]
  rw [he]

/-- Actual bounded words supplied by an unbounded-length source subring. -/
def HasMixedWords (T : Subring (actualPole C R)) :=
  ∃ b : ℕ, {n : ℕ | ∃ w : BoundedWord n, w.latestExponent ≤ b ∧ ∃ x ∈ T,
    let W := (family C R).generator mixedPower
    (x : FractionRing (Poly r)) = W n ^ w.latestExponent * (∏ j ∈ Finset.range n, W j ^ w.oldExponent j)}.Infinite

def HasClearedMixedWords (T : Subring (actualPole C R)) :=
  ∃ b : ℕ, {n : ℕ | ∃ w : BoundedWord n, w.latestExponent ≤ b ∧ ∃ x ∈ T,
    algebraMap (Poly r) (actualPole C R) (main C R n ^ w.latestExponent) =
      algebraMap (Poly r) (actualPole C R) (wordDen (before C R n) w) * x}.Infinite

theorem HasMixedWords.cleared {T : Subring (actualPole C R)} (h : HasMixedWords C R T) :
    HasClearedMixedWords C R T := by
  obtain ⟨b,hb⟩ := h
  refine ⟨b,hb.mono ?_⟩
  rintro n ⟨w,hw,x,hx,hword⟩
  let φ := algebraMap (Poly r) (FractionRing (Poly r))
  have hφ := IsFractionRing.injective (Poly r) (FractionRing (Poly r))
  have hF (n : ℕ) : φ (main C R n) ≠ 0 := (map_ne_zero_iff _ hφ).mpr (event C R n).irreducible.ne_zero
  have hG (n : ℕ) : φ (puncture C R n) ≠ 0 := (map_ne_zero_iff _ hφ).mpr (event C R n).irreducible_puncture.ne_zero
  have hH : φ (mixedDenominator (main C R) (puncture C R) w) ≠ 0 := by
    rw [← wordDen_before C R w]
    exact (map_ne_zero_iff _ hφ).mpr (wordDen_ne_zero _ _)
  have he := ((eq_div_iff hH).mp (hword.trans (normalized_main_word_fraction φ _ _ hF hG w))).symm
  refine ⟨w,hw,x,hx,Subtype.ext ?_⟩
  rw [wordDen_before]
  exact he.trans (mul_comm ..)

variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
  (q : PrimeIndex) (c : Fin (r+1) → ℚ)
local notation "L" => tableRule (genericTablePolicy r K) q c

theorem mixed_hull_eq_top (T : Subring (actualPole C L)) (h : HasMixedWords C L T) :
    RationalHull.hull T = ⊤ := by
  apply genericTable_recover K q c C
  obtain ⟨_,hb⟩ := h
  refine hb.mono ?_
  rintro n ⟨w,_,x,hx,he⟩
  exact ⟨w,⟨x,Algebra.subset_adjoin hx⟩,he⟩

end UnconditionalCounterexample.Variations.PrivateGuards.Live
