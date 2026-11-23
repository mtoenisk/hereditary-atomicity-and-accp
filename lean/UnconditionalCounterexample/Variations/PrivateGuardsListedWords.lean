import UnconditionalCounterexample.Variations.PrivateGuardsWords
import UnconditionalCounterexample.Variations.MultivariateSelectionWords

/-!
# The enlarged denominators of the actual listed words

Place the main and auxiliary irreducibles at slots 2j and 2j+1. A main
word at stage n is a bounded word at slot 2n whose older odd-slot exponents
are zero. The single-numerator expansion therefore applies unchanged, and
its denominator is divisible by every earlier main and auxiliary polynomial.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open RawWords MultivariateSelection

def interleave {L : Type*} (F G : ℕ → L) (n : ℕ) : L :=
  if n % 2 = 0 then F (n/2) else G (n/2)

@[simp] theorem interleave_even {L : Type*} (F G : ℕ → L) (j : ℕ) :
    interleave F G (2*j) = F j := by simp [interleave]

@[simp] theorem interleave_odd {L : Type*} (F G : ℕ → L) (j : ℕ) :
    interleave F G (2*j+1) = G j := by
  simp [interleave, Nat.add_div]

private theorem range_pairs {L : Type*} [CommMonoid L] (f : ℕ → L) (n : ℕ) :
    (∏ j ∈ Finset.range (2*n), f j) = ∏ j ∈ Finset.range n, (f (2*j) * f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 from by omega, Finset.prod_range_succ,
      Finset.prod_range_succ, ih, Finset.prod_range_succ, mul_assoc]

/-- One global choice of triangular powers works after adjoining the new inverses. -/
def mixedPower (n : ℕ) := normalizationPower (2*n)

private theorem paired_factor {L : Type*} [Field L] (F G : ℕ → L) (n : ℕ) :
    normalizedFactor (interleave F G) normalizationPower (2*n) = normalizedMain F G mixedPower n := by
  simp only [normalizedFactor,normalizedMain,mixedPower,interleave_even,range_pairs,
    interleave_odd, mul_pow]

private theorem liftedWord_exists {n : ℕ} (w : BoundedWord n) :
    ∃ u : BoundedWord (2*n), (∀ j < 2*n, u.oldExponent j = interleave w.oldExponent (fun _ => 0) j) ∧
      u.latestExponent = w.latestExponent := by
  apply stageWord_covers
  · intro j _
    have h := w.oldExponent_bounds (j/2)
    unfold interleave
    split <;> dsimp <;> constructor <;> omega
  · have h := w.latestExponent_bounds
    omega

def liftedWord {n : ℕ} (w : BoundedWord n) : BoundedWord (2*n) := (liftedWord_exists w).choose

/-- The enlarged polynomial denominator fixed at stage n before choosing its
new main numerator. -/
def mixedDenominator {L : Type*} [CommMonoid L] (F G : ℕ → L) {n : ℕ} (w : BoundedWord n) : L :=
  denominator (interleave F G) (liftedWord w)

theorem main_dvd_mixedDenominator {L : Type*} [CommMonoid L] (F G : ℕ → L)
    {n j : ℕ} (w : BoundedWord n) (hj : j < n) : F j ∣ mixedDenominator F G w := by
  simpa only [interleave_even, mixedDenominator] using dvd_denominator (interleave F G) (liftedWord w)
    (j := 2*j) (by omega)

theorem auxiliary_dvd_mixedDenominator {L : Type*} [CommMonoid L] (F G : ℕ → L)
    {n j : ℕ} (w : BoundedWord n) (hj : j < n) : G j ∣ mixedDenominator F G w := by
  simpa only [interleave_odd, mixedDenominator] using dvd_denominator (interleave F G) (liftedWord w)
    (j := 2*j+1) (by omega)

/-- The original normalized main word is literally the latest main numerator
power divided by the enlarged denominator. No auxiliary numerator occurs. -/
theorem normalized_main_word_fraction {A L : Type*} [CommRing A] [Field L]
    (f : A →+* L) (F G : ℕ → A) (hf : ∀ j, f (F j) ≠ 0) (hg : ∀ j, f (G j) ≠ 0)
    {n : ℕ} (w : BoundedWord n) :
    let W := normalizedMain (f ∘ F) (f ∘ G) mixedPower
    W n ^ w.latestExponent * (∏ j ∈ Finset.range n, W j ^ w.oldExponent j) =
      f (F n ^ w.latestExponent) / f (mixedDenominator F G w) := by
  let P := interleave F G
  have hmap : (fun j => f (P j)) = interleave (f ∘ F) (f ∘ G) := by
    funext j
    unfold P interleave
    split <;> rfl
  have hP (i : ℕ) : f (P i) ≠ 0 := by
    unfold P interleave
    split <;> first | apply hf | apply hg
  obtain ⟨hu,hnew⟩ := (liftedWord_exists w).choose_spec
  change (∀ j < 2*n, (liftedWord w).oldExponent j = _) at hu
  change (liftedWord w).latestExponent = _ at hnew
  have h := word_eq_fraction f P hP (liftedWord w)
  dsimp only at h ⊢
  rw [hmap, paired_factor,hnew,range_pairs] at h
  have hprod : (∏ j ∈ Finset.range n, normalizedMain (f ∘ F) (f ∘ G) mixedPower j ^ w.oldExponent j) =
      ∏ j ∈ Finset.range n,
        (normalizedFactor (interleave (f ∘ F) (f ∘ G)) normalizationPower (2*j) ^ (liftedWord w).oldExponent (2*j) *
        normalizedFactor (interleave (f ∘ F) (f ∘ G)) normalizationPower (2*j+1) ^ (liftedWord w).oldExponent (2*j+1)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hlt := Finset.mem_range.mp hj
    rw [hu _ (by omega),hu _ (by omega),interleave_even,interleave_odd,zpow_zero,mul_one,paired_factor]
  rw [← hprod] at h
  simpa only [P,interleave_even,mixedDenominator] using h

end UnconditionalCounterexample.Variations.PrivateGuards
