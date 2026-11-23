import UnconditionalCounterexample.Variations.PrivateGuardsUnits
import UnconditionalCounterexample.Variations.PrivateGuardsListedWords
import UnconditionalCounterexample.Variations.PrivateGuardsLocal

/-! # The joint chronological main and puncture history -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection

structure MainChoice (r n : ℕ) (M : Type*) where
  entry : Entry r M
  irreducible : Irreducible (entry.raw n)
  reserved : Finset PrimeIndex

structure Round (r n : ℕ) (M : Type*) extends MainChoice r n M where
  puncture : Poly r
  irreducible_puncture : Irreducible puncture
  prime : PrimeIndex
  checked : Finset (Poly r)
  pair : Pair prime puncture checked

abbrev History (r : ℕ) (M : ℕ → Type*) (n : ℕ) := (j : Fin n) → Round r j.val (M j.val)

variable {r n : ℕ} {M : ℕ → Type*}

def oldDenominator (h : History r M n) : Poly r :=
  ∏ j : Fin n, ((h j).entry.raw j.val * (h j).puncture) ^ mixedPower n

theorem oldDenominator_ne_zero (h : History r M n) : oldDenominator h ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _
    (mul_ne_zero (h j).irreducible.ne_zero (h j).irreducible_puncture.ne_zero)

def UnitsAt (h : History r M n) (f : Poly r) : Prop :=
  ∀ j : Fin n, ∀ b : Bool, ‖aeval ((h j).pair.point b) f /
    aeval ((h j).pair.point b) (oldDenominator h)‖ = 1

end UnconditionalCounterexample.Variations.PrivateGuards.Live
