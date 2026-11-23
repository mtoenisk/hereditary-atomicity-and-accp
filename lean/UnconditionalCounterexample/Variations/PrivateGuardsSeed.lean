import UnconditionalCounterexample.Variations.PrivateGuardsLifts

/-! # Smooth local data for each auxiliary factor -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial GuardSupport

/-- Rational polynomial evaluated at an actual integral p-adic tuple. -/
def value {r : ℕ} (p : PrimeIndex) (a : Fin r → ℤ_[p.val]) (f : MvPolynomial (Fin r) ℚ) :
    ℚ_[p.val] := aeval (fun i => (a i).val) f

/-- Finite local data obtained by embedding the field of definition of a
smooth point and an ordinary point above the same rational prime. -/
structure SmoothSeed {r : ℕ} (p : PrimeIndex) (G : MvPolynomial (Fin (r+1)) ℚ)
    (tests : Finset (MvPolynomial (Fin (r+1)) ℚ)) where
  privatePoint : Fin (r+1) → ℤ_[p.val]
  ordinaryPoint : Fin (r+1) → ℤ_[p.val]
  direction : Fin (r+1)
  distinct : PadicInt.toZMod (privatePoint 0) ≠ PadicInt.toZMod (ordinaryPoint 0)
  root : value p privatePoint G = 0
  partial_norm : ‖value p privatePoint (pderiv direction G)‖ = 1
  ordinary_norm : ‖value p ordinaryPoint G‖ = 1
  private_tests : ∀ f ∈ tests, ‖value p privatePoint f‖ = 1
  ordinary_tests : ∀ f ∈ tests, ‖value p ordinaryPoint f‖ = 1
  integral_coeffs : ∀ f, f = G ∨ f ∈ tests → ∀ q ∈ f.coeffs, ‖(q : ℚ_[p.val])‖ ≤ 1

end UnconditionalCounterexample.Variations.PrivateGuards
