import UnconditionalCounterexample.Variations.DyadicAxis
import UnconditionalCounterexample.Variations.SplitConductor

/-!
# The dyadic example conditional on realization, conductor, and splitting

The same realized profiles control the pair obstruction and the finite bounds
needed to factor elements in every unital subring. The simultaneous arithmetic
construction must still supply the realization and the stated conductor and
splitting properties on one ring.
-/

namespace UnconditionalCounterexample.DyadicProfiles.Realization

variable {R E : Type*} [CommRing R] [IsDomain R] (D : Realization R E)

/-- Conditional joint statement for the dyadic construction. Each common
divisor of the named nonzero pair grows strictly, and every unital subring
of the same ring is atomic. -/
theorem dyadic_conclusion
    (hsign : ∀ u : R, IsUnit u → u = 1 ∨ u = -1)
    (hfinite : ∀ x : R, x ≠ 0 → (Function.support (D.extra x)).Finite)
    (hindex : ∀ T : Subring R, ¬ Factorization.IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z : R, (m : R) * z ∈ T)
    (hsplit : ∀ (x : R) (m : ℕ), x ≠ 0 → 0 < m →
      0 < (D.regular x).height false → 0 < (D.regular x).height true →
      ∃ (u v : R) (a b : ℕ), x = u * v ∧ (D.regular u).height true = 0 ∧
        (D.regular v).height false = 0 ∧ m = a * b ∧ a.Coprime b ∧
        (a : R) ∣ u - 1 ∧ (b : R) ∣ v - 1) :
    Factorization.IsHereditarilyAtomic R ∧ D.pairEntry false ≠ 0 ∧ D.pairEntry true ≠ 0 ∧
    (∀ e : R, e ∣ D.pairEntry false → e ∣ D.pairEntry true →
      ∃ u : R, ¬ IsUnit u ∧ e * u ∣ D.pairEntry false ∧ e * u ∣ D.pairEntry true) ∧
    ¬ Factorization.IsStronglyAtomicDomain R ∧ ¬ Factorization.IsWeakACCP R := by
  classical
  refine ⟨DyadicSplit.hereditarilyAtomic_of_axis_splits
    (fun x => (D.regular x).height false) (fun x => (D.regular x).height true)
    hindex ?_ hsplit, (D.pairEntry_spec false).1, (D.pairEntry_spec true).1,
    fun _ => D.pair_extension, D.pair_obstruction.2⟩
  intro T x hx haxis
  exact D.subring_bounded_of_axis hsign T x hx (hfinite x (fun h => hx (Subtype.ext h))) haxis

end UnconditionalCounterexample.DyadicProfiles.Realization
