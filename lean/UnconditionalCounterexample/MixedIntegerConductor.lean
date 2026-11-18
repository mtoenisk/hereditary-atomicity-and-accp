import UnconditionalCounterexample.MixedWordEstimates
import UnconditionalCounterexample.SparseGenericRecovery

/-!
# The integer conductor in the constructed sparse-primary domains

The same extracted sequence supplies generic recovery and both kinds of local
conductor. The resulting statement preserves every prescribed positive integer
that clears the original coordinate. Every construction, profile, extraction and local-estimate input is supplied
by the actual mixed sequence; no conditional realization premise remains.
-/

namespace UnconditionalCounterexample.MixedIntegerConductor

open GuardSupport MixedConstruction

variable (S : Set PrimeIndex) (hS : S.Infinite)

theorem integer_conductor
    (T : Subring (domain S hS)) (x : T) (hx : x ≠ 0)
    (hu : ¬ Factorization.HasBoundedFactorizations x) :
    (∃ n : ℕ, 0 < n ∧ (n : domain S hS) * MixedConductor.coordinate S hS ∈ T) ∧
      ∀ n : ℕ, 0 < n → (n : domain S hS) * MixedConductor.coordinate S hS ∈ T →
        ∀ z : domain S hS, (n : domain S hS) * z ∈ T := by
  obtain ⟨r, _, y, stage, w, _, hstage, hbound, _, hword⟩ :=
    SparseGenericRecovery.exists_listed_sequence_of_unbounded S hS T x hx hu
  exact MixedConductor.integer_conductor_of_listed_sequence S hS
    (MixedWordEstimates.wordEstimates S hS) T y stage hstage w (2 * r) hbound hword

theorem exists_integer_conductor
    (T : Subring (domain S hS)) (hT : ¬ Factorization.IsBFDomain T) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : domain S hS, (n : domain S hS) * z ∈ T := by
  classical
  unfold Factorization.IsBFDomain at hT
  push Not at hT
  obtain ⟨x, hx, hu⟩ := hT
  obtain ⟨⟨n, hn, hnt⟩, hall⟩ := integer_conductor S hS T x hx hu
  exact ⟨n, hn, hall n hn hnt⟩

end UnconditionalCounterexample.MixedIntegerConductor
