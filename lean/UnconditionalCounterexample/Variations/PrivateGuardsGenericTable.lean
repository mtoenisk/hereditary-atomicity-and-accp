import UnconditionalCounterexample.Variations.PrivateGuardsGenericLive
import UnconditionalCounterexample.Variations.PrivateGuardsTableFamily

/-! # Generic geometric recovery for combined local tables -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MultivariateSelection

variable {r : ℕ} {M : ℕ → Type} {K : Type} [Field K] [CharZero K] [IsAlgClosed K]

/-- A stage prescription containing the generic tests and passing their degree bound
satisfies the recovery criterion on the very same recursive sequence. -/
theorem ruleOfTable_meets (c : Fin (r+1) → ℚ) (P : ∀ n (h : History r M n)
    (_ : Function.Injective (fun j => (h j).prime.val)), TablePrescription K h)
    (floor : ∀ n h hinj, genericDegreeFloor h < (P n h hinj).degree)
    (tests : ∀ n h hinj, genericTests K h ⊆ (P n h hinj).geometry) :
    MeetsGenericTests c K (ruleOfTable c P) := by
  intro n h x hx
  obtain ⟨hinj, hdegree, _, _, _, _, htests, _⟩ := hx
  exact ⟨hdegree ▸ floor n h hinj, fun t ht => htests t (tests n h hinj ht)⟩

/-- The concrete table can retain all geometric tests on the joint history. -/
def genericTablePolicy (r : ℕ) (K : Type) [Field K] [CharZero K] [IsAlgClosed K] : TablePolicy r K where
  floor _ h := genericDegreeFloor h
  geometry _ h := genericTests K h
  valid _ h := genericTests_valid h

variable (K) (q : GuardSupport.PrimeIndex) (c : Fin (r+1) → ℚ)

/-- The public and private local interpolation tables meet every scheduled geometric test. -/
theorem genericTablePolicy_meets : MeetsGenericTests c K (tableRule (genericTablePolicy r K) q c) := by
  apply ruleOfTable_meets
  · intro n h hi
    exact Nat.lt_succ_of_le ((le_max_left ..).trans (le_max_right ..))
  · intro n h hi
    exact fun _ he => he

local notation "L" => tableRule (genericTablePolicy r K) q c

/-- Bounded normalized words recover the enlarged generic fibre of the actual
joint table construction. -/
theorem genericTable_recover [Uncountable K] {d : ℕ} (C : Config r d)
    (A : Subalgebra ℚ ((family C L).poleAlgebra (fun n => (event C L n).irreducible)))
    (hwords : {n | ∃ (w : BoundedWord n) (x : A),
      let W := (family C L).generator mixedPower
      (((x : (family C L).poleAlgebra _) : FractionRing (Poly r))) =
        W n ^ w.latestExponent * (∏ j ∈ Finset.range n, W j ^ w.oldExponent j)}.Infinite) : A = ⊤ :=
  recover_pole_of_meets c C L (genericTablePolicy_meets K q c) A hwords

end UnconditionalCounterexample.Variations.PrivateGuards.Live
