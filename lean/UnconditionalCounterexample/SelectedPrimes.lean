import UnconditionalCounterexample.PrimaryChoices
import Mathlib.Order.Filter.Cofinite

/-!
# Increasing selected primes and their primary arguments

Any infinite subset of rational primes has an actual increasing enumeration
with exactly that range, together with an order equivalence onto the selected
subtype. Finite sets of primes have finite preimages, so the enumeration
eventually avoids each such set.

For any prime sequence, p-adic approximation supplies primary
arguments transcendental over Q, with valuation two at index zero and one at
all later indices.
-/

noncomputable section
namespace UnconditionalCounterexample.SelectedPrimes
open GuardSupport

/-- The selected primes, as an infinite subset of the natural numbers. -/
def naturals (S : Set PrimeIndex) : Set ℕ := Subtype.val '' S

theorem naturals_infinite (S : Set PrimeIndex) (hS : S.Infinite) : (naturals S).Infinite :=
  hS.image Subtype.val_injective.injOn

def natEnumeration (S : Set PrimeIndex) (hS : S.Infinite) : ℕ ≃o naturals S :=
  @Nat.Subtype.orderIsoOfNat (naturals S) (naturals_infinite S hS).to_subtype

/-- Increasing enumeration of precisely the selected prime set. -/
def primes (S : Set PrimeIndex) (hS : S.Infinite) (n : ℕ) : PrimeIndex :=
  ⟨(natEnumeration S hS n).val, by
    obtain ⟨p, _, hp⟩ := (natEnumeration S hS n).property
    exact hp ▸ p.property⟩

@[simp] theorem primes_val (S : Set PrimeIndex) (hS : S.Infinite) (n : ℕ) :
    (primes S hS n).val = (natEnumeration S hS n).val := rfl

theorem primes_mem (S : Set PrimeIndex) (hS : S.Infinite) (n : ℕ) : primes S hS n ∈ S := by
  obtain ⟨p, hp, heq⟩ := (natEnumeration S hS n).property
  have heq' : primes S hS n = p := Subtype.ext heq.symm
  exact heq' ▸ hp

theorem primes_strictMono (S : Set PrimeIndex) (hS : S.Infinite) : StrictMono (primes S hS) := by
  intro m n hmn
  exact (natEnumeration S hS).strictMono hmn

theorem primes_injective (S : Set PrimeIndex) (hS : S.Infinite) :
    Function.Injective (primes S hS) := (primes_strictMono S hS).injective

theorem range_primes (S : Set PrimeIndex) (hS : S.Infinite) : Set.range (primes S hS) = S := by
  ext p
  constructor
  · rintro ⟨n, rfl⟩
    exact primes_mem S hS n
  · intro hp
    obtain ⟨n, hn⟩ := (natEnumeration S hS).surjective ⟨p.val, p, hp, rfl⟩
    exact ⟨n, Subtype.ext (congrArg (fun z : naturals S => z.val) hn)⟩

/-- The same increasing enumeration as an equivalence onto the selected subtype. -/
def orderIso (S : Set PrimeIndex) (hS : S.Infinite) : ℕ ≃o S where
  toEquiv := Equiv.ofBijective (fun n => ⟨primes S hS n, primes_mem S hS n⟩)
    ⟨fun _ _ h => primes_injective S hS (congrArg Subtype.val h), by
      intro p
      have hp : p.val ∈ Set.range (primes S hS) := by rw [range_primes]; exact p.property
      obtain ⟨n, hn⟩ := hp
      exact ⟨n, Subtype.ext hn⟩⟩
  map_rel_iff' := by
    intro m n
    exact (primes_strictMono S hS).le_iff_le

theorem finite_preimage (S : Set PrimeIndex) (hS : S.Infinite)
    (T : Set PrimeIndex) (hT : T.Finite) : ((primes S hS) ⁻¹' T).Finite :=
  hT.preimage (primes_injective S hS).injOn

theorem tendsto_cofinite (S : Set PrimeIndex) (hS : S.Infinite) :
    Filter.Tendsto (primes S hS) Filter.atTop Filter.cofinite := by
  simpa only [Nat.cofinite_eq_atTop] using (primes_injective S hS).tendsto_cofinite

theorem eventually_not_mem (S : Set PrimeIndex) (hS : S.Infinite)
    (T : Set PrimeIndex) (hT : T.Finite) : ∀ᶠ n in Filter.atTop, primes S hS n ∉ T :=
  (tendsto_cofinite S hS).eventually hT.eventually_cofinite_notMem

theorem exists_cutoff_avoiding (S : Set PrimeIndex) (hS : S.Infinite)
    (T : Set PrimeIndex) (hT : T.Finite) : ∃ N, ∀ n ≥ N, primes S hS n ∉ T :=
  Filter.eventually_atTop.mp (eventually_not_mem S hS T hT)

section Primary
variable (p : ℕ → PrimeIndex)

/-- Primary arguments require only the selected prime at each index. -/
theorem exists_primary (j : ℕ) : ∃ z : ℤ_[(p j).val],
    Transcendental ℚ z.val ∧ z.val.valuation = PrimaryChoices.order j := by
  obtain ⟨x, ht, _, hv⟩ :=
    EvaluationChoices.exists_transcendental_valuation (p j).val (PrimaryChoices.order j)
  have h : 0 ≤ PrimaryChoices.order j := by
    unfold PrimaryChoices.order
    split <;> decide
  exact ⟨⟨x, (Padic.norm_le_one_iff_val_nonneg x).mpr (hv ▸ h)⟩, ht, hv⟩

def primary (j : ℕ) : ℤ_[(p j).val] := (exists_primary p j).choose

theorem primary_transcendental (j : ℕ) : Transcendental ℚ (primary p j).val :=
  (exists_primary p j).choose_spec.1

theorem primary_valuation (j : ℕ) :
    (primary p j).val.valuation = PrimaryChoices.order j :=
  (exists_primary p j).choose_spec.2

@[simp] theorem primary_zero : (primary p 0).val.valuation = 2 := primary_valuation p 0

theorem primary_late (j : ℕ) (hj : 0 < j) : (primary p j).val.valuation = 1 := by
  rw [primary_valuation]
  simp [PrimaryChoices.order, Nat.ne_of_gt hj]

end Primary
end UnconditionalCounterexample.SelectedPrimes
