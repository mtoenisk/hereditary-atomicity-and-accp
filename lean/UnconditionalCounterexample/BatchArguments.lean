import UnconditionalCounterexample.CombinedGuardStep
import UnconditionalCounterexample.ConstructionWords

/-!
# The actual branches for a finite processing batch

Index the processed primes by their position in the increasing enumeration.
The primary and guard then have the same coefficient field. The primary has
positive valuation and the guard is a unit, so they are distinct, including
at the first prime. This gives the branch inputs of the finite word choice.
-/

noncomputable section
namespace UnconditionalCounterexample.CombinedGuardStep

open PrimaryChoices GuardSupport

/-- Index by the position of a prime, so the chosen primary has the
correct coefficient field without transport. -/
def Batch.indices (B : Batch) : Finset ℕ :=
  B.processed.primes.map primes.symm.toEquiv.toEmbedding

@[simp] theorem Batch.mem_indices (B : Batch) (j : ℕ) :
    j ∈ B.indices ↔ primes j ∈ B.processed.primes := by
  simp [Batch.indices]

def Batch.primeAt (B : Batch) (j : B.indices) : ℕ := (primes j.val).val

instance (B : Batch) (j : B.indices) : Fact (B.primeAt j).Prime := primeFact (primes j.val)

def Batch.guardAt (B : Batch) (j : B.indices) :=
  B.processed.guard (primes j.val) ((B.mem_indices _).mp j.property)

def Batch.branch (B : Batch) (j : B.indices) (b : Bool) : ℚ_[B.primeAt j] :=
  if b then (B.guardAt j).value.val else (primary j.val).val

theorem Batch.branch_transcendental (B : Batch) (j : B.indices) (b : Bool) :
    Transcendental ℚ (B.branch j b) := by
  cases b
  · exact primary_transcendental j.val
  · exact (B.guardAt j).transcendental

theorem primary_not_unit (i : ℕ) : ¬ IsUnit (primary i) := by
  have hv : 0 < (primary i).val.valuation := by
    rw [primary_valuation, order]
    split <;> decide
  have hne : (primary i).val ≠ 0 := by intro h; simp [h] at hv
  apply PadicInt.not_isUnit_iff.mpr
  change ‖(primary i).val‖ < 1
  rw [Padic.norm_eq_zpow_neg_valuation hne]
  exact (zpow_lt_one_iff_right₀ (by exact_mod_cast (primes i).property.one_lt)).mpr (by omega)

theorem Batch.branch_ne (B : Batch) (j : B.indices) : B.branch j false ≠ B.branch j true := by
  intro heq
  have h : primary j.val = (B.guardAt j).value := Subtype.ext heq
  exact primary_not_unit j.val (h ▸ (B.guardAt j).unit)

theorem Batch.choice_nonempty (B : Batch) {n : ℕ} {P : ℕ → Polynomial ℚ} {oldE : ℕ → ℕ}
    (plan : ConstructionWords.DegreePlan n P oldE)
    (hP : ∀ j < n, (P j).Monic)
    (v : ∀ i : B.indices, Bool → ℚ_[B.primeAt i]) (kv : B.indices → Bool → ℕ)
    (hv : ∀ i b, v i b ≠ 0) :
    Nonempty (ConstructionWords.Choice B.primeAt B.auxiliary.val plan B.branch v kv) := by
  apply ConstructionWords.choice_nonempty _ _ _ _ _ _ _ _ hP
    B.branch_transcendental B.branch_ne hv
  · exact Subtype.val_injective.comp (primes.injective.comp Subtype.val_injective)
  · intro i h
    apply B.auxiliary_fresh
    have heq : primes i.val = B.auxiliary := Subtype.ext h
    exact heq ▸ (B.mem_indices _).mp i.property

end UnconditionalCounterexample.CombinedGuardStep
