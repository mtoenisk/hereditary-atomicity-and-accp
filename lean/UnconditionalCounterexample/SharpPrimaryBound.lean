import UnconditionalCounterexample.EscapingProfiles
import Mathlib.Order.Lattice.Nat

/-!
# The exact primary supremum in Lemma 5.1

Eventual stabilization bounds the primary orders of a nonzero element. Their
literal natural supremum is the least such bound. Escaping-divisor extraction
retains the same divisor and uses its actual divisibility into the fixed top
to replace the auxiliary bound by this exact supremum. Unbounded factorization
forces the supremum to be positive.
-/

namespace UnconditionalCounterexample

universe u v

namespace ValuationProfiles

variable {R : Type u} {ι : Type v} [CommRing R] [IsDomain R]

/-- The paper's exact primary bound, rather than a chosen larger bound. -/
noncomputable def primarySup (v : ValuationProfiles R ι) (x : R) : ℕ :=
  sSup (Set.range (fun j => v.value (.primary j) x))

/-- Eventual stabilization makes the primary range of a nonzero element bounded. -/
theorem primary_values_bddAbove (v : ValuationProfiles R ι)
    {x : R} (hx : x ≠ 0) : BddAbove (Set.range (fun j => v.value (.primary j) x)) := by
  obtain ⟨r, _, hr⟩ := v.exists_positive_primary_bound hx
  refine ⟨r, ?_⟩
  rintro z ⟨j, rfl⟩
  exact hr j

/-- Every primary order of a nonzero element is at most its exact supremum. -/
theorem primary_le_primarySup (v : ValuationProfiles R ι) {x : R} (hx : x ≠ 0) (j : ℕ) :
    v.value (.primary j) x ≤ v.primarySup x :=
  le_csSup (v.primary_values_bddAbove hx) ⟨j, rfl⟩

/-- The supremum is no larger than any common primary bound. -/
theorem primarySup_le (v : ValuationProfiles R ι) (x : R) (r : ℕ)
    (hr : ∀ j, v.value (.primary j) x ≤ r) : v.primarySup x ≤ r := by
  apply csSup_le (Set.range_nonempty _)
  rintro z ⟨j, rfl⟩
  exact hr j

/-- Exact least-upper-bound formulation for the primary profile. -/
theorem primarySup_le_iff (v : ValuationProfiles R ι) {x : R} (hx : x ≠ 0) (r : ℕ) :
    v.primarySup x ≤ r ↔ ∀ j, v.value (.primary j) x ≤ r := by
  constructor
  · intro h j
    exact (v.primary_le_primarySup hx j).trans h
  · exact v.primarySup_le x r

/-- Reuse the actual extracted divisor, sharpening its bound by divisibility
into the fixed top. No new divisor or enlargement of the supremum is chosen. -/
theorem exists_escaping_primary_divisor_sup
    (v : ValuationProfiles R ι) (T : Subring R)
    (hunit : ∀ y : T, IsUnit (y : R) → IsUnit y)
    (x : T) (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x)
    (N : ℕ) :
    ∃ y : T, IsEscapingPrimaryDivisor v T x y (v.primarySup (x : R)) N := by
  obtain ⟨r, _, hextract⟩ := v.exists_escaping_primary_divisors T hunit hx hunbounded
  obtain ⟨y, hy⟩ := hextract N
  have hxR : (x : R) ≠ 0 := fun h => hx (Subtype.ext h)
  have hydvdR : (y : R) ∣ (x : R) := by
    obtain ⟨z, hz⟩ := hy.dvd_top
    exact ⟨z, congrArg Subtype.val hz⟩
  refine ⟨y, { hy with primary_bound := ?_ }⟩
  intro j
  exact (v.value_le_of_dvd (.primary j) hxR hydvdR).trans (v.primary_le_primarySup hxR j)

/-- Unbounded factorization forces the exact primary supremum to be positive. -/
theorem primarySup_pos_of_unbounded
    (v : ValuationProfiles R ι) (T : Subring R)
    (hunit : ∀ y : T, IsUnit (y : R) → IsUnit y)
    (x : T) (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    0 < v.primarySup (x : R) := by
  obtain ⟨y, hy⟩ := v.exists_escaping_primary_divisor_sup T hunit x hx hunbounded 0
  obtain ⟨j, hj⟩ := hy.nonempty_support
  exact hj.trans_le (hy.primary_bound j)

end ValuationProfiles
end UnconditionalCounterexample
