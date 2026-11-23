import UnconditionalCounterexample.Variations.DimensionChains
import UnconditionalCounterexample.Variations.DimensionTrdeg
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Dimension bound for subrings of rational function fields

An affine ℤ-domain is built one generator at a time. For an algebraic
generator, a nonzero polynomial in the kernel of evaluation allows a strict
step below every lifted prime chain. The polynomial ring therefore supplies
no dimension increase in this case. Each transcendental adjunction increases
dimension by at most one and increases transcendence degree by at least one.
-/

namespace UnconditionalCounterexample.Variations

open Polynomial Algebra
open scoped nonZeroDivisors

private theorem cancel_krullDim_succ {d : WithBot ℕ∞} {k : ℕ}
    (h : d + 1 ≤ (k : WithBot ℕ∞) + 1) : d ≤ k := by
  cases d with
  | bot => exact bot_le
  | coe d =>
    change (↑(d+1) : WithBot ℕ∞) ≤ ↑((k : ℕ∞)+1) at h
    exact WithBot.coe_le_coe.mpr ((ENat.add_le_add_iff_right (by decide : (1 : ℕ∞) ≠ ⊤)).mp
      (WithBot.coe_le_coe.mp h))

private theorem dim_trdeg_adjoin_step {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (A : Subalgebra ℤ K) [IsNoetherianRing A] (x : K) {n : ℕ}
    (hdim : ringKrullDim A ≤ (n+1 : ℕ)) (htr : (n : Cardinal) ≤ trdeg ℤ A) :
    ∃ m : ℕ, ringKrullDim (adjoin A ({x} : Set K)) ≤ (m+1 : ℕ) ∧
      (m : Cardinal) ≤ trdeg ℤ (adjoin A ({x} : Set K)) := by
  classical
  let B := adjoin A ({x} : Set K)
  let y : B := ⟨x, subset_adjoin rfl⟩
  let f : A[X] →ₐ[A] B := Polynomial.aeval y
  have hsurj : Function.Surjective f := by
    intro z
    have hz := z.property
    change (z : K) ∈ adjoin A {x} at hz
    rw [adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, hp⟩ := hz
    exact ⟨p, Subtype.ext ((Polynomial.aeval_algHom_apply B.val y p).symm.trans hp)⟩
  let : IsScalarTower ℤ A B := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (fun a b hab => Subtype.ext (congrArg B.val hab))
  have ht := trdeg_add_eq ℤ A (A := B)
  have hpoly := (add_le_add_left hdim 1)
  rw [← Polynomial.ringKrullDim_of_isNoetherianRing] at hpoly
  change ∃ m : ℕ, ringKrullDim B ≤ (m+1 : ℕ) ∧ (m : Cardinal) ≤ trdeg ℤ B
  by_cases ha : IsAlgebraic A y
  · obtain ⟨p, hp, hroot⟩ := ha
    have hstrict := ringKrullDim_succ_le_of_surjective f.toRingHom hsurj
      (mem_nonZeroDivisors_of_ne_zero hp) hroot
    refine ⟨n, cancel_krullDim_succ (hstrict.trans hpoly), ?_⟩
    rw [← ht]
    exact htr.trans le_self_add
  · have : Algebra.Transcendental A B := ⟨y, ha⟩
    refine ⟨n+1, ?_, ?_⟩
    · simpa only [Nat.cast_add, Nat.cast_one] using (ringKrullDim_le_of_surjective f.toRingHom hsurj).trans hpoly
    · rw [Nat.cast_succ, ← ht]
      exact add_le_add htr (Cardinal.one_le_iff_pos.mpr (trdeg_pos A B))

/-- Every finitely generated characteristic-zero ℤ-domain admits a dimension
bound by one plus an integer bounded by its absolute transcendence degree. -/
theorem affine_subalgebra_dimension_bound {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (B : Subalgebra ℤ K) (hB : B.FG) :
    ∃ n : ℕ, ringKrullDim B ≤ (n+1 : ℕ) ∧ (n : Cardinal) ≤ trdeg ℤ B := by
  classical
  obtain ⟨s, rfl⟩ := hB
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_, by simp⟩
    let equiv := (Subalgebra.equivOfEq (adjoin ℤ ((∅ : Finset K) : Set K)) ⊥
      (by simp)).trans (Algebra.botEquivOfInjective (Int.castRingHom K).injective_int)
    rw [ringKrullDim_eq_of_ringEquiv equiv.toRingEquiv]
    exact Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
  | insert x s _ ih =>
    let A := adjoin ℤ (s : Set K)
    let : Algebra.FiniteType ℤ A := ⟨(Subalgebra.fg_top _).mpr ⟨s, rfl⟩⟩
    let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
    obtain ⟨n, hdim, htr⟩ := ih
    rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, adjoin_union_eq_adjoin_adjoin]
    exact dim_trdeg_adjoin_step A x hdim htr

/-- A characteristic-zero domain of rational transcendence degree at most `r`
has dimension at most `r+1`. Only finitely generated subalgebras need be tested. -/
theorem ringKrullDim_le_of_int_trdeg {D : Type*} [CommRing D] [IsDomain D] [CharZero D]
    (r : ℕ) (hr : trdeg ℤ D ≤ r) : ringKrullDim D ≤ (r+1 : ℕ) := by
  apply ringKrullDim_le_of_fg_subalgebras (R := ℤ)
  intro B hB
  obtain ⟨n, hn, ht⟩ := affine_subalgebra_dimension_bound B hB
  let : IsScalarTower ℤ B D := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have H : (n : Cardinal) ≤ r := calc
    _ ≤ trdeg ℤ B := ht
    _ ≤ trdeg ℤ B + trdeg B D := le_self_add
    _ = trdeg ℤ D := trdeg_add_eq ℤ B (A := D)
    _ ≤ r := hr
  have hnr : n ≤ r := by exact_mod_cast H
  exact hn.trans (by exact_mod_cast Nat.succ_le_succ hnr)

/-- The dimension bound for any unital subring of the specified
rational function field. No finite-type assumption on the subring is needed. -/
theorem rationalFunctionField_subring_dimension_le (r : ℕ)
    (D : Subring (FractionRing (MvPolynomial (Fin r) ℚ))) : ringKrullDim D ≤ (r+1 : ℕ) := by
  let K := FractionRing (MvPolynomial (Fin r) ℚ)
  let : Algebra ℚ K := inferInstanceAs (Algebra ℚ (FractionRing (MvPolynomial (Fin r) ℚ)))
  let : CharZero K := Algebra.charZero_of_charZero ℚ K
  let : CharZero D := ⟨fun _ _ h => Nat.cast_injective (R := K) (by simpa using congrArg D.subtype h)⟩
  let intDomainTower := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := D) (A := K) (Subsingleton.elim _ _)
  let intRatTower := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := K) (Subsingleton.elim _ _)
  let : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ ℤ⁰
  apply ringKrullDim_le_of_int_trdeg r
  calc
    trdeg ℤ D ≤ trdeg ℤ D + trdeg D K := le_self_add
    _ = trdeg ℤ K := trdeg_add_eq ℤ D (A := K)
    _ = trdeg ℚ K := by simpa [trdeg_eq_zero (R := ℤ) (A := ℚ)] using (trdeg_add_eq ℤ ℚ (A := K)).symm
    _ = r := rationalFunctionField_trdeg r

end UnconditionalCounterexample.Variations
