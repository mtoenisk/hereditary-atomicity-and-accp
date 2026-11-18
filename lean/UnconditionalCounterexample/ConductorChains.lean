import UnconditionalCounterexample.FiniteResidueBlocks
import UnconditionalCounterexample.PrincipalChain
import UnconditionalCounterexample.ConductorAtomicity
import UnconditionalCounterexample.Target
import Factorization.LengthSets
import Mathlib.Order.WellFounded

noncomputable section
namespace UnconditionalCounterexample.ConductorChains
open scoped BigOperators

variable {R Q : Type*} [CommRing R] [IsDomain R] [CommRing Q] [Finite Q]

/-- Disjoint ambient divisors can be grouped into conductor-one blocks in any
finite residue ring. The endpoints and block ratios belong to the actual subring. -/
theorem exists_nonunit_recurrence
    (T : Subring R) (m : R) (hconductor : ∀ z : R, m*z ∈ T)
    (f : R →+* Q) (hker : RingHom.ker f = Ideal.span {m})
    (x : T) (hx : x ≠ 0) (q : ℕ → R) (hq : ∀ i, ¬ IsUnit (q i))
    (hqunit : ∀ i, IsUnit (f (q i)))
    (hdiv : ∀ s : Finset ℕ, (∏ j ∈ s, q j) ∣ (x : R)) :
    ∃ y b : ℕ → T, y 0 = x ∧ (∀ i, y i ≠ 0) ∧ (∀ i, ¬ IsUnit (b i)) ∧
      ∀ i, y i = y (i+1) * b i := by
  classical
  let g : ℕ → Qˣ := fun i => (hqunit i).unit
  obtain ⟨c,hc,hblock,hprefix⟩ := FiniteResidueBlocks.exists_one_blocks g
  let A (i : ℕ) : R := ∏ j ∈ Finset.Ico (c 0) (c i), q j
  let C (i : ℕ) : R := ∏ j ∈ Finset.Ico (c i) (c (i+1)), q j
  have hA (i : ℕ) : f (A i) = 1 := by
    simpa [A, g, map_prod] using congrArg (fun u : Qˣ => (u : Q)) (hprefix i)
  have hC (i : ℕ) : f (C i) = 1 := by
    simpa [C, g, map_prod] using congrArg (fun u : Qˣ => (u : Q)) (hblock i)
  have hcong {z : R} (hz : f z = 1) : m ∣ z-1 := by
    rw [← Ideal.mem_span_singleton, ← hker, RingHom.mem_ker, map_sub, map_one, hz, sub_self]
  have hCT (i : ℕ) : C i ∈ T := mem_subring_of_conductor_dvd_sub_one T m hconductor (hcong (hC i))
  have hCnu (i : ℕ) : ¬ IsUnit (C i) := by
    intro hu
    apply hq (c i)
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem q
      (Finset.mem_Ico.mpr ⟨le_rfl,hc (Nat.lt_succ_self i)⟩)) hu
  have hx0 : (x : R) ≠ 0 := fun h => hx (Subtype.ext h)
  have hchoose (i : ℕ) : ∃ y : R, (x : R) = A i * y := hdiv (Finset.Ico (c 0) (c i))
  choose y hy using hchoose
  have hyT (i : ℕ) : y i ∈ T := cofactor_mem_subring_of_conductor T m hconductor
    ((hy i) ▸ x.property) (hcong (hA i))
  have hy0 (i : ℕ) : y i ≠ 0 := right_ne_zero_of_mul (by rw [← hy i]; exact hx0)
  have hA0 (i : ℕ) : A i ≠ 0 := left_ne_zero_of_mul (by rw [← hy i]; exact hx0)
  have hrec (i : ℕ) : y i = y (i+1) * C i := by
    apply mul_left_cancel₀ (hA0 i)
    calc
      A i * y i = x := (hy i).symm
      _ = A (i+1) * y (i+1) := hy (i+1)
      _ = A i * (y (i+1) * C i) := by
        have hp := Finset.prod_Ico_consecutive q (hc.monotone (Nat.zero_le i))
          (hc.monotone (Nat.le_succ i))
        change (∏ j ∈ Finset.Ico (c 0) (c (i+1)), q j) * y (i+1) = _
        rw [← hp]
        change (A i * C i) * y (i+1) = _
        ac_rfl
  refine ⟨fun i => ⟨y i,hyT i⟩, fun i => ⟨C i,hCT i⟩, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    have h := hy 0
    simpa [A] using h.symm
  · intro i h
    exact hy0 i (congrArg Subtype.val h)
  · intro i hu
    exact hCnu i (hu.map T.subtype)
  · intro i
    exact Subtype.ext (hrec i)

theorem hasStrictChainAt_of_finite_residues
    (T : Subring R) (m : R) (hconductor : ∀ z : R, m*z ∈ T)
    (f : R →+* Q) (hker : RingHom.ker f = Ideal.span {m})
    (x : T) (hx : x ≠ 0) (q : ℕ → R) (hq : ∀ i, ¬ IsUnit (q i))
    (hqunit : ∀ i, IsUnit (f (q i)))
    (hdiv : ∀ s : Finset ℕ, (∏ j ∈ s, q j) ∣ (x : R)) : HasStrictChainAt x := by
  obtain ⟨y,b,hy0,hy,hb,hrec⟩ := exists_nonunit_recurrence T m hconductor f hker x hx q hq hqunit hdiv
  exact ⟨y,hy0,hy,strictMono_principalIdeals_of_nonunit_recurrence y b hy hb hrec⟩

/-- A strict principal chain at x rules out every bound on nonunit decompositions. -/
theorem not_bounded_of_strict_chain {x : R} (hchain : HasStrictChainAt x) :
    ¬ Factorization.HasBoundedFactorizations x := by
  intro hbounded
  obtain ⟨y,hy0,_,hstrict⟩ := hchain
  apply (not_acc_iff_exists_descending_chain.mpr ?_) hbounded.acc_dvdNotUnit
  refine ⟨y,hy0,?_⟩
  intro i
  exact Ideal.span_singleton_lt_span_singleton.mp (hstrict (Nat.lt_succ_self i))

/-- Atomicity turns the unbounded nonunit decompositions into unbounded atom lengths. -/
theorem atom_lengths_unbounded_of_strict_chain
    (hR : Factorization.IsAtomicDomain R) {x : R} (hx : x ≠ 0)
    (hchain : HasStrictChainAt x) : ¬ BddAbove (Factorization.factorizationLengths x) := by
  intro hbound
  exact not_bounded_of_strict_chain hchain
    ((Factorization.hasBoundedFactorizations_iff_bddAbove_factorizationLengths hR hx).mpr hbound)

end UnconditionalCounterexample.ConductorChains
