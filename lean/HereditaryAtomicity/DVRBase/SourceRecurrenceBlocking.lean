import HereditaryAtomicity.DVRBase.BlockDegrees
import HereditaryAtomicity.CharP.SourceChain
import Mathlib.Data.Nat.Nth

/-!
# Exact recurrence blocking of finite-support source chains

Every prescribed infinite set of source endpoints admits a blocking whose
ratio support is exactly the original recurrent set. No nonatomicity or
class-group hypothesis is used in this combinatorial construction.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open Set

/-- An arbitrary infinite endpoint set admits blocks meeting every recurrent
member of a finite total support and no nonrecurrent member. -/
theorem exists_finite_support_blocking
    {X : Type*} (A : ℕ → X → Prop)
    (hfinite : Set.Finite {x | ∃ n, A n x})
    (B : Set ℕ) (hB : B.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (∀ n, f n ∈ B) ∧
      ∀ n x, (∃ j, f n ≤ j ∧ j < f (n + 1) ∧ A j x) ↔
        Set.Infinite {j | A j x} := by
  classical
  let T := {x : X // ∃ n, A n x}
  let : Fintype T := hfinite.fintype
  let Rec : Set X := {x | Set.Infinite {j | A j x}}
  have hRec : Rec.Finite := hfinite.subset fun x hx => hx.nonempty
  let : Fintype Rec := hRec.fintype
  let bad : Set ℕ := ⋃ x : T, {j | A j x.val ∧ x.val ∉ Rec}
  have hbad : bad.Finite := Set.finite_iUnion fun x => by
    by_cases hx : x.val ∈ Rec
    · simp only [hx, not_true_eq_false, and_false, Set.ofPred_false]
      exact Set.finite_empty
    · exact (Set.not_infinite.mp hx).subset (fun _ h => h.1)
  obtain ⟨N, hN⟩ := hbad.bddAbove
  have hlate (a j : ℕ) (ha : N < a) (haj : a ≤ j) (x : X) (hx : A j x) : x ∈ Rec := by
    by_contra hn
    have hj : j ∈ bad := Set.mem_iUnion.mpr ⟨⟨x, ⟨j, hx⟩⟩, hx, hn⟩
    exact (not_le_of_gt (ha.trans_le haj)) (hN hj)
  have hnext (a : {a : ℕ // N < a}) :
      ∃ b : {a : ℕ // N < a}, b.val ∈ B ∧ a.val < b.val ∧
        ∀ x, (∃ j, a.val ≤ j ∧ j < b.val ∧ A j x) ↔ x ∈ Rec := by
    choose j hj hja using fun x : Rec => x.property.exists_gt a.val
    obtain ⟨b, hb, hbig⟩ := hB.exists_gt (max a.val (Finset.univ.sup j))
    have hab : a.val < b := (le_max_left _ _).trans_lt hbig
    refine ⟨⟨b, a.property.trans hab⟩, hb, hab, ?_⟩
    intro x
    constructor
    · rintro ⟨i, hai, hib, hix⟩
      exact hlate _ _ a.property hai x hix
    · intro hx
      let x' : Rec := ⟨x, hx⟩
      exact ⟨j x', (hja x').le,
        (Finset.le_sup (f := j) (Finset.mem_univ x')).trans_lt
          ((le_max_right _ _).trans_lt hbig), hj x'⟩
  choose next hnextB hnextgt hnextspec using hnext
  obtain ⟨a, haB, haN⟩ := hB.exists_gt N
  let seq : ℕ → {a : ℕ // N < a} := fun n => Nat.rec ⟨a, haN⟩ (fun _ s => next s) n
  refine ⟨fun n => (seq n).val, strictMono_nat_of_lt_succ (fun n => hnextgt (seq n)), ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact haB
    | succ n => exact hnextB (seq n)
  · intro n x
    exact hnextspec (seq n) x


variable {R : Type*} [CommRing R]

/-- The interval product identity uses only the exact source chain equations. -/
theorem sourceChain_endpoint_eq_mul_sourceBlock (x t : ℕ → R)
    (hstep : ∀ n, x n = x (n + 1) * t n) (a n : ℕ) :
    x a = x (a + n + 1) * sourceBlock t a n := by
  induction n with
  | zero => simpa only [sourceBlock_zero, Nat.add_zero] using hstep a
  | succ n ih =>
    rw [sourceBlock_succ, ih, hstep (a + n + 1)]
    have heq : a + n + 1 + 1 = a + (n + 1) + 1 := by omega
    rw [heq]
    ring

/-- A block belongs to a prime precisely when one of its literal factors does. -/
theorem sourceBlock_mem_prime_iff (t : ℕ → R) (P : Ideal R) [P.IsPrime] (a n : ℕ) :
    sourceBlock t a n ∈ P ↔ ∃ j, a ≤ j ∧ j < a + n + 1 ∧ t j ∈ P := by
  rw [sourceBlock, Ideal.IsPrime.prod_mem_iff]
  constructor
  · rintro ⟨i, hi, ht⟩
    exact ⟨a + i, by omega, by have hi' := Finset.mem_range.mp hi; omega, ht⟩
  · rintro ⟨j, haj, hja, ht⟩
    refine ⟨j - a, Finset.mem_range.mpr (by omega), ?_⟩
    simpa only [Nat.add_sub_of_le haj] using ht

/-- Finite top support admits literal common-support blocking inside any
specified infinite set of endpoint indices. The common support is exactly
the original recurrent set. -/
theorem exists_sourceChain_recurrent_blocking
    (x t : ℕ → R) (hstep : ∀ n, x n = x (n + 1) * t n)
    (hfinite : Set.Finite {P : MaximalSpectrum R | x 0 ∈ P.asIdeal})
    (B : Set ℕ) (hB : B.Infinite) :
    ∃ (f : ℕ → ℕ) (r : ℕ → R), StrictMono f ∧ (∀ n, f n ∈ B) ∧
      (∀ n, x (f n) = x (f (n + 1)) * r n) ∧
      ∀ n (P : MaximalSpectrum R), r n ∈ P.asIdeal ↔
        Set.Infinite {j | t j ∈ P.asIdeal} := by
  have htotal : Set.Finite {P : MaximalSpectrum R | ∃ n, t n ∈ P.asIdeal} :=
    hfinite.subset (by
      rintro P ⟨n, hn⟩
      exact P.asIdeal.mem_of_dvd (sourceChain_ratio_dvd_top x t hstep n) hn)
  obtain ⟨f, hf, hfB, hblock⟩ :=
    exists_finite_support_blocking (fun n (P : MaximalSpectrum R) => t n ∈ P.asIdeal)
      htotal B hB
  let len (n : ℕ) := f (n + 1) - f n - 1
  have hend (n : ℕ) : f n + len n + 1 = f (n + 1) := by
    have hh : f n < f (n + 1) := hf (Nat.lt_succ_self n)
    dsimp [len]
    omega
  refine ⟨f, fun n => sourceBlock t (f n) (len n), hf, hfB, ?_, ?_⟩
  · intro n
    simpa only [hend n] using sourceChain_endpoint_eq_mul_sourceBlock x t hstep (f n) (len n)
  · intro n P
    rw [sourceBlock_mem_prime_iff, hend n]
    exact hblock n P

end HereditaryAtomicity.DVRBase
