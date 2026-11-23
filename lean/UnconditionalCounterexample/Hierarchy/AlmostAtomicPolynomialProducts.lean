import UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomialBase
import Factorization.StrictHierarchy
import Mathlib.Data.Nat.Factorization.Induction

/-! # Atomic products from normalized polynomial factors -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial
open Polynomial Factorization

theorem nat_atomic (n : ℕ) : n ≠ 0 → HasAtomicFactorization (n : ring) := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp [hasAtomicFactorization_of_isUnit]
  | prime p hp => exact fun _ => hasAtomicFactorization_of_irreducible (prime_atom p hp)
  | mul a b ha hb =>
    intro hn
    rw [Nat.cast_mul]
    exact (ha (left_ne_zero_of_mul hn)).mul (hb (right_ne_zero_of_mul hn))

theorem int_atomic (z : ℤ) (hz : z ≠ 0) : HasAtomicFactorization (z : ring) := by
  have hn := nat_atomic z.natAbs (Int.natAbs_ne_zero.mpr hz)
  rcases Int.natAbs_eq z with h | h
  · exact (congrArg (fun k : ℤ => HasAtomicFactorization (k : ring)) h).mpr (by simpa only [Int.cast_natCast] using hn)
  · apply (congrArg (fun k : ℤ => HasAtomicFactorization (k : ring)) h).mpr
    rw [Int.cast_neg,Int.cast_natCast,← neg_one_mul]
    exact (hasAtomicFactorization_of_isUnit isUnit_neg_one).mul hn

/-- Factor in the rational polynomial PID, then use an atomic integral scalar
to clear the product of the rational normalization constants. -/
theorem almostAtomic_of_representatives
    (rep : ∀ f : ℚ[X], Irreducible f → ∃ a : ring, Irreducible a ∧ ∃ q : ℚ, q ≠ 0 ∧ f = C q * a.val) :
    IsAlmostAtomicDomain ring := by
  have all (f : ℚ[X]) : f ≠ 0 → ∃ a : ring, HasAtomicFactorization a ∧ ∃ q : ℚ, q ≠ 0 ∧ f = C q * a.val := by
    induction f using WfDvdMonoid.induction_on_irreducible with
    | zero => simp
    | unit f hf =>
      obtain ⟨q,hq,hf⟩ := Polynomial.isUnit_iff.mp hf
      exact fun _ => ⟨1,hasAtomicFactorization_of_isUnit isUnit_one,q,hq.ne_zero,by simp [hf]⟩
    | mul g i hg hi ih =>
      obtain ⟨u,hu,a,ha,hg'⟩ := ih hg
      obtain ⟨v,hv,b,hb,hi'⟩ := rep i hi
      exact fun _ => ⟨v*u,(hasAtomicFactorization_of_irreducible hv).mul hu,b*a,mul_ne_zero hb ha,by
        rw [hg',hi',map_mul]; change _ = _ * (_ * _); ring⟩
  intro x hx
  obtain ⟨a,ha,q,hq,he⟩ := all x.val (fun h => hx (Subtype.ext h))
  have hd : (q.den : ℚ) * q = q.num := by
    conv_lhs => rhs; rw [← q.num_div_den]
    field_simp
  have h : (q.den : ring)*x = (q.num : ring)*a := by
    apply Subtype.ext
    change (q.den : ℚ[X])*x.val = (q.num : ℚ[X])*a.val
    rw [he,← mul_assoc,← map_natCast (C : ℚ →+* ℚ[X]) q.den,← map_mul,hd,map_intCast]
  exact ⟨q.den,nat_atomic _ q.den_ne_zero,h ▸ (int_atomic _ (Rat.num_ne_zero.mpr hq)).mul ha⟩

end UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial
