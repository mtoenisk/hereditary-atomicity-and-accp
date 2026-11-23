import UnconditionalCounterexample.Hierarchy.EvaluationRing
import Mathlib.Data.Nat.Factorization.Basic

/-! Away from one prime all coefficient denominators can be cleared by an integer
which is a unit at that prime. -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy
open Polynomial GuardSupport

theorem exists_away_clear (p : PrimeIndex) (f : ℚ[X]) :
    ∃ d : ℕ, p.val.Coprime d ∧ ∀ q : PrimeIndex, q ≠ p → ∀ a : ℤ_[q.val],
      ‖(d : ℚ_[q.val]) * f.eval₂ (Rat.castHom _) (a : ℚ_[q.val])‖ ≤ 1 := by
  by_cases hf : f = 0
  · exact ⟨1, by simp, by simp [hf]⟩
  obtain ⟨c, V, hc, _, hV⟩ := exists_integer_multiple f hf
  have hn : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  let d := ordCompl[p.val] c.natAbs
  refine ⟨d, Nat.coprime_ordCompl p.property hn, ?_⟩
  intro q hq a
  have hVq : ‖(c : ℚ_[q.val]) * f.eval₂ (Rat.castHom _) (a : ℚ_[q.val])‖ ≤ 1 := by
    have he := congrArg (Polynomial.eval₂ (Rat.castHom ℚ_[q.val]) (a : ℚ_[q.val])) hV
    simp only [Polynomial.eval₂_map, Polynomial.eval₂_mul, Polynomial.eval₂_C] at he
    have hm : (Rat.castHom ℚ_[q.val]).comp (algebraMap ℤ ℚ) = Int.castRingHom ℚ_[q.val] :=
      Subsingleton.elim _ _
    rw [hm, ← coe_intPolynomial_eval] at he
    change _ = (c : ℚ_[q.val]) * _ at he
    rw [← he]
    exact (V.eval₂ (Int.castRingHom ℤ_[q.val]) a).property
  have hu : ‖(p.val : ℚ_[q.val])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes q.property p.property).mpr
      (fun h => hq (Subtype.ext h)))
  have he : (p.val : ℚ_[q.val]) ^ c.natAbs.factorization p.val * d = c.natAbs := by
    exact_mod_cast Nat.ordProj_mul_ordCompl_eq_self c.natAbs p.val
  have hnorm := congrArg norm he
  simp only [norm_mul, norm_pow, hu, one_pow, one_mul, norm_natAbs] at hnorm
  simpa only [norm_mul, hnorm] using hVq

end UnconditionalCounterexample.Hierarchy
