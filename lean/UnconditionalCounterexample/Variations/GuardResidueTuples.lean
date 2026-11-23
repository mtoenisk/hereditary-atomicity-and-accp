import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.Positivity

/-!
# Residue-field choices for a guard

At any assigned prime, pass to a sufficiently large prime-degree residue
extension. Besides the frozen polynomials, avoid the Frobenius equation
on the first coordinate. This coordinate then generates the entire residue
field, so polynomial interpolation later distinguishes the guard from the
rational primary or the extra point.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.GuardResidueTuples

open MvPolynomial Finset

private theorem exists_nonzero_value {E : Type*} [Field E] [Fintype E] {r : ℕ}
    (F : MvPolynomial (Fin r) E) (hF : F ≠ 0) (hd : F.totalDegree < Fintype.card E) :
    ∃ a : Fin r → E, eval a F ≠ 0 := by
  classical
  by_contra! hall
  have h := schwartz_zippel_totalDegree hF (Finset.univ : Finset E)
  simp [hall] at h
  have hc : (0 : ℚ≥0) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hpow : ((Fintype.card E : ℚ≥0) ^ r) ≠ 0 := pow_ne_zero _ hc.ne'
  have bad : (1 : ℚ≥0) ≤ F.totalDegree / Fintype.card E := by simpa [hpow] using h
  have := (le_div_iff₀ hc).mp bad
  exact (not_le_of_gt (show (F.totalDegree : ℚ≥0) < Fintype.card E by exact_mod_cast hd))
    (by simpa using this)

/-- A prime-degree finite extension of arbitrarily large degree contains a
generating guard tuple avoiding the entire finite list simultaneously. -/
theorem exists_guard (p r bound : ℕ) [Fact p.Prime]
    (S : Finset (MvPolynomial (Fin (r+1)) (ZMod p))) (hS : ∀ f ∈ S, f ≠ 0) :
    ∃ e > bound, e.Prime ∧ ∃ a : Fin (r+1) → GaloisField p e,
      a 0 ≠ 0 ∧ Algebra.adjoin (ZMod p) ({a 0} : Set (GaloisField p e)) = ⊤ ∧
      a 0 ∉ Set.range (algebraMap (ZMod p) (GaloisField p e)) ∧
      ∀ f ∈ S, aeval a f ≠ 0 := by
  classical
  let Y : MvPolynomial (Fin (r+1)) (ZMod p) := X 0
  have hY : Y ^ p - Y ≠ 0 := by
    intro h
    have he := congrArg totalDegree (sub_eq_zero.mp h)
    simp [Y] at he
    exact (Fact.out : p.Prime).ne_one he
  let F := (Y^p-Y) * ∏ f ∈ S, f
  have hF : F ≠ 0 := mul_ne_zero hY (Finset.prod_ne_zero_iff.mpr hS)
  obtain ⟨e, he, hprime⟩ := Nat.exists_infinite_primes (max bound F.totalDegree + 1)
  let E := GaloisField p e
  let := Fintype.ofFinite E
  have hc : Fintype.card E = p^e := by rw [← Nat.card_eq_fintype_card, GaloisField.card p e hprime.ne_zero]
  let φ := algebraMap (ZMod p) E
  have hmap : map φ F ≠ 0 := (map_ne_zero_iff (map φ) (map_injective φ φ.injective)).mpr hF
  have hd : (map φ F).totalDegree < Fintype.card E := by
    rw [hc]
    have h1 := Nat.lt_pow_self (Fact.out : p.Prime).one_lt (n := e)
    rw [totalDegree, support_map_of_injective _ φ.injective]
    change F.totalDegree < p ^ e
    omega
  obtain ⟨a, ha⟩ := exists_nonzero_value (map φ F) hmap hd
  change eval a (map φ F) ≠ 0 at ha
  rw [← eval₂_eq_eval_map] at ha
  have hprod : aeval a (Y^p-Y) ≠ 0 ∧ ∀ f ∈ S, aeval a f ≠ 0 := by
    change aeval a F ≠ 0 at ha
    rw [show aeval a F = aeval a (Y^p-Y) * ∏ f ∈ S, aeval a f by simp [F]] at ha
    exact ⟨left_ne_zero_of_mul ha, Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul ha)⟩
  have hnot : a 0 ∉ Set.range φ := by
    rintro ⟨c, hc'⟩
    apply hprod.1
    rw [map_sub, map_pow]
    simp only [Y, aeval_X]
    rw [← hc', ← map_pow, ZMod.pow_card, sub_self]
  have hadj : Algebra.adjoin (ZMod p) ({a 0} : Set E) = ⊤ := by
    have deg : Module.finrank (ZMod p) E = e := GaloisField.finrank p hprime.ne_zero
    rcases (Subalgebra.isSimpleOrder_of_finrank_prime (ZMod p) E (deg.symm ▸ hprime)).eq_bot_or_eq_top
        (Algebra.adjoin (ZMod p) ({a 0} : Set E)) with hbot | htop
    · have hmem := Algebra.subset_adjoin (R := ZMod p) (Set.mem_singleton (a 0))
      rw [hbot] at hmem
      exact (hnot (Algebra.mem_bot.mp hmem)).elim
    · exact htop
  exact ⟨e, by omega, hprime, a, fun h => hnot ⟨0, (map_zero φ).trans h.symm⟩, hadj, hnot, hprod.2⟩

end UnconditionalCounterexample.Variations.GuardResidueTuples
