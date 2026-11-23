import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Fresh primes for calibration of a retained polynomial

Schur's polynomial-values argument lets the scheduler avoid the prime
divisors of any fixed nonzero integer. A resultant excludes simultaneous
roots of the retained polynomial and a prescribed coprime polynomial.
-/

namespace UnconditionalCounterexample.Calibration

open Polynomial Filter

/-- A nonconstant integer polynomial has a root modulo a prime not dividing
the specified nonzero integer. The witness is an integer representative. -/
theorem exists_prime_dvd_eval_avoiding (f : ℤ[X]) (hd : f.natDegree ≠ 0)
    {L : ℤ} (hL : L ≠ 0) :
    ∃ (p : ℕ) (a : ℤ), p.Prime ∧ ¬ (p : ℤ) ∣ L ∧ (p : ℤ) ∣ f.eval a := by
  have hf : f ≠ 0 := fun h => hd (by simp [h])
  obtain ⟨c, hc⟩ := (eventually_eval_ne_zero_cofinite hf).exists
  let b := f.eval c
  have hb : b ≠ 0 := hc
  let a (j : ℤ) := c + (b * L) * j
  have hainj : Function.Injective a := by
    intro i j hij
    exact mul_left_cancel₀ (mul_ne_zero hb hL) (add_left_cancel hij)
  have ht := ((tendstoCofinite_iff _).mp (f.tendstoCofinite_of_natDegree_ne_zero hd)).comp
    hainj.tendsto_cofinite
  obtain ⟨j, hplus, hminus⟩ := ((ht.eventually (eventually_cofinite_ne b)).and
    (ht.eventually (eventually_cofinite_ne (-b)))).exists
  obtain ⟨z, hz⟩ := sub_dvd_eval_sub (a j) c f
  change f.eval (a j) - b = (a j - c) * z at hz
  dsimp only [a] at hz
  let q := 1 + L * (j * z)
  have he : f.eval (a j) = b * q := by
    dsimp [q, a]
    linear_combination hz
  have hq : q.natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq q with eq | eq
    · have hq1 : q = 1 := by simpa [h] using eq
      exact hplus (by simpa [hq1] using he)
    · have hq1 : q = -1 := by simpa [h] using eq
      exact hminus (by simpa [hq1] using he)
  obtain ⟨p, hp, hdq⟩ := Nat.exists_prime_and_dvd hq
  have hpq : (p : ℤ) ∣ q := Int.natCast_dvd.mpr hdq
  refine ⟨p, a j, hp, ?_, he ▸ dvd_mul_of_dvd_right hpq b⟩
  intro hpL
  have hone : (p : ℤ) ∣ 1 := by
    simpa [q] using dvd_sub hpq (dvd_mul_of_dvd_left hpL (j*z))
  exact hp.not_dvd_one (by exact_mod_cast hone)

private theorem resultant_ne_zero_of_rat {f g : ℤ[X]}
    (hc : IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))) :
    f.resultant g ≠ 0 := by
  have h := resultant_ne_zero _ _ hc
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  simpa only [natDegree_map_eq_of_injective hinj, resultant_map_map, ne_eq,
    map_eq_zero_iff _ hinj] using h

/-- Above any cutoff there is a prime at which a nonconstant polynomial has
a root where a rationally coprime integer polynomial does not vanish. -/
theorem exists_prime_root_avoiding (f g : ℤ[X]) (hd : f.natDegree ≠ 0)
    (hc : IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))) (cutoff : ℕ) :
    ∃ (p : ℕ) (a : ℤ), p.Prime ∧ cutoff < p ∧
      (p : ℤ) ∣ f.eval a ∧ ¬ (p : ℤ) ∣ g.eval a := by
  have hres := resultant_ne_zero_of_rat hc
  have hfac : (cutoff.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero cutoff
  obtain ⟨p, a, hp, hav, hpa⟩ := exists_prime_dvd_eval_avoiding f hd (mul_ne_zero hres hfac)
  have hlarge : cutoff < p := by
    by_contra! h
    apply hav
    apply dvd_mul_of_dvd_right
    exact_mod_cast Nat.dvd_factorial hp.pos h
  refine ⟨p, a, hp, hlarge, hpa, ?_⟩
  intro hpg
  obtain ⟨u, v, _, _, eq⟩ := exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inl hd)
  have heq := congrArg (eval a) eq
  simp only [eval_add, eval_mul, eval_C] at heq
  exact hav (dvd_mul_of_dvd_left (heq ▸ dvd_add (dvd_mul_of_dvd_left hpa _)
    (dvd_mul_of_dvd_left hpg _)) _)

/-- For a primitive irreducible, the chosen prime admits a simple root
avoiding every root of a rationally coprime guard polynomial. Taking the
guard polynomial to be a product enforces a finite list of exclusions. -/
theorem exists_simple_root_prime (f guard : ℤ[X]) (hd : f.natDegree ≠ 0)
    (hprim : f.IsPrimitive) (hirr : Irreducible f)
    (hc : IsCoprime (f.map (Int.castRingHom ℚ)) (guard.map (Int.castRingHom ℚ)))
    (cutoff : ℕ) :
    ∃ (p : ℕ) (a : ℤ), p.Prime ∧ cutoff < p ∧ (p : ℤ) ∣ f.eval a ∧
      ¬ (p : ℤ) ∣ f.derivative.eval a ∧ ¬ (p : ℤ) ∣ guard.eval a := by
  have hs := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hirr |>.separable
  have hcop : IsCoprime (f.map (Int.castRingHom ℚ))
      ((f.derivative * guard).map (Int.castRingHom ℚ)) := by
    rw [Polynomial.map_mul, ← derivative_map]
    exact hs.mul_right hc
  obtain ⟨p, a, hp, hbig, ha, hn⟩ := exists_prime_root_avoiding f _ hd hcop cutoff
  rw [eval_mul] at hn
  exact ⟨p, a, hp, hbig, ha, fun h => hn (dvd_mul_of_dvd_left h _),
    fun h => hn (dvd_mul_of_dvd_right h _)⟩

end UnconditionalCounterexample.Calibration
