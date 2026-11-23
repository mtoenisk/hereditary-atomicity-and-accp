import UnconditionalCounterexample.Variations.DyadicSplitValues
import UnconditionalCounterexample.Variations.SplitConductor
import UnconditionalCounterexample.Variations.TwoChainReturns

/-!
# Descent of the reserved raw's local returns

The prime powers of the conductor modulus are partitioned by whole fibre.
Local estimates for the selected normalized raw then put both factors of a
split task in the original subring, including at modulus one.
-/

noncomputable section

namespace UnconditionalCounterexample.DyadicSplit

open PrimaryChoices GuardSupport MixedStageSelection
open Variations.Univariate

set_option backward.isDefEq.respectTransparency false

/-- Partition a positive modulus into coprime parts with the specified prime
assignment, retaining the full power of each prime. -/
theorem exists_coprime_parts {m : ℕ} (hm : 0 < m) (first : ℕ → Bool) :
    ∃ a b : ℕ, a*b = m ∧ a.Coprime b ∧
      (∀ p, p.Prime → p ∣ a → first p = false ∧ a.factorization p = m.factorization p) ∧
      (∀ p, p.Prime → p ∣ b → first p = true ∧ b.factorization p = m.factorization p) := by
  let f (c : Bool) := m.factorization.filter (fun p => first p = c)
  let d (c : Bool) := (f c).prod (· ^ ·)
  have hle (c) : f c ≤ m.factorization := by
    intro p
    simp only [f, Finsupp.filter_apply]
    split <;> simp
  have hfac (c) : (d c).factorization = f c :=
    Nat.factorization_prod_pow_eq_self_of_le_factorization (hle c)
  have hsum : f false + f true = m.factorization := by
    ext p
    cases he : first p <;> simp [f, he]
  have hprod : d false * d true = m := by
    rw [← Nat.prod_factorization_pow_eq_self hm.ne', ← hsum]
    exact (Finsupp.prod_add_index' (fun p => pow_zero p) (fun p u v => pow_add p u v)).symm
  have hside (c : Bool) {p : ℕ} (hp : p.Prime) (hd : p ∣ d c) :
      first p = c ∧ (d c).factorization p = m.factorization p := by
    have hdc : d c ≠ 0 := by
      cases c <;> intro he <;> simp [he] at hprod <;> omega
    have hpos := hp.factorization_pos_of_dvd hdc hd
    rw [hfac] at hpos ⊢
    by_cases he : first p = c
    · simp [f, he]
    · simp [f, he] at hpos
  refine ⟨_, _, hprod, Nat.coprime_of_dvd ?_, fun _ => hside false, fun _ => hside true⟩
  intro p hp ha hb
  have h₁ := (hside false hp ha).1
  have h₂ := (hside true hp hb).1
  simp [h₁] at h₂

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Test the quotient by an integer only at actual points over the finitely
many primes dividing it. -/
theorem integer_dvd_of_prime_power_points (R : Requirements) (a : domain R) {m : ℕ}
    (hm : 0 < m) (hlocal : ∀ (p : PrimeIndex), p.val ∣ m →
      ∀ z ∈ (permanentSite R p).fibre.points,
        LocalEvaluation.evalAt z.value.val z.transcendental (a : RatFunc ℚ) /
        (p.val : ℚ_[p.val]) ^ m.factorization p.val ∈ PadicInt.subring p.val) :
    (m : domain R) ∣ a := by
  have ha := (mem_domain_iff R _).mp a.property
  let q : RatFunc ℚ := (a : RatFunc ℚ) / m
  have hq : q ∈ domain R := by
    apply (mem_domain_iff R _).mpr
    constructor
    · change (a : RatFunc ℚ) / m ∈ poleAlgebra R
      rw [div_eq_mul_inv]
      apply (poleAlgebra R).mul_mem ha.1
      simpa using (poleAlgebra R).algebraMap_mem ((m : ℚ)⁻¹)
    · intro p z hz
      simp only [q, map_div₀, map_natCast]
      by_cases hd : p.val ∣ m
      · apply integral_div_nat_of_precision hm.ne' _ (hlocal p hd z hz)
        exact (Nat.factorization_def m p.property).symm.le
      · apply integral_div_nat_of_precision hm.ne' (n := 0)
          (by simp [padicValNat.eq_zero_of_not_dvd hd])
        simpa using ha.2 p z hz
  exact ⟨⟨q,hq⟩, Subtype.ext (show (a : RatFunc ℚ) = m*((a : RatFunc ℚ)/m) by field_simp [hm.ne'])⟩

/-- The two full coprime conductor parts returning the two factors to one. -/
theorem coprime_returns_of_point_returns (R : Requirements) (m : ℕ) (hm : 0 < m) (first : ℕ → Bool)
    (u v : domain R)
    (hlocal : ∀ (p : PrimeIndex), p.val ∣ m → ∀ z ∈ (permanentSite R p).fibre.points,
      let e := LocalEvaluation.evalAt z.value.val z.transcendental
      let d := (p.val : ℚ_[p.val]) ^ m.factorization p.val
      (first p.val = false → (e (u : RatFunc ℚ)-1)/d ∈ PadicInt.subring p.val) ∧
      (first p.val = true → (e (v : RatFunc ℚ)-1)/d ∈ PadicInt.subring p.val)) :
    ∃ a b : ℕ, m = a*b ∧ a.Coprime b ∧ (a : domain R) ∣ u-1 ∧ (b : domain R) ∣ v-1 := by
  obtain ⟨a,b,hab,hcop,hfalse,htrue⟩ := exists_coprime_parts hm first
  have ha : 0 < a := by by_contra! he; simp [Nat.eq_zero_of_le_zero he] at hab; omega
  have hb : 0 < b := by by_contra! he; simp [Nat.eq_zero_of_le_zero he] at hab; omega
  refine ⟨a,b,hab.symm,hcop,?_,?_⟩
  · apply integer_dvd_of_prime_power_points R _ ha
    intro p hp z hz
    obtain ⟨hfirst, he⟩ := hfalse _ p.property hp
    have hd : p.val ∣ m := hab ▸ dvd_mul_of_dvd_left hp b
    simpa [he] using (hlocal p hd z hz).1 hfirst
  · apply integer_dvd_of_prime_power_points R _ hb
    intro p hp z hz
    obtain ⟨hfirst, he⟩ := htrue _ p.property hp
    have hd : p.val ∣ m := hab ▸ dvd_mul_of_dvd_right hp a
    simpa [he] using (hlocal p hd z hz).2 hfirst

/-- Prime-power returns at whole fibres, with either factor selected as the
unit, put both factors of a product in its original conductor-containing subring. -/
theorem factors_mem_of_point_returns (R : Requirements) (m : ℕ) (hm : 0 < m) (first : ℕ → Bool)
    (T : Subring (domain R)) (hc : ∀ t : domain R, (m : domain R)*t ∈ T)
    (u v : domain R) (hprod : u*v ∈ T)
    (hlocal : ∀ (p : PrimeIndex), p.val ∣ m → ∀ z ∈ (permanentSite R p).fibre.points,
      let e := LocalEvaluation.evalAt z.value.val z.transcendental
      let d := (p.val : ℚ_[p.val]) ^ m.factorization p.val
      (first p.val = false → (e (u : RatFunc ℚ)-1)/d ∈ PadicInt.subring p.val) ∧
      (first p.val = true → (e (v : RatFunc ℚ)-1)/d ∈ PadicInt.subring p.val)) :
    u ∈ T ∧ v ∈ T := by
  obtain ⟨a,b,hab,hcop,hu,hv⟩ := coprime_returns_of_point_returns R m hm first u v hlocal
  exact factors_mem_of_coprime_returns T hcop (hab ▸ hc) hprod hu hv

/-- The selected reserved raw realizes both coprime congruences on the actual domain. -/
theorem selected_coprime_returns (R : Requirements) (n m : ℕ) (hm : 0 < m) (first : ℕ → Bool)
    (x : domain R) (hx : (x : RatFunc ℚ) ≠ 0)
    (u₀ : RatFunc ℚ) (h₀ : u₀ ≠ 0)
    (base : Targets (selection R n).batch
      (extend R ((chain R).approx n) (table R n) (selection R n).batch))
    (ht : actualTargets R n = reserveTargets _ _ base m first (x : RatFunc ℚ) u₀ hx h₀)
    (hprocessed : ∀ p : PrimeIndex, p.val ∣ m → p ∈ (selection R n).batch.processed.primes)
    (hmatch : ∀ (p : PrimeIndex), p.val ∣ m → ∀ b (hb : Active (permanentSite R p).paired b),
      ‖(permanentSite R p).evaluate b hb u₀‖ =
        if first p.val then ‖(permanentSite R p).evaluate b hb (x : RatFunc ℚ)‖ else 1)
    (u v : domain R) (hu : (u : RatFunc ℚ) = u₀ * (chain R).generators n)
    (hv : (v : RatFunc ℚ) = (x : RatFunc ℚ)/(u : RatFunc ℚ))
    : ∃ a b : ℕ, m = a*b ∧ a.Coprime b ∧ (a : domain R) ∣ u-1 ∧ (b : domain R) ∣ v-1 := by
  apply coprime_returns_of_point_returns R m hm first u v
  intro p hd z hz
  obtain ⟨j, rfl⟩ := primes.surjective p
  let i : (selection R n).batch.indices := ⟨j, ((selection R n).batch.mem_indices j).mpr
    (hprocessed (primes j) hd)⟩
  obtain ⟨c, hc', heval⟩ := (permanentSite R (primes j)).branch_of_point hz
  have hxint := ((mem_domain_iff R _).mp x.property).2 (primes j) z hz
  have he (y : RatFunc ℚ) : (permanentSite R (primes j)).evaluate c hc' y =
      LocalEvaluation.evalAt z.value.val z.transcendental y := by
    change LocalEvaluation.evalAt _ _ _ = _
    simp only [heval]
  have hcong := selected_factor_congruences R n m first (x : RatFunc ℚ) u₀ hx h₀ base ht i hd c
    hc' ((he x).symm ▸ hxint) (hmatch (primes j) hd c hc')
  dsimp only [i] at hcong
  rw [← hu, ← hv] at hcong
  rw [he u, he v, he x] at hcong
  constructor
  · intro hfirst
    simpa only [hfirst, Bool.false_eq_true, ↓reduceIte] using hcong.1
  · intro hfirst
    simpa only [hfirst, ↓reduceIte] using hcong.2

/-- For a split task whose conductor primes were requested before this stage,
the two factors with the reserved last raw belong to every subring containing
their product and the given integer conductor. -/
theorem selected_factors_mem (R : Requirements) (n m : ℕ) (hm : 0 < m) (first : ℕ → Bool)
    (T : Subring (domain R)) (hc : ∀ t : domain R, (m : domain R)*t ∈ T)
    (x : domain R) (hxT : x ∈ T) (hx : (x : RatFunc ℚ) ≠ 0)
    (u₀ : RatFunc ℚ) (h₀ : u₀ ≠ 0)
    (base : Targets (selection R n).batch
      (extend R ((chain R).approx n) (table R n) (selection R n).batch))
    (ht : actualTargets R n = reserveTargets _ _ base m first (x : RatFunc ℚ) u₀ hx h₀)
    (hprocessed : ∀ p : PrimeIndex, p.val ∣ m → p ∈ (selection R n).batch.processed.primes)
    (hmatch : ∀ (p : PrimeIndex), p.val ∣ m → ∀ b (hb : Active (permanentSite R p).paired b),
      ‖(permanentSite R p).evaluate b hb u₀‖ =
        if first p.val then ‖(permanentSite R p).evaluate b hb (x : RatFunc ℚ)‖ else 1)
    (u v : domain R) (hu : (u : RatFunc ℚ) = u₀ * (chain R).generators n)
    (hv : (v : RatFunc ℚ) = (x : RatFunc ℚ)/(u : RatFunc ℚ))
    (hne : (u : RatFunc ℚ) ≠ 0) : u ∈ T ∧ v ∈ T := by
  obtain ⟨a,b,hab,hcop,h₁,h₂⟩ := selected_coprime_returns R n m hm first x hx u₀ h₀
    base ht hprocessed hmatch u v hu hv
  have hprod : u*v = x := Subtype.ext (show (u : RatFunc ℚ)*(v : RatFunc ℚ) = x by
    rw [hv, mul_div_cancel₀ _ hne])
  exact factors_mem_of_coprime_returns T hcop (hab ▸ hc) (hprod ▸ hxT) h₁ h₂

end UnconditionalCounterexample.DyadicSplit
