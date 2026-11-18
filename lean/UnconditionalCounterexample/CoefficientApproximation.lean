import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Associated
import UnconditionalCounterexample.PolynomialAvoidance

/-!
# Supported coefficient approximation

Approximation at finitely many p-adic places gives rational coefficients whose
denominators are supported on the prescribed primes. An independent congruence at a
fresh prime leaves a Cartesian grid of coefficients for finite polynomial avoidance.
-/

noncomputable section
open scoped BigOperators

namespace UnconditionalCounterexample.CoefficientApproximation

/-- Finite CRT retains the entire integer progression of solutions. -/
theorem exists_integer_progression_residues {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, m i ≠ 0)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (r : ∀ i, ZMod (m i)) :
    ∃ z : ℤ, ∀ k : ℤ, ∀ i,
      ((z + (∏ j, m j : ℕ) * k : ℤ) : ZMod (m i)) = r i := by
  classical
  let (i : ι) : NeZero (m i) := ⟨hm i⟩
  let z := Nat.chineseRemainderOfFinset (fun i => (r i).val) m Finset.univ
    (fun i _ => hm i) (fun i _ j _ hij => hcop hij)
  refine ⟨z.val, ?_⟩
  intro k i
  have hz : (z.val : ZMod (m i)) = r i := by
    rw [← ZMod.natCast_zmod_val (r i)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ i))
  have hmprod : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hprod : ((∏ j, m j : ℕ) : ZMod (m i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hmprod
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hprod, zero_mul,
    add_zero] using hz

/-- The progression step is nonzero, including for an empty set of places. -/
theorem modulus_product_ne_zero {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, m i ≠ 0) : (∏ i, m i) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hm i)

/-- Prime-power residues admit a common integer with a nonzero progression step. -/
theorem exists_prime_power_progression {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (N : ι → ℕ) (r : ∀ i, ZMod (p i ^ N i)) :
    ∃ z : ℤ, ∀ k : ℤ, ∀ i,
      ((z + (∏ j, p j ^ N j : ℕ) * k : ℤ) : ZMod (p i ^ N i)) = r i := by
  apply exists_integer_progression_residues
  · intro i
    exact pow_ne_zero _ (hp i).ne_zero
  · intro i j hij
    exact Nat.coprime_pow_primes _ _ (hp i) (hp j) (hinj.ne hij)

/-- Agreement modulo `p^N` means actual `p`-adic approximation. -/
theorem norm_sub_intCast_le_of_residue {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) (N : ℕ) (z : ℤ)
    (hz : (z : ZMod (p ^ N)) = PadicInt.toZModPow N x) :
    ‖x - z‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, map_intCast, ← hz, sub_self]

/-- Approximate finitely many integral local targets and impose a separate congruence
at a fresh auxiliary prime. Every integer in a common nonzero progression works. -/
theorem exists_padic_integer_progression_with_auxiliary
    {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (N : ι → ℕ) (x : ∀ i, ℤ_[p i])
    (ell : ℕ) (hell : ell.Prime) (hfresh : ∀ i, p i ≠ ell)
    (s : ℕ) (r : ZMod (ell ^ s)) :
    ∃ z : ℤ, ∃ M : ℕ, M ≠ 0 ∧ ∀ k : ℤ,
      (∀ i, ‖x i - (z + M * k : ℤ)‖ ≤ (p i : ℝ) ^ (-(N i : ℤ))) ∧
      ((z + M * k : ℤ) : ZMod (ell ^ s)) = r := by
  classical
  let p' : Option ι → ℕ := fun i => i.elim ell p
  let N' : Option ι → ℕ := fun i => i.elim s N
  let r' : ∀ i, ZMod (p' i ^ N' i) := fun i =>
    match i with
    | none => r
    | some j => (show ZMod (p j ^ N j) from PadicInt.toZModPow (N j) (x j))
  have hp' : ∀ i, (p' i).Prime := by
    intro i
    cases i with
    | none => exact hell
    | some i => exact (show (p i).Prime from Fact.out)
  have hi' : Function.Injective p' := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim (hfresh j hij.symm)
    | some i =>
      cases j with
      | none => exact False.elim (hfresh i hij)
      | some j => exact congrArg some (hinj hij)
  obtain ⟨z, hz⟩ := exists_prime_power_progression p' hp' hi' N' r'
  refine ⟨z, ∏ j, p' j ^ N' j, modulus_product_ne_zero _
    (fun i => pow_ne_zero _ (hp' i).ne_zero), ?_⟩
  intro k
  constructor
  · intro i
    apply norm_sub_intCast_le_of_residue (x i) (N i) _
    convert! hz k (some i) using 1
  · exact hz k none

/-- Multiplication by a power of the local prime makes every local target integral. -/
theorem exists_prime_power_mul_norm_le_one {p : ℕ} [Fact p.Prime]
    (x : ℚ_[p]) : ∃ e : ℕ, ‖(p : ℚ_[p]) ^ e * x‖ ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨e, he⟩ := PadicInt.exists_pow_neg_lt p (inv_pos.mpr (norm_pos_iff.mpr hx))
  refine ⟨e, ?_⟩
  rw [norm_mul, Padic.norm_p_pow]
  calc
    (p : ℝ) ^ (-(e : ℤ)) * ‖x‖ ≤ ‖x‖⁻¹ * ‖x‖ :=
      mul_le_mul_of_nonneg_right he.le (norm_nonneg _)
    _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- A single denominator supported on the listed primes makes all targets integral. -/
theorem exists_supported_denominator {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (x : ∀ i, ℚ_[p i]) :
    ∃ D : ℕ, D ≠ 0 ∧
      (∀ q : ℕ, q.Prime → q ∣ D → ∃ i, q = p i) ∧
      ∀ i, ‖(D : ℚ_[p i]) * x i‖ ≤ 1 := by
  classical
  choose e he using fun i => exists_prime_power_mul_norm_le_one (x i)
  let D := ∏ i, p i ^ e i
  refine ⟨D, modulus_product_ne_zero _ (fun i => pow_ne_zero _
    (show (p i).Prime from Fact.out).ne_zero), ?_, ?_⟩
  · intro q hq hqD
    obtain ⟨i, _, hi⟩ := ((Nat.prime_iff.mp hq).dvd_finsetProd_iff _).mp hqD
    exact ⟨i, (Nat.prime_dvd_prime_iff_eq hq (show (p i).Prime from Fact.out)).mp (hq.dvd_of_dvd_pow hi)⟩
  · intro i
    have hdvd : p i ^ e i ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨d, hd⟩ := hdvd
    rw [hd, Nat.cast_mul, Nat.cast_pow, mul_right_comm, norm_mul]
    have hd1 : ‖(d : ℚ_[p i])‖ ≤ 1 := by
      simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := p i) (d : ℤ)
    exact (mul_le_mul_of_nonneg_left hd1 (norm_nonneg _)).trans (by simpa using he i)

/-- Dividing an integer by `D` introduces no denominator outside `D`. -/
theorem denominator_divides (z : ℤ) (D : ℕ) : ((z : ℚ) / D).den ∣ D := by
  apply Int.natCast_dvd_natCast.mp
  simpa only [Rat.divInt_eq_div, Int.cast_natCast] using Rat.den_dvd z (D : ℤ)

/-- Actual finite rational approximation with a fixed supported denominator.
The auxiliary congruence is written after clearing that denominator. -/
theorem exists_rational_progression_with_denominator
    {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (x : ∀ i, ℚ_[p i]) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (D : ℕ) (hD : D ≠ 0) (hDx : ∀ i, ‖(D : ℚ_[p i]) * x i‖ ≤ 1)
    (ell : ℕ) (hell : ell.Prime) (hfresh : ∀ i, p i ≠ ell)
    (s : ℕ) (r : ZMod (ell ^ s)) :
    ∃ z : ℤ, ∃ M : ℕ, M ≠ 0 ∧ ∀ k : ℤ,
      (((z + M * k : ℤ) : ℚ) / D).den ∣ D ∧
      (∀ i, ‖((((z + M * k : ℤ) : ℚ) / D : ℚ) : ℚ_[p i]) - x i‖ < ε i) ∧
      ((z + M * k : ℤ) : ZMod (ell ^ s)) = (D : ZMod (ell ^ s)) * r := by
  classical
  have hDpos (i : ι) : 0 < ‖(D : ℚ_[p i])‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hD)
  choose N hN using fun i => PadicInt.exists_pow_neg_lt (p i) (mul_pos (hε i) (hDpos i))
  let y (i : ι) : ℤ_[p i] := ⟨(D : ℚ_[p i]) * x i, hDx i⟩
  obtain ⟨z, M, hM, hz⟩ := exists_padic_integer_progression_with_auxiliary
    p hinj N y ell hell hfresh s ((D : ZMod (ell ^ s)) * r)
  refine ⟨z, M, hM, fun k => ⟨denominator_divides _ _, ?_, (hz k).2⟩⟩
  intro i
  have he : ‖(D : ℚ_[p i]) * x i - (z + M * k : ℤ)‖ < ε i * ‖(D : ℚ_[p i])‖ := by
    exact ((hz k).1 i).trans_lt (hN i)
  have hid : ((D : ℚ_[p i]) * x i - (z + M * k : ℤ)) / D =
      x i - (z + M * k : ℤ) / (D : ℚ_[p i]) := by
    rw [sub_div, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hD)]
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, norm_sub_rev, ← hid, norm_div]
  exact (div_lt_iff₀ (hDpos i)).mpr he

/-- Finite approximation by rationals integral away from the listed primes, together
with any prescribed auxiliary-prime-power residue after clearing denominators.
The solution set includes a full, nonconstant rational arithmetic progression. -/
theorem exists_supported_rational_progression
    {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (x : ∀ i, ℚ_[p i]) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (ell : ℕ) (hell : ell.Prime) (hfresh : ∀ i, p i ≠ ell)
    (s : ℕ) (r : ZMod (ell ^ s)) :
    ∃ D : ℕ, D ≠ 0 ∧ (∀ q : ℕ, q.Prime → q ∣ D → ∃ i, q = p i) ∧
    ∃ z : ℤ, ∃ M : ℕ, M ≠ 0 ∧ ∀ k : ℤ,
      (((z + M * k : ℤ) : ℚ) / D).den ∣ D ∧
      (∀ i, ‖((((z + M * k : ℤ) : ℚ) / D : ℚ) : ℚ_[p i]) - x i‖ < ε i) ∧
      ((z + M * k : ℤ) : ZMod (ell ^ s)) = (D : ZMod (ell ^ s)) * r := by
  obtain ⟨D, hD, hsupp, hDx⟩ := exists_supported_denominator p x
  exact ⟨D, hD, hsupp, exists_rational_progression_with_denominator
    p hinj x ε hε D hD hDx ell hell hfresh s r⟩

/-- Independent rational coefficient progressions, each with controlled denominator
support and its own auxiliary residue, form a full Cartesian grid. -/
theorem exists_supported_rational_grid
    {ι κ : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (x : κ → ∀ i, ℚ_[p i]) (ε : κ → ι → ℝ) (hε : ∀ c i, 0 < ε c i)
    (ell : ℕ) (hell : ell.Prime) (hfresh : ∀ i, p i ≠ ell)
    (s : ℕ) (r : κ → ZMod (ell ^ s)) :
    ∃ D : κ → ℕ, ∃ z : κ → ℤ, ∃ M : κ → ℕ, ∀ c,
      D c ≠ 0 ∧ (∀ q : ℕ, q.Prime → q ∣ D c → ∃ i, q = p i) ∧
      M c ≠ 0 ∧ ∀ k : ℤ,
        (((z c + M c * k : ℤ) : ℚ) / D c).den ∣ D c ∧
        (∀ i, ‖((((z c + M c * k : ℤ) : ℚ) / D c : ℚ) : ℚ_[p i]) - x c i‖ < ε c i) ∧
        ((z c + M c * k : ℤ) : ZMod (ell ^ s)) = (D c : ZMod (ell ^ s)) * r c := by
  choose D hD hsupp z M hM hz using fun c =>
    exists_supported_rational_progression p hinj (x c) (ε c) (hε c) ell hell hfresh s (r c)
  exact ⟨D, z, M, fun c => ⟨hD c, hsupp c, hM c, hz c⟩⟩

/-- The approximation grid can simultaneously avoid any finite collection of
nonzero polynomial equations, including equations over an extension of `ℚ`. -/
theorem exists_approximating_coefficients_avoiding
    {ι κ η K : Type*} [Fintype ι] [Field K] [CharZero K]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (x : κ → ∀ i, ℚ_[p i]) (ε : κ → ι → ℝ) (hε : ∀ c i, 0 < ε c i)
    (ell : ℕ) (hell : ell.Prime) (hfresh : ∀ i, p i ≠ ell)
    (s : ℕ) (r : κ → ZMod (ell ^ s))
    (I : Finset η) (P : η → MvPolynomial κ K) (hP : ∀ j ∈ I, P j ≠ 0) :
    ∃ q : κ → ℚ,
      (∀ c, (∀ prime : ℕ, prime.Prime → prime ∣ (q c).den → ∃ i, prime = p i) ∧
        (∀ i, ‖(q c : ℚ_[p i]) - x c i‖ < ε c i) ∧
        ∃ D : ℕ, ∃ z : ℤ, D ≠ 0 ∧ ¬ell ∣ D ∧ q c = (z : ℚ) / D ∧
          (z : ZMod (ell ^ s)) = (D : ZMod (ell ^ s)) * r c) ∧
      ∀ j ∈ I, MvPolynomial.eval (fun c => algebraMap ℚ K (q c)) (P j) ≠ 0 := by
  classical
  obtain ⟨D, z, M, hgrid⟩ := exists_supported_rational_grid
    p hinj x ε hε ell hell hfresh s r
  let a : κ → ℚ := fun c => (z c : ℚ) / D c
  let b : κ → ℚ := fun c => (M c : ℚ) / D c
  have hb (c : κ) : b c ≠ 0 := div_ne_zero
    (Nat.cast_ne_zero.mpr (hgrid c).2.2.1) (Nat.cast_ne_zero.mpr (hgrid c).1)
  obtain ⟨n, hn⟩ := PolynomialAvoidance.exists_rational_grid_avoiding
    a b hb (fun _ => 0) I P hP
  let q : κ → ℚ := fun c => a c + b c * (n c : ℚ)
  have hq (c : κ) : q c = ((z c + M c * (n c : ℤ) : ℤ) : ℚ) / D c := by
    simp only [q, a, b, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [add_div, div_mul_eq_mul_div, mul_div_assoc]
  refine ⟨q, fun c => ?_, ?_⟩
  · obtain ⟨hden, herr, hres⟩ := (hgrid c).2.2.2 (n c)
    refine ⟨?_, ?_, D c, z c + M c * (n c : ℤ), (hgrid c).1, ?_, hq c, hres⟩
    · intro prime hprime hdiv
      rw [hq c] at hdiv
      exact (hgrid c).2.1 prime hprime (hdiv.trans hden)
    · simpa only [hq c] using herr
    · intro hdiv
      obtain ⟨i, hi⟩ := (hgrid c).2.1 ell hell hdiv
      exact hfresh i hi.symm
  · simpa only [Nat.zero_add, q] using hn

/-- Supported rational coefficients are integral at every unassigned prime. -/
theorem norm_ratCast_le_one_of_denominator_support {ι : Type*}
    (p : ι → ℕ) (q : ℚ)
    (hsupp : ∀ prime : ℕ, prime.Prime → prime ∣ q.den → ∃ i, prime = p i)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell) :
    ‖(q : ℚ_[ell])‖ ≤ 1 := by
  apply Padic.norm_rat_le_one
  intro hdiv
  obtain ⟨i, hi⟩ := hsupp ell Fact.out hdiv
  exact hfresh i hi.symm

/-- The preceding norm bound supplies an actual integral coefficient model. -/
theorem exists_padicInt_of_denominator_support {ι : Type*}
    (p : ι → ℕ) (q : ℚ)
    (hsupp : ∀ prime : ℕ, prime.Prime → prime ∣ q.den → ∃ i, prime = p i)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell) :
    ∃ a : ℤ_[ell], (a : ℚ_[ell]) = q :=
  ⟨⟨q, norm_ratCast_le_one_of_denominator_support p q hsupp ell hfresh⟩, rfl⟩

end UnconditionalCounterexample.CoefficientApproximation
