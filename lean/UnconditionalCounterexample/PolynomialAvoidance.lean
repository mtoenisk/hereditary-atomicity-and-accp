import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push

/-!
# Polynomial avoidance on arithmetic grids

A fixed arithmetic grid admits simultaneous avoidance of finitely many nonzero
polynomial equations. The coefficients chosen on the grid are rational, even when the
excluded equations have coefficients in an extension field.
-/

namespace UnconditionalCounterexample.PolynomialAvoidance

open MvPolynomial

/-- Finitely many nonzero polynomials can be simultaneously avoided on any
Cartesian box whose coordinate sets are infinite. -/
theorem exists_simultaneous_nonzero_on_box
    {K σ ι : Type*} [CommRing K] [IsDomain K]
    (s : σ → Set K) (hs : ∀ i, (s i).Infinite)
    (I : Finset ι) (p : ι → MvPolynomial σ K)
    (hp : ∀ j ∈ I, p j ≠ 0) :
    ∃ x : σ → K, (∀ i, x i ∈ s i) ∧ ∀ j ∈ I, eval x (p j) ≠ 0 := by
  classical
  let P : MvPolynomial σ K := ∏ j ∈ I, p j
  have hP : P ≠ 0 := by
    dsimp [P]
    exact Finset.prod_ne_zero_iff.mpr hp
  have hnon : ∃ x ∈ Set.pi Set.univ s, eval x P ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hP
    apply MvPolynomial.funext_set s hs
    intro x hx
    simpa using hn x hx
  obtain ⟨x, hx, hPx⟩ := hnon
  refine ⟨x, ?_, ?_⟩
  · intro i
    exact hx i (Set.mem_univ i)
  · have hprod : (∏ j ∈ I, eval x (p j)) ≠ 0 := by
      simpa only [P, map_prod] using hPx
    exact Finset.prod_ne_zero_iff.mp hprod

/-- Every nonconstant arithmetic progression in a characteristic-zero domain
is infinite, even after discarding an initial segment. -/
theorem infinite_arithmetic_progression
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (a b : K) (hb : b ≠ 0) (N : ℕ) :
    (Set.range fun n : ℕ => a + b * ((N + n : ℕ) : K)).Infinite := by
  apply Set.infinite_range_of_injective
  intro n m h
  have hcast : ((N + n : ℕ) : K) = ((N + m : ℕ) : K) :=
    mul_left_cancel₀ hb (add_left_cancel h)
  exact Nat.add_left_cancel (Nat.cast_injective hcast)

/-- Simultaneous polynomial avoidance on independent arithmetic progressions.
Each offset and step is fixed first. Arithmetic conditions encoded by the
supplied grid therefore remain satisfied by the selected tuple. -/
theorem exists_simultaneous_nonzero_on_arithmetic_grid
    {K σ ι : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (a b : σ → K) (hb : ∀ i, b i ≠ 0) (N : σ → ℕ)
    (I : Finset ι) (p : ι → MvPolynomial σ K)
    (hp : ∀ j ∈ I, p j ≠ 0) :
    ∃ n : σ → ℕ, ∀ j ∈ I,
      eval (fun i => a i + b i * ((N i + n i : ℕ) : K)) (p j) ≠ 0 := by
  classical
  obtain ⟨x, hx, hp'⟩ := exists_simultaneous_nonzero_on_box
    (fun i => Set.range fun n : ℕ => a i + b i * ((N i + n : ℕ) : K))
    (fun i => infinite_arithmetic_progression (a i) (b i) (hb i) (N i)) I p hp
  choose n hn using hx
  refine ⟨n, ?_⟩
  have heq : (fun i => a i + b i * ((N i + n i : ℕ) : K)) = x := funext hn
  simpa only [heq] using hp'

/-- The grid coordinates can be rational while the excluded equations have
coefficients in any characteristic-zero extension field, including an algebraic
closure of the rationals. -/
theorem exists_rational_grid_avoiding
    {K σ ι : Type*} [Field K] [CharZero K]
    (a b : σ → ℚ) (hb : ∀ i, b i ≠ 0) (N : σ → ℕ)
    (I : Finset ι) (p : ι → MvPolynomial σ K)
    (hp : ∀ j ∈ I, p j ≠ 0) :
    ∃ n : σ → ℕ, ∀ j ∈ I,
      eval (fun i => algebraMap ℚ K (a i + b i * ((N i + n i : ℕ) : ℚ)))
        (p j) ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_simultaneous_nonzero_on_arithmetic_grid
    (fun i => algebraMap ℚ K (a i)) (fun i => algebraMap ℚ K (b i))
    (fun i => by simpa using hb i) N I p hp
  refine ⟨n, ?_⟩
  simpa only [map_add, map_mul, map_natCast] using hn

end UnconditionalCounterexample.PolynomialAvoidance
