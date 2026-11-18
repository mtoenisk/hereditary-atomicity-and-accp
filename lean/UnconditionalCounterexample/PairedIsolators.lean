import UnconditionalCounterexample.IntersectionStalks

/-!
# Constructing the paired guard isolator

If the primary singleton f has value k, then p^k/f is the guard singleton. Its
vertical profile and the identity f(p^k/f) = p^k supply the two isolators above p.
-/

noncomputable section
namespace UnconditionalCounterexample.PairedIsolators
open WithZero IntersectionDomain IntersectionStalks
variable {K ι : Type*} [Field K]

/-- A primary singleton yields the paired guard singleton by the actual quotient p^k/f. -/
theorem exists_guard_isolator (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    (i j : ι) (hij : i ≠ j) (p : ℕ) (hpinv : (p : K)⁻¹ ∈ B)
    (hpi : v i (p : K) = exp (-1)) (hpj : v j (p : K) = exp (-1))
    (hpother : ∀ l, l ≠ i → l ≠ j → v l (p : K) = 1)
    (f : intersection B v) (k : ℕ) (hk : 0 < k) (hfinv : (f : K)⁻¹ ∈ B)
    (hfi : v i f = exp (-(k : ℤ))) (hfother : ∀ l, l ≠ i → v l f = 1) :
    ∃ g : intersection B v, (g : K)⁻¹ ∈ B ∧
      v j g = exp (-(k : ℤ)) ∧ (∀ l, l ≠ j → v l g = 1) ∧
      f * g = (p : intersection B v) ^ k := by
  let z : K := (p : K) ^ k / (f : K)
  have hpPow (l : ι) (hl : v l (p : K) = exp (-1)) :
      v l ((p : K) ^ k) = exp (-(k : ℤ)) := by
    rw [map_pow, hl, ← exp_nsmul]
    congr 1
    simp
  have hzi : v i z = 1 := by
    dsimp [z]
    rw [map_div₀, hpPow i hpi, hfi, div_self exp_ne_zero]
  have hzj : v j z = exp (-(k : ℤ)) := by
    dsimp [z]
    rw [map_div₀, hpPow j hpj, hfother j (Ne.symm hij), div_one]
  have hzother : ∀ l, l ≠ j → v l z = 1 := by
    intro l hlj
    by_cases hli : l = i
    · simpa [hli] using hzi
    · dsimp [z]
      rw [map_div₀, map_pow, hpother l hli hlj, hfother l hli, one_pow, div_one]
  have hzB : z ∈ B := by
    dsimp [z]
    rw [div_eq_mul_inv]
    exact B.mul_mem (B.pow_mem (natCast_mem B p) k) hfinv
  have hzD : z ∈ intersection B v := by
    apply (mem_intersection B v z).mpr
    refine ⟨hzB, fun l => ?_⟩
    by_cases hl : l = j
    · rw [hl, hzj, exp_le_one_iff]
      exact neg_nonpos.mpr (by positivity)
    · rw [hzother l hl]
  let g : intersection B v := ⟨z, hzD⟩
  have hf0 : (f : K) ≠ 0 := by
    intro hz
    exact exp_ne_zero (hfi.symm.trans (by simp [hz]))
  refine ⟨g, ?_, hzj, hzother, ?_⟩
  · change z⁻¹ ∈ B
    dsimp [z]
    rw [inv_div, div_eq_mul_inv, ← inv_pow]
    exact B.mul_mem ((mem_intersection B v f).mp f.property).1 (B.pow_mem hpinv k)
  · apply Subtype.ext
    change (f : K) * ((p : K) ^ k / (f : K)) = (p : K) ^ k
    exact mul_div_cancel₀ _ hf0

end UnconditionalCounterexample.PairedIsolators
