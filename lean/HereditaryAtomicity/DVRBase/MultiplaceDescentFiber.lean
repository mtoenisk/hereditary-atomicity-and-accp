import HereditaryAtomicity.DVRBase.MultiplaceDescent

/-! Actual source descent from an infinite weighted component-class fiber. -/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped nonZeroDivisors BigOperators
variable {R ι : Type*} [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R] [Fintype ι]

/-- An infinite weighted component-class fiber gives an actual strict chain
with exactly the positive-weight recurrent support. The top is literally a
power of an original endpoint, rather than an assumed local return. -/
theorem exists_strict_chain_of_infinite_weighted_component_fiber
    (π : ι → R) (U : ι → Set (MaximalSpectrum R))
    (hU : ∀ i, IsClopenInFiber (π i) (U i)) (e : ι → ℕ)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hfinite : Set.Finite {P : MaximalSpectrum R | x 0 ∈ P.asIdeal})
    (γ : ClassGroup R)
    (hγ : Set.Infinite {n | (∏ i, componentClassHom (hU i)
      ⟨x n, mem_nonZeroDivisors_of_ne_zero (hx n)⟩ ^ e i) = γ})
    (hactive : ∃ (i : ι) (P : MaximalSpectrum R), 0 < e i ∧ P ∈ U i ∧
      Set.Infinite {n | t n ∈ P.asIdeal}) :
    ∃ (n₀ : ℕ) (c a : ℕ → R),
      (∀ n, c n ≠ 0) ∧ c 0 = x n₀ ^ ∑ i, e i ∧
      (∀ n, c n = c (n + 1) * a n) ∧ (∀ n, ¬ IsUnit (a n)) ∧
      Set.Finite {P : MaximalSpectrum R | c 0 ∈ P.asIdeal} ∧
      ∀ n (P : MaximalSpectrum R), a n ∈ P.asIdeal ↔
        ∃ i, 0 < e i ∧ P ∈ U i ∧ Set.Infinite {j | t j ∈ P.asIdeal} := by
  classical
  obtain ⟨f, r, hf, hfB, hfr, hrsupp⟩ := exists_sourceChain_recurrent_blocking x t hxt hfinite
    {n | (∏ i, componentClassHom (hU i)
      ⟨x n, mem_nonZeroDivisors_of_ne_zero (hx n)⟩ ^ e i) = γ} hγ
  obtain ⟨c, a, hc, hc0, hca, hsa⟩ :=
    exists_supported_chain_of_weighted_component_class_constant π U hU e
      (fun n => x (f n)) r (fun n => hx (f n)) hfr
      (fun n => (hfB n).trans (hfB 0).symm)
  obtain ⟨u, hu⟩ := hc0
  let c' : ℕ → R := fun n => c n * (u : R)
  have hs (n : ℕ) (P : MaximalSpectrum R) : a n ∈ P.asIdeal ↔
      ∃ i, 0 < e i ∧ P ∈ U i ∧ Set.Infinite {j | t j ∈ P.asIdeal} := by
    rw [hsa]
    simp only [hrsupp]
  refine ⟨f 0, c', a, fun n => mul_ne_zero (hc n) u.ne_zero, hu, ?_, ?_, ?_, hs⟩
  · intro n
    dsimp [c']
    rw [hca n]
    ring
  · intro n haunit
    obtain ⟨i, P, he, hPU, hrec⟩ := hactive
    exact (inferInstance : P.asIdeal.IsPrime).ne_top
      (P.asIdeal.eq_top_of_isUnit_mem ((hs n P).mpr ⟨i, he, hPU, hrec⟩) haunit)
  · apply hfinite.subset
    intro P hP
    have hpow : x (f 0) ^ ∑ i, e i ∈ P.asIdeal := hu ▸ hP
    have hxP := (inferInstance : P.asIdeal.IsPrime).mem_of_pow_mem _ hpow
    exact P.asIdeal.mem_of_dvd (sourceChain_endpoint_dvd_top x t hxt (f 0)) hxP

end HereditaryAtomicity.DVRBase
