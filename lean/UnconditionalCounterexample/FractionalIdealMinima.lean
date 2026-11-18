import UnconditionalCounterexample.FractionalIdealProfiles

/-! Actual finite-generator minima and transport between valuations. -/

namespace UnconditionalCounterexample.FractionalIdealProfiles
open WithZero
open scoped nonZeroDivisors
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

/-- The actual sum of two fractional ideals takes the minimum exponent. -/
theorem HasValue.add {I J : FractionalIdeal R⁰ K} {v : Valuation K ℤᵐ⁰} {a b : ℤ}
    (hI : HasValue I v a) (hJ : HasValue J v b) : HasValue (I + J) v (min a b) := by
  have ha : exp (-a) ≤ (exp (-min a b) : ℤᵐ⁰) := exp_le_exp.mpr (by omega)
  have hb : exp (-b) ≤ (exp (-min a b) : ℤᵐ⁰) := exp_le_exp.mpr (by omega)
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := (FractionalIdeal.mem_add I J z).mp hz
    exact (v.map_add x y).trans (max_le ((hI.1 x hx).trans ha) ((hJ.1 y hy).trans hb))
  · rcases le_total a b with hab | hba
    · obtain ⟨x, hx, hv⟩ := hI.2
      refine ⟨x, (FractionalIdeal.mem_add I J x).mpr ⟨x, hx, 0, J.zero_mem, add_zero x⟩, ?_⟩
      simpa only [min_eq_left hab] using hv
    · obtain ⟨y, hy, hv⟩ := hJ.2
      refine ⟨y, (FractionalIdeal.mem_add I J y).mpr ⟨0, I.zero_mem, y, hy, zero_add y⟩, ?_⟩
      simpa only [min_eq_right hba] using hv

/-- A chosen finite generating set gives the actual ideal value whenever it
contains a generator attaining the bound. -/
theorem hasValue_of_span (v : Valuation K ℤᵐ⁰)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (I : FractionalIdeal R⁰ K) (s : Set K) (hs : Submodule.span R s = I) (n : ℤ)
    (hbound : ∀ x ∈ s, v x ≤ exp (-n)) (hattain : ∃ x ∈ s, v x = exp (-n)) :
    HasValue I v n := by
  refine ⟨?_, ?_⟩
  · intro x hx
    apply span_bound v hR s (exp (-n)) hbound x
    rw [hs]
    exact hx
  · obtain ⟨x, hx, hv⟩ := hattain
    refine ⟨x, ?_, hv⟩
    change x ∈ (I : Submodule R K)
    rw [← hs]
    exact Submodule.subset_span hx

/-- An attained ideal minimum is attained by a generator in any finite generating set. -/
theorem HasValue.generator_attains {I : FractionalIdeal R⁰ K} {v : Valuation K ℤᵐ⁰} {n : ℤ}
    (hI : HasValue I v n) (hR : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (s : Finset K) (hs : Submodule.span R (s : Set K) = I) :
    ∃ x ∈ s, v x = exp (-n) := by
  classical
  have hsn : s.Nonempty := by
    by_contra he
    have he' := Finset.not_nonempty_iff_eq_empty.mp he
    apply hI.ne_zero
    apply FractionalIdeal.coeToSubmodule_eq_bot.mp
    rw [← hs, he']
    simp
  obtain ⟨y, hy, hmax⟩ := s.exists_max_image v hsn
  obtain ⟨x, hx, hvx⟩ := hI.2
  have hyI : y ∈ I := by
    change y ∈ (I : Submodule R K)
    rw [← hs]
    exact Submodule.subset_span hy
  have hvle : v x ≤ v y := by
    apply span_bound v hR (s : Set K) (v y) hmax x
    rw [hs]
    exact hx
  exact ⟨y, hy, le_antisymm (hI.1 y hyI) (hvx ▸ hvle)⟩

/-- Agreement of two valuations on a finite generating set transports the
actual attained ideal value; the ring is integral for both valuations. -/
theorem HasValue.of_generators_eq {I : FractionalIdeal R⁰ K} {v w : Valuation K ℤᵐ⁰} {n : ℤ}
    (hI : HasValue I v n) (hv : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hw : ∀ r : R, w (algebraMap R K r) ≤ 1)
    (s : Finset K) (hs : Submodule.span R (s : Set K) = I)
    (heq : ∀ x ∈ s, v x = w x) : HasValue I w n := by
  apply hasValue_of_span w hw I (s : Set K) hs n
  · intro x hx
    rw [← heq x hx]
    apply hI.1 x
    change x ∈ (I : Submodule R K)
    rw [← hs]
    exact Submodule.subset_span hx
  · obtain ⟨x, hx, hval⟩ := hI.generator_attains hv s hs
    exact ⟨x, hx, (heq x hx).symm.trans hval⟩

end UnconditionalCounterexample.FractionalIdealProfiles
