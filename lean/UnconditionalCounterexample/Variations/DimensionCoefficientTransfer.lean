import UnconditionalCounterexample.Variations.DimensionScaledTransfer
import UnconditionalCounterexample.Variations.DimensionLocalStage

namespace UnconditionalCounterexample.Variations

open MvPolynomial

/-- Linear test measuring the coefficient after scaling every coordinate by s and the
polynomial by t. These are the coefficient observations used by the local stage. -/
noncomputable def scaledCoefficient {σ K : Type*} [Field K] (s t : K) (m : σ →₀ ℕ) :
    MvPolynomial σ K →ₗ[K] K := (t / m.prod (fun _ n ↦ s^n)) • lcoeff K m

/-- The coefficient inequalities imposed by the chosen p-adic neighborhood imply an
exact congruence after evaluating in the actual subring containing the scaled coordinates. -/
theorem evaluated_congruence_of_scaledCoefficient {K A σ : Type*} [NontriviallyNormedField K]
    [CommRing A] [Algebra K A] (T : Subring A) (z : σ → A) (s t δ l : K)
    (hs : s ≠ 0) (hδ : δ ≠ 0) (hscalar : ∀ c : K, ‖c‖ ≤ 1 → algebraMap K A c ∈ T)
    (hz : ∀ j, algebraMap K A s * z j ∈ T) (F V : MvPolynomial σ K)
    (hcoeff : ∀ m ∈ (C (t*l) * F - C t * V).support,
      ‖l * scaledCoefficient s t m F - scaledCoefficient s t m V‖ ≤ ‖δ‖) :
    ∃ e ∈ T, algebraMap K A (t*l) * aeval z F - algebraMap K A t * aeval z V =
      algebraMap K A δ * e := by
  obtain ⟨e, he, hh⟩ := scaled_multivariate_transfer T z s δ hz (C (t*l) * F - C t * V) (by
    intro m hm
    let v := m.prod fun _ n ↦ s^n
    have hv : v ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ hs
    let c := (l * scaledCoefficient s t m F - scaledCoefficient s t m V) / δ
    have hc : ‖c‖ ≤ 1 := by
      rw [show ‖c‖ = _ from norm_div _ _, div_le_one (norm_pos_iff.mpr hδ)]
      exact hcoeff m hm
    refine ⟨c, hscalar c hc, ?_⟩
    change _ = δ * ((l * ((t / v) * F.coeff m) - (t / v) * V.coeff m) / δ) * v
    simp only [coeff_sub, coeff_C_mul]
    field_simp)
  exact ⟨e, he, by simpa only [map_sub, map_mul, aeval_C] using hh⟩

end UnconditionalCounterexample.Variations
