import UnconditionalCounterexample.Variations.DimensionWordDirections
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous observations of bounded-degree polynomial stages
-/

namespace UnconditionalCounterexample.Variations

open MvPolynomial Filter
open scoped Topology

variable {K E σ : Type*} [NontriviallyNormedField K] [NontriviallyNormedField E]
  [NormedAlgebra K E] [Fintype σ]

/-- A finite box containing all monomials of total degree at most the bound. -/
noncomputable def monomialBox (σ : Type*) [Fintype σ] (d : ℕ) : Finset (σ →₀ ℕ) := by
  classical
  exact Finset.univ.image (fun b : σ → Fin (d+1) ↦ Finsupp.equivFunOnFinite.symm fun j ↦ (b j : ℕ))

theorem support_subset_monomialBox (f : MvPolynomial σ K) {d : ℕ} (hd : f.totalDegree ≤ d) :
    f.support ⊆ monomialBox σ d := by
  classical
  intro m hm
  have h (i : σ) : m i ≤ d := (degreeOf_le_iff.mp (degreeOf_le_totalDegree f i) m hm).trans hd
  exact Finset.mem_image.mpr ⟨(fun j ↦ ⟨m j, Nat.lt_succ_iff.mpr (h j)⟩), Finset.mem_univ _, by ext; rfl⟩

/-- Reconstruct the lower-degree polynomial by observing a finite box of coefficients. -/
noncomputable def polynomialFromBox (d : ℕ) (f : (σ →₀ ℕ) → K) : MvPolynomial σ K :=
  ∑ m ∈ monomialBox σ d, monomial m (f m)

theorem polynomialFromBox_coeff (f : MvPolynomial σ K) {d : ℕ} (hd : f.totalDegree ≤ d) :
    polynomialFromBox d f.coeff = f := by
  classical
  calc
    polynomialFromBox d f.coeff = ∑ m ∈ f.support, monomial m (f.coeff m) := by
      symm
      apply Finset.sum_subset (support_subset_monomialBox f hd)
      intro m _ hm
      simp [notMem_support_iff.mp hm]
    _ = f := f.as_sum.symm

/-- Linear polynomial observations are continuous on the truncated coefficient vectors. -/
theorem continuous_observe_box {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]
    (d : ℕ) (L : MvPolynomial σ K →ₗ[K] V) :
    Continuous (fun z ↦ L (polynomialFromBox d z)) := by
  classical
  have he (z : (σ →₀ ℕ) → K) : L (polynomialFromBox d z) =
      ∑ m ∈ monomialBox σ d, z m • L (monomial m 1) := by
    simp only [polynomialFromBox, map_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [← map_smul]
    congr 1
    rw [smul_monomial, smul_eq_mul, mul_one]
  simp_rw [he]
  fun_prop

/-- Each actual localized-word gradient is continuous under lower-coefficient perturbation
with fixed leading form and denominator. -/
theorem continuous_wordGradient_box (d : ℕ) (leading H : MvPolynomial σ K)
    (u : σ → E) (a : ℕ) :
    Continuous (fun z ↦ residueWordGradient u (leading + polynomialFromBox d z) H a) := by
  apply continuous_pi
  intro j
  let ev := (aeval (R := K) u).toLinearMap
  let dj := ev.comp (pderiv j).toLinearMap
  have h0 := (continuous_const (y := ev leading)).add (continuous_observe_box d ev)
  have h1 := (continuous_const (y := dj leading)).add (continuous_observe_box d dj)
  have heq (z : (σ →₀ ℕ) → K) : residueWordGradient u (leading + polynomialFromBox d z) H a j =
      ((a : E) * (ev leading + ev (polynomialFromBox d z))^(a-1) *
        (dj leading + dj (polynomialFromBox d z)) * ev H -
       (ev leading + ev (polynomialFromBox d z))^a * dj H) / (ev H)^2 := by
    simp [ev, dj, residueWordGradient, mul_assoc]
  simp_rw [heq]
  exact ((((continuous_const.mul (h0.pow _)).mul h1).mul_const _).sub
    ((h0.pow _).mul_const _)).div_const _

end UnconditionalCounterexample.Variations
