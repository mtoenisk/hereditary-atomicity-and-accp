import UnconditionalCounterexample.Variations.MultivariateSelection
import UnconditionalCounterexample.Variations.MultivariateInfinity

/-!
# Open local stage conditions and integral models

The simultaneous stage selector accepts arbitrary neighborhoods of the
local coefficient vectors. Its concrete leading forms are the rational
Vandermonde forms of the generic recovery theorem.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial Filter
open scoped Topology

variable {σ ι k : Type*} [Fintype σ] [DecidableEq σ] [Field k] [CharZero k]

theorem exists_radii {κ E : Type*} [NormedAddCommGroup E]
    (x : κ → E) {U : Set (κ → E)} (hU : U ∈ 𝓝 x) :
    ∃ ε : κ → ℝ, (∀ j, 0 < ε j) ∧ ∀ y : κ → E, (∀ j, ‖y j - x j‖ < ε j) → y ∈ U := by
  rw [nhds_pi] at hU
  obtain ⟨I,_,V,hV,hsub⟩ := Filter.mem_pi.mp hU
  choose ε hε hball using fun j => Metric.mem_nhds_iff.mp (hV j)
  exact ⟨ε,hε, fun y hy => hsub (fun j _ => hball j (by simpa only [Metric.mem_ball, dist_eq_norm] using hy j))⟩

/-- Select the actual stage in local product neighborhoods of coefficient
vectors. Pullbacks of simultaneous value and gradient tests give exactly
such neighborhoods. -/
theorem exists_stage_of_open [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (d : ℕ) (hd : 2 ≤ d) (l : MvPolynomial (Option σ) ℚ)
    (hl : l.totalDegree ≤ 1) (ha : axis l = Polynomial.X)
    (locals : ∀ i, MvPolynomial (Option σ) ℚ_[p i]) (hdeg : ∀ i, (locals i).totalDegree < d)
    (U : ∀ i, Set (((Option σ) →₀ ℕ) → ℚ_[p i]))
    (hU : ∀ i, U i ∈ 𝓝 (fun m => (locals i).coeff m))
    (T : Finset (MultivariateStage.Test k (Option σ))) (hT : ∀ t ∈ T, t.Valid) :
    ∃ q : MvPolynomial (Option σ) ℚ, q.totalDegree < d ∧
      Irreducible (l ^ d + q) ∧ (l ^ d + q).totalDegree = d ∧
      (∀ m, ∀ r : ℕ, r.Prime → r ∣ (q.coeff m).den → ∃ i, r = p i) ∧
      (∀ i, (fun m => ((q.coeff m : ℚ) : ℚ_[p i])) ∈ U i) ∧
      (∀ m, HasAuxiliaryResidue ell (q.coeff m) (if m = 0 then (ell : ZMod (ell^2)) else 0)) ∧
      ∀ t ∈ T, t.Holds (MvPolynomial.map (algebraMap ℚ k) (l ^ d + q)) := by
  choose ε hε hmem using fun i => exists_radii (fun m => (locals i).coeff m) (hU i)
  obtain ⟨q,hq,hi,hdegq,hs,hclose,hr,ht⟩ := exists_stage p hinj ell hfresh d hd l hl ha
    locals hdeg (fun m i => ε i m) (fun m i => hε i m) T hT
  exact ⟨q,hq,hi,hdegq,hs, fun i => hmem i _ (fun m => hclose m i),hr,ht⟩

/-- The coordinate order `none, some 0, ..., some (r-1)` writes the
Vandermonde form as the first variable plus its weighted companions. -/
def leadingForm (r s : ℕ) {R : Type*} [CommSemiring R] : MvPolynomial (Option (Fin r)) R :=
  X none + ∑ j : Fin r, C ((s : R) ^ (j.val+1)) * X (some j)

theorem leadingForm_eq_rename (r s : ℕ) :
    leadingForm r s = rename (_root_.finSuccEquiv r) (MultivariateInfinity.vandermondeForm (k := ℚ) (r+1) s) := by
  rw [MultivariateInfinity.vandermondeForm, Fin.sum_univ_succ, map_add, map_sum]
  simp [leadingForm]

theorem leadingForm_degree (r s : ℕ) : (leadingForm r s (R := ℚ)).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans (max_le (by simp) (totalDegree_finsetSum_le (fun j _ => ?_)))
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

theorem leadingForm_axis (r s : ℕ) : axis (leadingForm r s (R := ℚ)) = Polynomial.X := by
  have h₁ : axis (X none : MvPolynomial (Option (Fin r)) ℚ) = Polynomial.X := by simp [axis]
  have h₀ (j : Fin r) : axis (X (some j) : MvPolynomial (Option (Fin r)) ℚ) = 0 := by simp [axis]
  simp only [leadingForm, map_add, map_sum, map_mul, h₁, h₀, mul_zero, Finset.sum_const_zero, add_zero]

theorem vandermonde_degree (r s : ℕ) : (MultivariateInfinity.vandermondeForm (k := ℚ) (r+1) s).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C,totalDegree_X])

theorem vandermonde_axis (r s : ℕ) : axis (rename (_root_.finSuccEquiv r)
    (MultivariateInfinity.vandermondeForm (k := ℚ) (r+1) s)) = Polynomial.X := by
  rw [← leadingForm_eq_rename, leadingForm_axis]

/-- Native finite-coordinate version of the selector for the stage scheduler. -/
theorem exists_vandermonde_stage [Fintype ι] (r s : ℕ)
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (d : ℕ) (hd : 2 ≤ d)
    (locals : ∀ i, MvPolynomial (Fin (r+1)) ℚ_[p i]) (hdeg : ∀ i, (locals i).totalDegree < d)
    (U : ∀ i, Set (((Fin (r+1)) →₀ ℕ) → ℚ_[p i])) (hU : ∀ i, U i ∈ 𝓝 (fun m => (locals i).coeff m))
    (T : Finset (MultivariateStage.Test k (Fin (r+1)))) (hT : ∀ t ∈ T, t.Valid) :
    let l := MultivariateInfinity.vandermondeForm (k := ℚ) (r+1) s
    ∃ q : MvPolynomial (Fin (r+1)) ℚ, q.totalDegree < d ∧
      Irreducible (l ^ d + q) ∧ (l ^ d + q).totalDegree = d ∧
      (∀ m, ∀ v : ℕ, v.Prime → v ∣ (q.coeff m).den → ∃ i, v = p i) ∧
      (∀ i, (fun m => ((q.coeff m : ℚ) : ℚ_[p i])) ∈ U i) ∧
      (∀ m, HasAuxiliaryResidue ell (q.coeff m) (if m = 0 then (ell : ZMod (ell^2)) else 0)) ∧
      ∀ t ∈ T, t.Holds (MvPolynomial.map (algebraMap ℚ k) (l ^ d + q)) := by
  choose ε hε hmem using fun i => exists_radii (fun m => (locals i).coeff m) (hU i)
  obtain ⟨q,hq,hi,hdegq,hs,hclose,hr,ht⟩ := exists_stage_equiv (_root_.finSuccEquiv r) p hinj ell hfresh d hd
    (MultivariateInfinity.vandermondeForm (k := ℚ) (r+1) s) (vandermonde_degree r s) (vandermonde_axis r s)
    locals hdeg (fun m i => ε i m) (fun m i => hε i m) T hT
  exact ⟨q,hq,hi,hdegq,hs, fun i => hmem i _ (fun m => hclose m i),hr,ht⟩

/-- Every coefficient of the selected lower part lifts to the integral
coefficient ring away from the current finite list. -/
theorem exists_integral_model {τ : Type*} (p : ι → ℕ) (q : MvPolynomial τ ℚ)
    (hs : ∀ m, ∀ r : ℕ, r.Prime → r ∣ (q.coeff m).den → ∃ i, r = p i)
    (v : ℕ) [Fact v.Prime] (hfresh : ∀ i, p i ≠ v) :
    ∃ Q : MvPolynomial τ ℤ_[v],
      MvPolynomial.map (algebraMap ℤ_[v] ℚ_[v]) Q = MvPolynomial.map (algebraMap ℚ ℚ_[v]) q := by
  classical
  choose a ha using fun m => CoefficientApproximation.exists_padicInt_of_denominator_support p
    (q.coeff m) (hs m) v hfresh
  refine ⟨∑ m ∈ q.support, monomial m (a m), ?_⟩
  conv_rhs => rw [q.as_sum]
  simp only [map_sum, map_monomial]
  exact Finset.sum_congr rfl fun m _ => congrArg (monomial m) (ha m)

theorem map_leadingForm {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (r s : ℕ) : MvPolynomial.map φ (leadingForm r s) = leadingForm r s := by
  simp [leadingForm]

/-- The entire polynomial, including the scheduled top form, has an actual
integral polynomial model at each unassigned prime. -/
theorem exists_integral_stage_model (r s d : ℕ) (p : ι → ℕ) (q : MvPolynomial (Option (Fin r)) ℚ)
    (hs : ∀ m, ∀ v : ℕ, v.Prime → v ∣ (q.coeff m).den → ∃ i, v = p i)
    (v : ℕ) [Fact v.Prime] (hfresh : ∀ i, p i ≠ v) :
    ∃ Q : MvPolynomial (Option (Fin r)) ℤ_[v],
      MvPolynomial.map (algebraMap ℤ_[v] ℚ_[v]) Q =
        MvPolynomial.map (algebraMap ℚ ℚ_[v]) ((leadingForm r s)^d + q) := by
  obtain ⟨q',hq⟩ := exists_integral_model p q hs v hfresh
  exact ⟨(leadingForm r s)^d + q', by simp only [map_add, map_pow, map_leadingForm, hq]⟩

end UnconditionalCounterexample.MultivariateSelection
