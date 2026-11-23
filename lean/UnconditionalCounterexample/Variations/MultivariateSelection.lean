import UnconditionalCounterexample.Variations.MultivariateSelectionEisenstein
import UnconditionalCounterexample.Variations.MultivariateStage

/-!
# Simultaneous multivariate finite stage

The lower coefficients approximate prescribed p-adic polynomials, are
integral away from the processed primes and obey the auxiliary prime-square
Eisenstein congruences. The remaining affine freedom meets every finite
geometric test on that same polynomial.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial

variable {τ σ ι k : Type*} [Fintype ι] [Field k] [CharZero k]

private def index : Option τ → τ →₀ ℕ
  | none => 0
  | some i => Finsupp.single i 1

private theorem index_injective : Function.Injective (index (τ := τ)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [index, Finsupp.single_left_inj]
  exact (Finsupp.single_ne_zero.mpr one_ne_zero) h.symm

/-- The constant and linear terms account for all coefficient changes used by
the finite geometric avoidance theorem. -/
private theorem perturb_eq_sum [Fintype τ] (p : MvPolynomial τ ℚ) (z : Option τ → ℚ) :
    MultivariateStage.perturb p z = p + ∑ i, monomial (index i) (z i) := by
  classical
  rw [Fintype.sum_option]
  simp only [MultivariateStage.perturb, index, C_mul_X_eq_monomial, add_assoc]
  rfl

/-- The rational coefficient has the indicated integral prime-square residue. -/
def HasAuxiliaryResidue (ell : ℕ) [Fact ell.Prime] (q : ℚ) (r : ZMod (ell^2)) : Prop :=
  ∃ x : ℤ_[ell], (x : ℚ_[ell]) = (q : ℚ_[ell]) ∧ PadicInt.toZModPow 2 x = r

private theorem exists_progressions {κ : Type*} (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hinj : Function.Injective p) (x : κ → ∀ i, ℚ_[p i]) (ε : κ → ι → ℝ)
    (hε : ∀ m i, 0 < ε m i) (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (res : κ → ZMod (ell^2)) :
    ∃ b s : κ → ℚ, (∀ m, s m ≠ 0) ∧ ∀ m (n : ℕ),
      let a := b m + s m * n
      (∀ q : ℕ, q.Prime → q ∣ a.den → ∃ i, q = p i) ∧
      (∀ i, ‖(a : ℚ_[p i]) - x m i‖ < ε m i) ∧ HasAuxiliaryResidue ell a (res m) := by
  classical
  obtain ⟨D,z,M,h⟩ := CoefficientApproximation.exists_supported_rational_grid
    p hinj x ε hε ell Fact.out hfresh 2 res
  let b (m : κ) : ℚ := z m / (D m : ℚ)
  let s (m : κ) : ℚ := M m / (D m : ℚ)
  refine ⟨b,s,fun m => div_ne_zero (Nat.cast_ne_zero.mpr (h m).2.2.1) (Nat.cast_ne_zero.mpr (h m).1),?_⟩
  intro m n
  let a : ℚ := b m + s m * n
  have ha : a = ((z m + M m * (n : ℤ) : ℤ) : ℚ) / D m := by
    simp only [a, b, s, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring
  obtain ⟨hden,hclose,hr⟩ := (h m).2.2.2 n
  have hs : ∀ q : ℕ, q.Prime → q ∣ a.den → ∃ i, q = p i := fun q hq hd =>
    (h m).2.1 q hq (hd.trans (ha ▸ hden))
  obtain ⟨u,hu⟩ := CoefficientApproximation.exists_padicInt_of_denominator_support p a hs ell hfresh
  refine ⟨hs, fun i => ?_, u, hu, ShiftedEisenstein.toZModPow_eq_of_cleared
    u a hu _ _ (h m).1 ?_ ha 2 (res m) hr⟩
  · change ‖(a : ℚ_[p i]) - x m i‖ < ε m i
    simpa only [ha] using hclose i
  · intro hd
    obtain ⟨i,hi⟩ := (h m).2.1 ell Fact.out hd
    exact hfresh i hi.symm

/-- A single rational polynomial meets the prescribed local coefficient balls,
retains its leading form, is irreducible, and meets every geometric test.
The finite support used to construct it is determined by the local targets. -/
theorem exists_stage_equiv [Fintype τ] [DecidableEq τ] [DecidableEq σ] (e : τ ≃ Option σ)
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (d : ℕ) (hd : 2 ≤ d) (l : MvPolynomial τ ℚ)
    (hl : l.totalDegree ≤ 1) (ha : axis (rename e l) = Polynomial.X)
    (locals : ∀ i, MvPolynomial τ ℚ_[p i]) (hdeg : ∀ i, (locals i).totalDegree < d)
    (ε : (τ →₀ ℕ) → ι → ℝ) (hε : ∀ m i, 0 < ε m i)
    (T : Finset (MultivariateStage.Test k τ)) (hT : ∀ t ∈ T, t.Valid) :
    ∃ q : MvPolynomial τ ℚ, q.totalDegree < d ∧
      Irreducible (l ^ d + q) ∧ (l ^ d + q).totalDegree = d ∧
      (∀ m, ∀ r : ℕ, r.Prime → r ∣ (q.coeff m).den → ∃ i, r = p i) ∧
      (∀ m i, ‖((q.coeff m : ℚ) : ℚ_[p i]) - (locals i).coeff m‖ < ε m i) ∧
      (∀ m, HasAuxiliaryResidue ell (q.coeff m) (if m = 0 then (ell : ZMod (ell^2)) else 0)) ∧
      ∀ t ∈ T, t.Holds (MvPolynomial.map (algebraMap ℚ k) (l ^ d + q)) := by
  classical
  let res (m : τ →₀ ℕ) : ZMod (ell^2) := if m = 0 then ell else 0
  obtain ⟨b,s,hs,hgrid⟩ := exists_progressions p hinj (fun m i => (locals i).coeff m)
    ε hε ell hfresh res
  let A : Finset (τ →₀ ℕ) := Finset.univ.image (index (τ := τ))
  let S : Finset (τ →₀ ℕ) := Finset.univ.biUnion (fun i => (locals i).support) \ A
  let base := ∑ m ∈ S, monomial m (b m)
  have hb : base.totalDegree < d := by
    apply lt_of_le_of_lt (b := d-1) (totalDegree_finsetSum_le (fun m hm => ?_)) (by omega)
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hm).1
    apply (totalDegree_monomial_le m _).trans
    change (m.sum fun _ e => e) ≤ d - 1
    have := (le_totalDegree hi).trans_lt (hdeg i)
    omega
  obtain ⟨n,q,hq,hform,htests⟩ := MultivariateStage.exists_rational_perturbation l base d hd hb T hT
    (fun i => b (index i)) (fun i => s (index i)) (fun i => hs _) (fun _ => 0)
  let z (i : Option τ) := b (index i) + s (index i) * (n i : ℚ)
  have hform' : q = base + ∑ i, monomial (index i) (z i) := by
    simpa only [Nat.zero_add, perturb_eq_sum, z] using hform
  have hcoef (m : τ →₀ ℕ) :
      (∀ r : ℕ, r.Prime → r ∣ (q.coeff m).den → ∃ i, r = p i) ∧
      (∀ i, ‖((q.coeff m : ℚ) : ℚ_[p i]) - (locals i).coeff m‖ < ε m i) ∧
      HasAuxiliaryResidue ell (q.coeff m) (res m) := by
    have hadd (x y : MvPolynomial τ ℚ) : (x+y).coeff m = x.coeff m + y.coeff m := rfl
    rw [hform', hadd, show base.coeff m = (if m ∈ S then b m else 0) by
      simp [base, coeff_monomial], coeff_sum]
    by_cases hA : m ∈ A
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hA
      have hS : index j ∉ S := fun h => (Finset.mem_sdiff.mp h).2 hA
      simp only [ite_eq_right hS, zero_add, coeff_monomial, index_injective.eq_iff, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      exact hgrid _ (n j)
    · have hnot (j : Option τ) : index j ≠ m := fun h => hA (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j))
      simp only [coeff_monomial, ite_eq_right (hnot _), Finset.sum_const_zero, add_zero]
      by_cases hS : m ∈ S
      · simpa [hS] using hgrid m 0
      · have hm : m ≠ 0 := fun hm => hA (hm ▸ Finset.mem_image_of_mem _ (Finset.mem_univ none))
        have hzero (i : ι) : (locals i).coeff m = 0 := notMem_support_iff.mp fun hi =>
          hS (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩, hA⟩)
        simp only [ite_eq_right hS, Rat.den_zero, Nat.dvd_one, Rat.cast_zero, hzero, sub_zero, norm_zero]
        exact ⟨fun r hr h => False.elim (hr.ne_one h), hε m, 0, by simp, by simp [res,hm]⟩
  obtain ⟨hirr,hdegree⟩ := irreducible_leading_power_equiv e ell l q d (by omega) hl ha hq (fun m => (hcoef m).2.2)
  exact ⟨q,hq,hirr,hdegree,fun m => (hcoef m).1,fun m => (hcoef m).2.1,fun m => (hcoef m).2.2,htests⟩

/-- The selector with the first variable labeled `none`. -/
theorem exists_stage [Fintype σ] [DecidableEq σ]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (d : ℕ) (hd : 2 ≤ d) (l : MvPolynomial (Option σ) ℚ)
    (hl : l.totalDegree ≤ 1) (ha : axis l = Polynomial.X)
    (locals : ∀ i, MvPolynomial (Option σ) ℚ_[p i]) (hdeg : ∀ i, (locals i).totalDegree < d)
    (ε : ((Option σ) →₀ ℕ) → ι → ℝ) (hε : ∀ m i, 0 < ε m i)
    (T : Finset (MultivariateStage.Test k (Option σ))) (hT : ∀ t ∈ T, t.Valid) :
    ∃ q : MvPolynomial (Option σ) ℚ, q.totalDegree < d ∧
      Irreducible (l ^ d + q) ∧ (l ^ d + q).totalDegree = d ∧
      (∀ m, ∀ r : ℕ, r.Prime → r ∣ (q.coeff m).den → ∃ i, r = p i) ∧
      (∀ m i, ‖((q.coeff m : ℚ) : ℚ_[p i]) - (locals i).coeff m‖ < ε m i) ∧
      (∀ m, HasAuxiliaryResidue ell (q.coeff m) (if m = 0 then (ell : ZMod (ell^2)) else 0)) ∧
      ∀ t ∈ T, t.Holds (MvPolynomial.map (algebraMap ℚ k) (l ^ d + q)) :=
  exists_stage_equiv (Equiv.refl (Option σ)) p hinj ell hfresh d hd l hl
    (by simpa using ha) locals hdeg ε hε T hT

end UnconditionalCounterexample.MultivariateSelection
