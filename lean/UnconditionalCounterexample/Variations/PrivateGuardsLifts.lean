import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Algebra.MvPolynomial.PDeriv
import UnconditionalCounterexample.Variations.IndependentTuples
import UnconditionalCounterexample.GuardSupport

/-!
# Independent private lifts of multivariate simple roots

Specializing all coordinates except one turns a unit partial derivative into
a univariate Hensel condition. Shift the polynomial by p, lift the resulting
equation, and perturb inside an open neighbourhood where all nonzero
polynomial values have constant norm.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial Filter
open scoped Topology

private def slice {R σ : Type*} [CommRing R] [DecidableEq σ] (c : σ → R) (i : σ) :
    MvPolynomial σ R →+* Polynomial R :=
  eval₂Hom Polynomial.C (fun j => if j = i then Polynomial.X else Polynomial.C (c j))

private theorem eval_slice {R σ : Type*} [CommRing R] [DecidableEq σ] (c : σ → R)
    (i : σ) (z : R) (f : MvPolynomial σ R) :
    (slice c i f).eval z = eval (Function.update c i z) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [slice]
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
    rw [map_mul, Polynomial.eval_mul, hf, map_mul, eval_X]
    by_cases h : j = i
    · subst j
      simp [slice]
    · simp [slice, h]

private theorem derivative_slice {R σ : Type*} [CommRing R] [DecidableEq σ] (c : σ → R)
    (i : σ) (f : MvPolynomial σ R) :
    (slice c i f).derivative = slice c i (pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [slice]
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
    rw [map_mul, Polynomial.derivative_mul, hf, pderiv_mul, map_add, map_mul, map_mul]
    by_cases h : j = i
    · subst j
      simp [slice]
    · simp [slice, h, pderiv_X_of_ne h]

/-- The private argument can be made algebraically independent while preserving
each residue and all specified nonzero polynomial norms. -/
theorem exists_independent_same_norms (p r : ℕ) [Fact p.Prime] (c : Fin r → ℤ_[p])
    (S : Finset (MvPolynomial (Fin r) ℚ_[p]))
    (hS : ∀ f ∈ S, eval (fun i => (c i).val) f ≠ 0) :
    ∃ a : Fin r → ℤ_[p], AlgebraicIndependent ℚ (fun i => (a i).val) ∧
      (∀ i, PadicInt.toZMod (a i) = PadicInt.toZMod (c i)) ∧
      ∀ f ∈ S, ‖eval (fun i => (a i).val) f‖ = ‖eval (fun i => (c i).val) f‖ := by
  let z (i : Fin r) := (c i).val
  have hall : ∀ᶠ x in 𝓝 z, ∀ f ∈ S, ‖eval x f‖ = ‖eval z f‖ := by
    apply (eventually_all_finset S).2
    intro f hf
    have hn := f.continuous_eval.continuousAt (x := z)
    filter_upwards [hn (Metric.ball_mem_nhds _ (norm_pos_iff.mpr (hS f hf)))] with x hx
    exact Padic.norm_eq_of_norm_sub_lt_right (by simpa [Metric.mem_ball, dist_eq_norm] using hx)
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hall
  obtain ⟨a, ha, hclose⟩ := IndependentTuples.exists_padic_lifts p r c (fun _ => ε) (fun _ => hε)
  refine ⟨a, ha, fun i => (hclose i).1, he (Metric.mem_ball.mpr ((dist_pi_lt_iff hε).mpr ?_))⟩
  intro i
  simpa only [z,dist_eq_norm] using (hclose i).2

/-- At a smooth integral p-adic point, a congruent integral point takes
the precise value p. In particular the resulting nonzero value has order one. -/
theorem exists_point_value_prime (p : ℕ) [Fact p.Prime] {r : ℕ}
    (G : MvPolynomial (Fin r) ℤ_[p]) (c : Fin r → ℤ_[p]) (i : Fin r)
    (hg : eval c G = 0) (hd : IsUnit (eval c (pderiv i G))) :
    ∃ b : Fin r → ℤ_[p], (∀ j, PadicInt.toZMod (b j) = PadicInt.toZMod (c j)) ∧
      eval b G = (p : ℤ_[p]) := by
  classical
  let F := slice c i G - Polynomial.C (p : ℤ_[p])
  have hder : ‖Polynomial.aeval (c i) F.derivative‖ = 1 := by
    simpa only [F, Polynomial.coe_aeval_eq_eval, Polynomial.derivative_sub, Polynomial.derivative_C,
      sub_zero, derivative_slice, eval_slice, Function.update_eq_self] using PadicInt.isUnit_iff.mp hd
  have hval : ‖Polynomial.aeval (c i) F‖ < 1 := by
    simp only [F, Polynomial.coe_aeval_eq_eval, Polynomial.eval_sub, Polynomial.eval_C, eval_slice,
      Function.update_eq_self, hg, zero_sub, norm_neg]
    simpa only [PadicInt.norm_def, PadicInt.coe_natCast] using Padic.norm_p_lt_one (p := p)
  obtain ⟨x,hx,hnear,_,_⟩ := hensels_lemma (F := F) (a := c i) (by rwa [hder, one_pow])
  refine ⟨Function.update c i x, ?_, ?_⟩
  · intro j
    by_cases h : j = i
    · subst j
      rw [Function.update_self]
      apply EvaluationChoices.toZMod_eq_of_norm_sub_lt_one p
      exact hder ▸ hnear
    · rw [Function.update_of_ne h]
  · simpa only [F, Polynomial.coe_aeval_eq_eval, Polynomial.eval_sub, Polynomial.eval_C, eval_slice,
      sub_eq_zero] using hx

/-- Values of integral polynomials at coordinatewise congruent integral
tuples have the same residue. -/
theorem residue_eval_congr {p r : ℕ} [Fact p.Prime] (H : MvPolynomial (Fin r) ℤ_[p])
    {a b : Fin r → ℤ_[p]} (h : ∀ i, PadicInt.toZMod (a i) = PadicInt.toZMod (b i)) :
    PadicInt.toZMod (eval a H) = PadicInt.toZMod (eval b H) := by
  rw [map_eval, map_eval]
  exact congrArg (fun t => eval t (MvPolynomial.map PadicInt.toZMod H)) (funext h)

/-- An actual independent private site. At the lifted tuple G has order one,
and every integral test which was a unit at the smooth point stays a unit. -/
theorem exists_private_lift (p : ℕ) [Fact p.Prime] {r : ℕ}
    (G : MvPolynomial (Fin r) ℤ_[p]) (c : Fin r → ℤ_[p]) (i : Fin r)
    (hg : eval c G = 0) (hd : IsUnit (eval c (pderiv i G))) :
    ∃ a : Fin r → ℤ_[p], AlgebraicIndependent ℚ (fun i => (a i).val) ∧
      (∀ j, PadicInt.toZMod (a j) = PadicInt.toZMod (c j)) ∧
      ‖eval a G‖ = ‖(p : ℚ_[p])‖ ∧
      ∀ H : MvPolynomial (Fin r) ℤ_[p], IsUnit (eval c H) → IsUnit (eval a H) := by
  classical
  obtain ⟨b, hb, hG⟩ := exists_point_value_prime p G c i hg hd
  let g := MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) G
  have hval (t : Fin r → ℤ_[p]) : (eval t G).val = eval (fun i => (t i).val) g :=
    map_eval (algebraMap ℤ_[p] ℚ_[p]) t G
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨a,ha,hr,hn⟩ := exists_independent_same_norms p r b {g} (by
    intro f hf
    obtain rfl := Finset.mem_singleton.mp hf
    simpa only [← hval,hG,PadicInt.coe_natCast] using hp)
  have he (j) := (hr j).trans (hb j)
  refine ⟨a, ha, he, ?_, fun H hH => ?_⟩
  · simpa only [← hval, hG, PadicInt.coe_natCast, PadicInt.norm_def] using hn g (Finset.mem_singleton_self _)
  · exact (GuardSupport.padicInt_isUnit_iff_toZMod_ne_zero _).mpr
      ((residue_eval_congr H he).symm ▸ (GuardSupport.padicInt_isUnit_iff_toZMod_ne_zero _).mp hH)

end UnconditionalCounterexample.Variations.PrivateGuards
