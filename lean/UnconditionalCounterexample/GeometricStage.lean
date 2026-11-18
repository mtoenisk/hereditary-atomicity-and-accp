import UnconditionalCounterexample.SeparationExclusions
import UnconditionalCounterexample.ShiftedEisenstein

/-!
# Geometric exclusions in the full coefficient space

The universal fixed-constant monic family yields actual point, pair, and
first-derivative test polynomials in all middle coefficients. Their evaluations
are exactly the requested geometric inequalities. Valid tests are proper:
the checked two-coefficient family supplies a witness inside this full family.

The final selection theorem combines these exclusions with shifted Eisenstein
and local approximation. Every output concerns the same rational coefficient
vector and the same resulting polynomial.
-/

noncomputable section
namespace UnconditionalCounterexample.GeometricStage
open Polynomial SeparationExclusions ShiftedEisenstein

variable {K : Type*} [Field K]

/-- The fixed-constant monic family over the ring of all middle coefficient variables. -/
def universalFamily (n : ℕ) (C0 : K) : (MvPolynomial (Fin n) K)[X] :=
  monicFamily n (MvPolynomial.C C0) MvPolynomial.X

theorem universalFamily_map (n : ℕ) (C0 : K) (a : Fin n → K) :
    (universalFamily n C0).map (MvPolynomial.eval a) = monicFamily n C0 a := by
  simp only [universalFamily, monicFamily_map, MvPolynomial.eval_C, MvPolynomial.eval_X]

def fullValue (n : ℕ) (C0 x : K) : MvPolynomial (Fin n) K :=
  (universalFamily n C0).eval (MvPolynomial.C x)

def fullDerivative (n : ℕ) (C0 x : K) : MvPolynomial (Fin n) K :=
  (universalFamily n C0).derivative.eval (MvPolynomial.C x)

theorem eval_fullValue (n : ℕ) (C0 x : K) (a : Fin n → K) :
    MvPolynomial.eval a (fullValue n C0 x) = (monicFamily n C0 a).eval x := by
  have h := Polynomial.eval_map_apply (p := universalFamily n C0) (MvPolynomial.eval a)
    (MvPolynomial.C x)
  simpa only [MvPolynomial.eval_C, universalFamily_map, fullValue] using h.symm

theorem eval_fullDerivative (n : ℕ) (C0 x : K) (a : Fin n → K) :
    MvPolynomial.eval a (fullDerivative n C0 x) =
      (monicFamily n C0 a).derivative.eval x := by
  have h := Polynomial.eval_map_apply (p := (universalFamily n C0).derivative) (MvPolynomial.eval a)
    (MvPolynomial.C x)
  rw [← Polynomial.derivative_map, universalFamily_map] at h
  simpa only [MvPolynomial.eval_C, fullDerivative] using h.symm

/-- The actual geometric bad equation in all middle coefficient variables. -/
def Test.polynomial (n : ℕ) (C0 : K) : Test K → MvPolynomial (Fin n) K
  | .point x => fullValue n C0 x
  | .pair x y m H => fullValue n C0 x ^ m * MvPolynomial.C (H.eval y) -
      fullValue n C0 y ^ m * MvPolynomial.C (H.eval x)
  | .tangent x m H => MvPolynomial.C (m : K) * fullValue n C0 x ^ (m - 1) *
      fullDerivative n C0 x * MvPolynomial.C (H.eval x) -
        fullValue n C0 x ^ m * MvPolynomial.C (H.derivative.eval x)

/-- Exact specialization semantics, with no nondegeneracy hypotheses. -/
theorem Test.holds_monicFamily_iff (n : ℕ) (C0 : K) (a : Fin n → K) (t : Test K) :
    t.Holds (monicFamily n C0 a) ↔ MvPolynomial.eval a (Test.polynomial n C0 t) ≠ 0 := by
  cases t <;> simp only [SeparationExclusions.Test.Holds, Test.polynomial,
    map_sub, map_mul, map_pow, MvPolynomial.eval_C, eval_fullValue, eval_fullDerivative]

variable [CharZero K]

/-- Properness follows by specializing to the checked linear/quadratic perturbations. -/
theorem Test.polynomial_ne_zero (n : ℕ) (hn : 2 ≤ n) (C0 : K) (hC : C0 ≠ 0)
    (t : Test K) (ht : t.Valid) : Test.polynomial n C0 t ≠ 0 := by
  classical
  let G : K[X] := monicFamily n C0 (fun _ => 0)
  have hG : G.coeff 0 ≠ 0 := by simpa only [G, monicFamily_coeff_zero] using hC
  obtain ⟨j, hj⟩ := exists_rational_grid_family G hG (fun _ => 0) (fun _ => 1)
    (fun _ => one_ne_zero) (fun _ => 0) {t} (by simpa using ht)
  let u : K := algebraMap ℚ K (0 + 1 * ((0 + j false : ℕ) : ℚ))
  let v : K := algebraMap ℚ K (0 + 1 * ((0 + j true : ℕ) : ℚ))
  let F : K[X] := family G u v
  have hFholds : t.Holds F := hj t (Finset.mem_singleton_self t)
  have hdegG : G.natDegree = n + 1 := (monicFamily_monic_degree n C0 (fun _ => 0)).2
  have hlarge : 2 < G.natDegree := by omega
  let a : Fin n → K := fun i => F.coeff (i.val + 1)
  have heq : monicFamily n C0 a = F := by
    apply monicFamily_eq n C0 a F
    · exact family_monic G (monicFamily_monic_degree n C0 (fun _ => 0)).1 hlarge u v
    · exact (family_natDegree G hlarge u v).trans hdegG
    · simp only [F, family_coeff_zero, G, monicFamily_coeff_zero]
    · intro i
      rfl
  have hnonzero : MvPolynomial.eval a (Test.polynomial n C0 t) ≠ 0 :=
    (Test.holds_monicFamily_iff n C0 a t).mp (heq.symm ▸ hFholds)
  intro hz
  apply hnonzero
  rw [hz, map_zero]


/-- The same rational polynomial gives the full-vector geometric specialization. -/
theorem Test.holds_map_monicFamily_iff (n : ℕ) (C0 : ℚ) (a : Fin n → ℚ) (t : Test K) :
    t.Holds ((monicFamily n C0 a).map (algebraMap ℚ K)) ↔
      MvPolynomial.eval (fun j => algebraMap ℚ K (a j))
        (Test.polynomial n (algebraMap ℚ K C0) t) ≠ 0 := by
  rw [monicFamily_map]
  exact Test.holds_monicFamily_iff n _ _ t

/-- One rational polynomial simultaneously realizes all arithmetic, approximation,
irreducibility, and valid geometric tests. All outputs refer to this same `q`. -/
theorem exists_irreducible_approximating_family_with_tests
    {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (n : ℕ) (hn : 2 ≤ n) (C0 : ℚ) (hC0 : C0 ≠ 0)
    (hCsupp : ∀ prime : ℕ, prime.Prime → prime ∣ C0.den → ∃ i, prime = p i)
    (x : Fin n → ∀ i, ℚ_[p i]) (ε : Fin n → ι → ℝ) (hε : ∀ c i, 0 < ε c i)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (c0 : ℤ_[ell]) (hc0 : (c0 : ℚ_[ell]) = C0)
    (hc : PadicInt.toZModPow 1 c0 = (-1) ^ (n + 1))
    (I : Finset (Test K)) (hI : ∀ t ∈ I, t.Valid) :
    ∃ q : Fin n → ℚ,
      (monicFamily n C0 q).Monic ∧ (monicFamily n C0 q).natDegree = n + 1 ∧
      (monicFamily n C0 q).coeff 0 = C0 ∧ Irreducible (monicFamily n C0 q) ∧
      (∀ k prime, prime.Prime → prime ∣ ((monicFamily n C0 q).coeff k).den → ∃ i, prime = p i) ∧
      (∀ j i, ‖(q j : ℚ_[p i]) - x j i‖ < ε j i) ∧
      (∀ t ∈ I, t.Holds ((monicFamily n C0 q).map (algebraMap ℚ K))) ∧
      ∃ g : ℤ_[ell][X], g.Monic ∧
        g.map (algebraMap ℤ_[ell] ℚ_[ell]) = (monicFamily n C0 q).map (algebraMap ℚ ℚ_[ell]) ∧
        g.map (PadicInt.toZModPow 1) = (X - C 1) ^ (n + 1) ∧
        PadicInt.toZModPow 2 (g.eval 1) = (ell : ZMod (ell ^ 2)) := by
  obtain ⟨q, hm, hd, hcoeff, hirr, hsupp, happ, hgeom, hmodel⟩ :=
    ShiftedEisenstein.exists_irreducible_approximating_family p hinj n (by omega) C0
      hCsupp x ε hε ell hfresh c0 hc0 hc I (Test.polynomial n (algebraMap ℚ K C0))
      (fun t ht => Test.polynomial_ne_zero n hn _ (by simpa only [map_zero] using (algebraMap ℚ K).injective.ne hC0) t (hI t ht))
  refine ⟨q, hm, hd, hcoeff, hirr, hsupp, happ, ?_, hmodel⟩
  intro t ht
  exact (Test.holds_map_monicFamily_iff n C0 q t).mpr (hgeom t ht)

end UnconditionalCounterexample.GeometricStage
