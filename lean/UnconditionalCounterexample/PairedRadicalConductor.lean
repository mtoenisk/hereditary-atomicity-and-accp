import UnconditionalCounterexample.RadicalConductor
import UnconditionalCounterexample.PolynomialJets
import Mathlib.Algebra.Ring.Prod

/-!
# Exact radical conductor at two rational points

At two distinct rational p-adic points, elements of the subring supply the lattice and
derivative witnesses. These show that the conductor exponent is one at each point.
-/

namespace UnconditionalCounterexample.RadicalConductor

open Polynomial PolynomialJets

theorem ideal_above_pair_pow_eq {K : Type*} [Field K] (I : Ideal K[X])
    (a b : K) (k : ℕ) (h : ((X - C a) * (X - C b)) ^ k ∈ I) :
    ∃ e ≤ k, ∃ d ≤ k, I = Ideal.span {((X - C a) ^ e) * ((X - C b) ^ d)} := by
  have hdiv := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp h
  rw [mul_pow] at hdiv
  obtain ⟨u, v, hu, hv, huv⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  obtain ⟨e, he, hae⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C a) k).mp hu
  obtain ⟨d, hd, had⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C b) k).mp hv
  refine ⟨e, he, d, hd, ?_⟩
  rw [← Ideal.span_singleton_generator I, huv]
  exact Ideal.span_singleton_eq_span_singleton.mpr (hae.mul_mul had)

/-- A ring map with the conductor as kernel has image containing no nonzero ideal. -/
theorem image_ideal_eq_bot_of_ker_eq_conductor
    {R A : Type*} [CommRing R] [CommRing A]
    (T : Subring R) (f : R →+* A) (hker : RingHom.ker f = conductorIdeal T)
    (J : Ideal A) (hJ : ∀ z ∈ J, z ∈ T.map f) : J = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨x, _, hxz⟩ := hJ z hz
  have hx : x ∈ conductorIdeal T := by
    intro y
    apply (LocalAlgebra.mem_iff_map_mem_of_kernel_subset T f ?_ (x * y)).mpr
    · rw [map_mul, hxz]
      exact hJ _ (J.mul_mem_right _ hz)
    · intro a ha
      apply conductorIdeal_subset T a
      rw [← hker]
      exact ha
  have hfx : f x = 0 := by
    change x ∈ RingHom.ker f
    rwa [hker]
  exact hxz.symm.trans hfx

noncomputable def leftSupport (A B : Type*) [CommRing A] [CommRing B] : A →ₙ+* A × B :=
  (NonUnitalRingHom.id A).prod 0

theorem leftSupport_injective (A B : Type*) [CommRing A] [CommRing B] :
    Function.Injective (leftSupport A B) := by
  intro x y h
  exact congrArg Prod.fst h

theorem leftSupport_action (A B : Type*) [CommRing A] [CommRing B]
    (z : A × B) (w : A) :
    z * leftSupport A B w = leftSupport A B (z.1 * w) := by
  ext <;> simp [leftSupport]

variable {K : Type*} [NontriviallyNormedField K]

set_option backward.isDefEq.respectTransparency.types false in
theorem twoPoint_left_exponent_le_one
    (O : Subring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (T : Subring (Polynomial K)) (a b : K) (hab : a ≠ b) (e d : ℕ)
    (hkernel : RingHom.ker (twoJetMap a b e d).toRingHom = conductorIdeal T)
    (hscalar : ∀ u ∈ O, C u ∈ T)
    (hclear : ∀ f : Polynomial K, ∃ c : K, c ≠ 0 ∧ C c * f ∈ T)
    (hvalue : ∀ f ∈ T, ‖f.eval a‖ ≤ 1)
    (hderivative : ∀ M : ℝ, ∃ f ∈ T, M < ‖f.derivative.eval a‖) :
    e ≤ 1 := by
  by_contra h
  have he2 : 2 ≤ e := by omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le he2
  have heN : e = n + 2 := by omega
  clear hn
  subst e
  let ψ := (twoJetMap a b (n + 2) d).toRingHom
  let S := T.map ψ
  let embed := leftSupport (Jet K (n + 2)) (Jet K d)
  have hno : ∀ J : Ideal (Jet K (n + 2) × Jet K d),
      (∀ z ∈ J, z ∈ S) → J = ⊥ :=
    image_ideal_eq_bot_of_ker_eq_conductor T ψ hkernel
  obtain ⟨r, hr⟩ := twoJetMap_surjective a b hab (n + 2) d
    (embed (jetMk K (n + 2) (X ^ n)))
  obtain ⟨c, hc, hcT⟩ := hclear r
  apply supported_no_ideal_of_unbounded
    (RingHom.fst _ _) embed (leftSupport_injective _ _)
    (leftSupport_action _ _) O hO S c hc hno
  · intro u hu
    have hm := T.mul_mem (hscalar u hu) hcT
    have hmS : ψ (C u * (C c * r)) ∈ S := ⟨_, hm, rfl⟩
    have heq : embed (jetMk K (n + 2) (C (c * u) * X ^ n)) =
        ψ (C u * (C c * r)) := by
      change embed (jetMk K (n + 2) (C (c * u) * X ^ n)) =
        twoJetMap a b (n + 2) d (C u * (C c * r))
      rw [map_mul (twoJetMap a b (n + 2) d) (C u) (C c * r),
        map_mul (twoJetMap a b (n + 2) d) (C c) r, hr]
      change (Ideal.Quotient.mk (truncIdeal K (n + 2)) (C (c * u) * X ^ n),
          (0 : TruncJet K d)) =
        (jetMap a (n + 2) (C u), jetMap b d (C u)) *
          ((jetMap a (n + 2) (C c), jetMap b d (C c)) *
            (Ideal.Quotient.mk (truncIdeal K (n + 2)) (X ^ n), (0 : TruncJet K d)))
      simp only [jetMap_apply, taylor_C]
      apply Prod.ext
      · change Ideal.Quotient.mk (truncIdeal K (n + 2)) (C (c * u) * X ^ n) =
          Ideal.Quotient.mk (truncIdeal K (n + 2)) (C u) *
            (Ideal.Quotient.mk (truncIdeal K (n + 2)) (C c) *
              Ideal.Quotient.mk (truncIdeal K (n + 2)) (X ^ n))
        rw [← map_mul, ← map_mul]
        apply congrArg (Ideal.Quotient.mk (truncIdeal K (n + 2)))
        rw [map_mul]
        ring
      · change 0 = _ * (_ * (0 : TruncJet K d))
        simp only [mul_zero]
    rwa [heq]
  · intro M
    obtain ⟨f, hf, hM⟩ := hderivative M
    refine ⟨ψ f, ⟨f, hf, rfl⟩, taylor a f, rfl, ?_, ?_⟩
    · rw [taylor_coeff_zero]
      exact (hO _).mpr (hvalue f hf)
    · rwa [taylor_coeff_one]

/-- Exact conductor for two distinct rational evaluation points in the polynomial
algebra. All conductor, lattice and derivative hypotheses concern actual elements. -/
theorem polynomial_conductor_eq_pair
    (O : Subring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (T : Subring (Polynomial K)) (a b : K) (hab : a ≠ b)
    (hscalar : ∀ u ∈ O, C u ∈ T)
    (hclear : ∀ f : Polynomial K, ∃ c : K, c ≠ 0 ∧ C c * f ∈ T)
    (hvalueA : ∀ f ∈ T, ‖f.eval a‖ ≤ 1)
    (hvalueB : ∀ f ∈ T, ‖f.eval b‖ ≤ 1)
    (hderivativeA : ∀ M : ℝ, ∃ f ∈ T, M < ‖f.derivative.eval a‖)
    (hderivativeB : ∀ M : ℝ, ∃ f ∈ T, M < ‖f.derivative.eval b‖)
    (k : ℕ) (hpower : ((X - C a) * (X - C b)) ^ k ∈ conductorIdeal T) :
    conductorIdeal T = Ideal.span {(X - C a) * (X - C b)} := by
  obtain ⟨e, _, d, _, he⟩ := ideal_above_pair_pow_eq (conductorIdeal T) a b k hpower
  have hker : RingHom.ker (twoJetMap a b e d).toRingHom = conductorIdeal T := by
    rw [ker_twoJetMap a b hab e d, ← he]
  have hker' : RingHom.ker (twoJetMap b a d e).toRingHom = conductorIdeal T := by
    rw [ker_twoJetMap b a hab.symm d e, mul_comm, ← he]
  have he_le := twoPoint_left_exponent_le_one O hO T a b hab e d hker
    hscalar hclear hvalueA hderivativeA
  have hd_le := twoPoint_left_exponent_le_one O hO T b a hab.symm d e hker'
    hscalar hclear hvalueB hderivativeB
  have hgen : (X - C a) ^ e * (X - C b) ^ d ∈ conductorIdeal T := by
    rw [he]
    exact Ideal.subset_span (by simp)
  have hzA : ((X - C a) ^ e * (X - C b) ^ d).eval a = 0 := by
    have h := conductor_le_ker_of_integral_values T (aeval a)
      (by intro f hf; simpa using hvalueA f hf) hgen
    exact h
  have hzB : ((X - C a) ^ e * (X - C b) ^ d).eval b = 0 := by
    have h := conductor_le_ker_of_integral_values T (aeval b)
      (by intro f hf; simpa using hvalueB f hf) hgen
    exact h
  have he_ne : e ≠ 0 := by
    intro h
    simp only [h, pow_zero, one_mul, eval_pow, eval_sub, eval_X, eval_C] at hzA
    exact pow_ne_zero d (sub_ne_zero.mpr hab) hzA
  have hd_ne : d ≠ 0 := by
    intro h
    simp only [h, pow_zero, mul_one, eval_pow, eval_sub, eval_X, eval_C] at hzB
    exact pow_ne_zero e (sub_ne_zero.mpr hab.symm) hzB
  have he1 : e = 1 := by omega
  have hd1 : d = 1 := by omega
  simpa only [he1, hd1, pow_one] using he

end UnconditionalCounterexample.RadicalConductor
