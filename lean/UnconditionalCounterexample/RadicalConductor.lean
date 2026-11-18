import UnconditionalCounterexample.LocalAlgebra.ConductorLifting
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# The algebraic radical conductor argument

The conductor is the largest ambient ideal contained in the subring. Modulo that
conductor, the image contains no nonzero ideal of the quotient. A truncated polynomial
component of exponent at least two would yield such an ideal from an integral
coefficient lattice and unbounded first derivatives.

The final PID and CRT assembly for the local conductor is separate. In
particular, these results do not assume that a topological closure equals the
actual subring and do not themselves construct the local polynomial model.
-/

namespace UnconditionalCounterexample.RadicalConductor

variable {R : Type*} [CommRing R]

/-- The largest ambient ideal contained in a subring. -/
def conductorIdeal (T : Subring R) : Ideal R where
  carrier := {a | ∀ b : R, a * b ∈ T}
  zero_mem' b := by simp only [zero_mul, zero_mem]
  add_mem' ha hb c := by simpa only [add_mul] using T.add_mem (ha c) (hb c)
  smul_mem' c a ha b := by
    simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * b)

theorem conductorIdeal_subset (T : Subring R) :
    ∀ x ∈ conductorIdeal T, x ∈ T := by
  intro x hx
  simpa only [mul_one] using hx 1

theorem le_conductorIdeal_iff (T : Subring R) (I : Ideal R) :
    I ≤ conductorIdeal T ↔ ∀ x ∈ I, x ∈ T := by
  constructor
  · intro h x hx
    exact conductorIdeal_subset T x (h hx)
  · intro h x hx b
    exact h (x * b) (I.mul_mem_right b hx)

/-- After quotienting by the full conductor, the image contains no nonzero ideal. -/
theorem quotient_image_ideal_eq_bot (T : Subring R)
    (J : Ideal (R ⧸ conductorIdeal T))
    (hJ : ∀ z ∈ J, z ∈ T.map (Ideal.Quotient.mk (conductorIdeal T))) :
    J = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hx : x ∈ conductorIdeal T := by
    intro y
    apply (LocalAlgebra.mem_iff_map_mem_of_kernel_subset T
      (Ideal.Quotient.mk (conductorIdeal T)) ?_ (x * y)).mpr
    · rw [map_mul]
      exact hJ _ (J.mul_mem_right _ hz)
    · intro a ha
      exact conductorIdeal_subset T a (Ideal.Quotient.eq_zero_iff_mem.mp ha)
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

open Polynomial

/-- The tail after the constant and linear coefficients is divisible by X squared. -/
theorem X_sq_dvd_remove_linear (f : Polynomial R) :
    X ^ 2 ∣ f - C (f.coeff 0) - C (f.coeff 1) * X := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro d hd
  interval_cases d <;> simp

/-- The cancellation used in the conductor calculation leaves exactly the first derivative in
the socle of the truncated polynomial ring. -/
theorem truncated_product_linear (f : Polynomial R) (u : R) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(X : Polynomial R) ^ (n + 2)})
      (f * C u * X ^ n - C (u * f.coeff 0) * X ^ n) =
    Ideal.Quotient.mk (Ideal.span {(X : Polynomial R) ^ (n + 2)})
      (C (u * f.coeff 1) * X ^ (n + 1)) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  obtain ⟨q, hq⟩ := X_sq_dvd_remove_linear f
  refine ⟨C u * q, ?_⟩
  calc
    f * C u * X ^ n - C (u * f.coeff 0) * X ^ n -
        C (u * f.coeff 1) * X ^ (n + 1) =
        (f - C (f.coeff 0) - C (f.coeff 1) * X) * C u * X ^ n := by
      rw [map_mul, map_mul, pow_succ]
      ring
    _ = X ^ (n + 2) * (C u * q) := by
      rw [hq, pow_add]
      ring

abbrev Jet (R : Type*) [CommRing R] (e : ℕ) :=
  Polynomial R ⧸ Ideal.span {(X : Polynomial R) ^ e}

noncomputable def jetMk (R : Type*) [CommRing R] (e : ℕ) : Polynomial R →+* Jet R e :=
  Ideal.Quotient.mk _

theorem truncated_product_constant (f : Polynomial R) (n : ℕ) :
    jetMk R (n + 2) (f * X ^ (n + 1)) =
      jetMk R (n + 2) (C (f.coeff 0) * X ^ (n + 1)) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := f)
  refine ⟨q, ?_⟩
  calc
    f * X ^ (n + 1) - C (f.coeff 0) * X ^ (n + 1) =
        (f - C (f.coeff 0)) * X ^ (n + 1) := by ring
    _ = X ^ (n + 2) * q := by
      rw [hq, pow_add, pow_add]
      ring

theorem socle_generator_ne_zero [Nontrivial R] (n : ℕ) :
    jetMk R (n + 2) (X ^ (n + 1)) ≠ 0 := by
  intro h
  have hdiv : (X : Polynomial R) ^ (n + 2) ∣ X ^ (n + 1) :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hcoeff := Polynomial.X_pow_dvd_iff.mp hdiv (n + 1) (by omega)
  simp at hcoeff

variable {n : ℕ}

theorem socle_ideal_subset (T : Subring (Jet R (n + 2)))
    (hmem : ∀ b : R, jetMk R (n + 2) (C b * X ^ (n + 1)) ∈ T) :
    ∀ z ∈ Ideal.span {jetMk R (n + 2) (X ^ (n + 1))}, z ∈ T := by
  intro z hz
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [ha, mul_comm]
  change jetMk R (n + 2) f * jetMk R (n + 2) (X ^ (n + 1)) ∈ T
  rw [← map_mul]
  rw [truncated_product_constant]
  exact hmem _

section Lattice

variable {K : Type*} [Field K]

/-- A coefficient lattice and arbitrarily scalable linear coefficients force
the complete socle into a subring of a truncated polynomial algebra. -/
theorem socle_mem_of_lattice (O : Subring K) (T : Subring (Jet K (n + 2))) (c : K)
    (hlattice : ∀ u ∈ O, jetMk K (n + 2) (C (c * u) * X ^ n) ∈ T)
    (hlinear : ∀ b : K, ∃ f : Polynomial K,
      jetMk K (n + 2) f ∈ T ∧ f.coeff 0 ∈ O ∧
        ∃ u ∈ O, (c * u) * f.coeff 1 = b) :
    ∀ b : K, jetMk K (n + 2) (C b * X ^ (n + 1)) ∈ T := by
  intro b
  obtain ⟨f, hf, hf0, u, hu, hub⟩ := hlinear b
  have hsub : jetMk K (n + 2)
      (f * C (c * u) * X ^ n - C ((c * u) * f.coeff 0) * X ^ n) ∈ T := by
    simpa only [map_sub, map_mul, mul_assoc] using
      T.sub_mem (T.mul_mem hf (hlattice u hu))
        (hlattice (u * f.coeff 0) (O.mul_mem hu hf0))
  rw [show jetMk K (n + 2) _ = _ from truncated_product_linear f (c * u) n,
    hub] at hsub
  exact hsub

theorem no_ideal_contradiction (O : Subring K) (T : Subring (Jet K (n + 2))) (c : K)
    (hno : ∀ J : Ideal (Jet K (n + 2)), (∀ z ∈ J, z ∈ T) → J = ⊥)
    (hlattice : ∀ u ∈ O, jetMk K (n + 2) (C (c * u) * X ^ n) ∈ T)
    (hlinear : ∀ b : K, ∃ f : Polynomial K,
      jetMk K (n + 2) f ∈ T ∧ f.coeff 0 ∈ O ∧
        ∃ u ∈ O, (c * u) * f.coeff 1 = b) : False := by
  have hmem := socle_mem_of_lattice O T c hlattice hlinear
  have hzero := hno (Ideal.span {jetMk K (n + 2) (X ^ (n + 1))})
    (socle_ideal_subset T hmem)
  have hg : jetMk K (n + 2) (X ^ (n + 1)) ∈
      Ideal.span {jetMk K (n + 2) (X ^ (n + 1))} := Ideal.subset_span (by simp)
  rw [hzero] at hg
  exact socle_generator_ne_zero n (Ideal.mem_bot.mp hg)

section SupportedComponent

variable {A : Type*} [CommRing A]

/-- The same socle argument in a supported component of a product algebra.
The nonunital embedding records the support idempotent explicitly. -/
theorem supported_socle_mem_of_lattice
    (project : A →+* Jet K (n + 2)) (embed : Jet K (n + 2) →ₙ+* A)
    (hact : ∀ z w, z * embed w = embed (project z * w))
    (O : Subring K) (T : Subring A) (c : K)
    (hlattice : ∀ u ∈ O,
      embed (jetMk K (n + 2) (C (c * u) * X ^ n)) ∈ T)
    (hlinear : ∀ b : K, ∃ z ∈ T, ∃ f : Polynomial K,
      project z = jetMk K (n + 2) f ∧ f.coeff 0 ∈ O ∧
        ∃ u ∈ O, (c * u) * f.coeff 1 = b) :
    ∀ b : K, embed (jetMk K (n + 2) (C b * X ^ (n + 1))) ∈ T := by
  intro b
  obtain ⟨z, hz, f, hf, hf0, u, hu, hub⟩ := hlinear b
  have hsub := T.sub_mem (T.mul_mem hz (hlattice u hu))
    (hlattice (u * f.coeff 0) (O.mul_mem hu hf0))
  have heq :
      z * embed (jetMk K (n + 2) (C (c * u) * X ^ n)) -
        embed (jetMk K (n + 2) (C (c * (u * f.coeff 0)) * X ^ n)) =
      embed (jetMk K (n + 2) (C b * X ^ (n + 1))) := by
    calc
      _ = embed (jetMk K (n + 2)
          (f * C (c * u) * X ^ n - C ((c * u) * f.coeff 0) * X ^ n)) := by
        rw [hact, hf]
        simp only [map_sub, map_mul, mul_assoc]
      _ = embed (jetMk K (n + 2) (C ((c * u) * f.coeff 1) * X ^ (n + 1))) :=
        congrArg embed (truncated_product_linear f (c * u) n)
      _ = _ := by rw [hub]
  rwa [heq] at hsub

theorem supported_socle_ideal_subset
    (project : A →+* Jet K (n + 2)) (embed : Jet K (n + 2) →ₙ+* A)
    (hact : ∀ z w, z * embed w = embed (project z * w))
    (T : Subring A)
    (hmem : ∀ b : K, embed (jetMk K (n + 2) (C b * X ^ (n + 1))) ∈ T) :
    ∀ z ∈ Ideal.span {embed (jetMk K (n + 2) (X ^ (n + 1)))}, z ∈ T := by
  intro z hz
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
  rw [ha, mul_comm, hact]
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (project a)
  change jetMk K (n + 2) f = project a at hf
  rw [← hf, ← map_mul, truncated_product_constant]
  exact hmem _

theorem supported_no_ideal_contradiction
    (project : A →+* Jet K (n + 2)) (embed : Jet K (n + 2) →ₙ+* A)
    (hinj : Function.Injective embed)
    (hact : ∀ z w, z * embed w = embed (project z * w))
    (O : Subring K) (T : Subring A) (c : K)
    (hno : ∀ J : Ideal A, (∀ z ∈ J, z ∈ T) → J = ⊥)
    (hlattice : ∀ u ∈ O,
      embed (jetMk K (n + 2) (C (c * u) * X ^ n)) ∈ T)
    (hlinear : ∀ b : K, ∃ z ∈ T, ∃ f : Polynomial K,
      project z = jetMk K (n + 2) f ∧ f.coeff 0 ∈ O ∧
        ∃ u ∈ O, (c * u) * f.coeff 1 = b) : False := by
  have hmem := supported_socle_mem_of_lattice project embed hact O T c hlattice hlinear
  have hzero := hno
    (Ideal.span {embed (jetMk K (n + 2) (X ^ (n + 1)))})
    (supported_socle_ideal_subset project embed hact T hmem)
  have hg : embed (jetMk K (n + 2) (X ^ (n + 1))) ∈
      Ideal.span {embed (jetMk K (n + 2) (X ^ (n + 1)))} :=
    Ideal.subset_span (by simp)
  rw [hzero] at hg
  apply socle_generator_ne_zero (R := K) n
  apply hinj
  simpa only [map_zero] using Ideal.mem_bot.mp hg

end SupportedComponent

end Lattice

section Normed

variable {K : Type*} [NormedField K]

/-- A sufficiently large coefficient can be scaled to any target using an
arbitrarily prescribed nonzero multiple of the valuation integer ring. -/
theorem integral_scale_of_norm_gt (O : Subring K)
    (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) (c b d : K) (hc : c ≠ 0)
    (hd : ‖b‖ / ‖c‖ < ‖d‖) :
    ∃ u ∈ O, (c * u) * d = b := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hdpos : 0 < ‖d‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg _) (norm_nonneg _)) hd
  have hdne : d ≠ 0 := norm_pos_iff.mp hdpos
  refine ⟨b / (c * d), ?_, ?_⟩
  · apply (hO _).mpr
    rw [norm_div, norm_mul]
    apply (div_le_one (mul_pos hcpos hdpos)).mpr
    have hbound := (div_lt_iff₀ hcpos).mp hd
    simpa only [mul_comm] using hbound.le
  · field_simp

/-- The algebraic contradiction of the conductor calculation from an integral coefficient
lattice and genuinely unbounded first derivatives in one supported component. -/
theorem supported_no_ideal_of_unbounded
    {A : Type*} [CommRing A]
    (project : A →+* Jet K (n + 2)) (embed : Jet K (n + 2) →ₙ+* A)
    (hinj : Function.Injective embed)
    (hact : ∀ z w, z * embed w = embed (project z * w))
    (O : Subring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (T : Subring A) (c : K) (hc : c ≠ 0)
    (hno : ∀ J : Ideal A, (∀ z ∈ J, z ∈ T) → J = ⊥)
    (hlattice : ∀ u ∈ O,
      embed (jetMk K (n + 2) (C (c * u) * X ^ n)) ∈ T)
    (hderivative : ∀ M : ℝ, ∃ z ∈ T, ∃ f : Polynomial K,
      project z = jetMk K (n + 2) f ∧ f.coeff 0 ∈ O ∧ M < ‖f.coeff 1‖) :
    False := by
  apply supported_no_ideal_contradiction project embed hinj hact O T c hno hlattice
  intro b
  obtain ⟨z, hz, f, hf, hf0, hlarge⟩ := hderivative (‖b‖ / ‖c‖)
  obtain ⟨u, hu, hub⟩ := integral_scale_of_norm_gt O hO c b (f.coeff 1) hc hlarge
  exact ⟨z, hz, f, hf, hf0, u, hu, hub⟩

end Normed

section IntegralValues

variable {K A : Type*} [NontriviallyNormedField K] [CommRing A] [Algebra K A]

/-- Bounded values force every conductor element to vanish under evaluation. -/
theorem conductor_le_ker_of_integral_values (T : Subring A) (v : A →ₐ[K] K)
    (hbound : ∀ z ∈ T, ‖v z‖ ≤ 1) :
    conductorIdeal T ≤ RingHom.ker v.toRingHom := by
  intro x hx
  change v x = 0
  by_contra hne
  obtain ⟨b, hb⟩ := NormedField.exists_one_lt_norm K
  have hmem := hx (algebraMap K A (b / v x))
  have hval : v (x * algebraMap K A (b / v x)) = b := by
    rw [map_mul, v.commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
  have h := hbound _ hmem
  rw [hval] at h
  exact (not_lt_of_ge h) hb


end IntegralValues

/-- Ideals above a power of X in the polynomial PID are powers of X. -/
theorem ideal_above_X_pow_eq {K : Type*} [Field K] (I : Ideal K[X]) (k : ℕ)
    (h : (X : K[X]) ^ k ∈ I) :
    ∃ e ≤ k, I = Ideal.span {(X : K[X]) ^ e} := by
  have hdiv := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp h
  obtain ⟨e, he, ha⟩ := (dvd_prime_pow (Polynomial.prime_X (R := K)) k).mp hdiv
  refine ⟨e, he, ?_⟩
  rw [← Ideal.span_singleton_generator I]
  exact Ideal.span_singleton_eq_span_singleton.mpr ha

section SinglePoint

variable {K : Type*} [NontriviallyNormedField K]

/-- The one-point polynomial case of the conductor calculation, with an explicit denominator
clearing hypothesis and integral coefficient scalars. -/
theorem polynomial_conductor_eq_X (O : Subring K)
    (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) (T : Subring (Polynomial K))
    (hscalar : ∀ u ∈ O, C u ∈ T)
    (hclear : ∀ f : Polynomial K, ∃ c : K, c ≠ 0 ∧ C c * f ∈ T)
    (hvalue : ∀ f ∈ T, ‖f.coeff 0‖ ≤ 1)
    (hderivative : ∀ M : ℝ, ∃ f ∈ T, M < ‖f.coeff 1‖)
    (k : ℕ) (hpower : (X : Polynomial K) ^ k ∈ conductorIdeal T) :
    conductorIdeal T = Ideal.span {(X : Polynomial K)} := by
  obtain ⟨e, _, he⟩ := ideal_above_X_pow_eq (conductorIdeal T) k hpower
  have hepos : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    obtain ⟨b, hb⟩ := NormedField.exists_one_lt_norm K
    have hbT : C b ∈ T := conductorIdeal_subset T (C b) (by simp [he, he0])
    have hbound := hvalue (C b) hbT
    simp only [coeff_C_zero] at hbound
    exact (not_lt_of_ge hbound) hb
  have hele : e ≤ 1 := by
    by_contra h
    have he2 : 2 ≤ e := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le he2
    have heN : e = n + 2 := by omega
    clear hn
    subst e
    let S : Subring (Jet K (n + 2)) := T.map (jetMk K (n + 2))
    have hno : ∀ J : Ideal (Jet K (n + 2)), (∀ z ∈ J, z ∈ S) → J = ⊥ := by
      have hno0 := quotient_image_ideal_eq_bot T
      rw [he] at hno0
      exact hno0
    obtain ⟨c, hc, hcT⟩ := hclear (X ^ n)
    have hlattice : ∀ u ∈ O, jetMk K (n + 2) (C (c * u) * X ^ n) ∈ S := by
      intro u hu
      apply Subring.mem_map.mpr
      refine ⟨C (c * u) * X ^ n, ?_, rfl⟩
      simpa only [map_mul, mul_assoc, mul_left_comm] using T.mul_mem (hscalar u hu) hcT
    apply no_ideal_contradiction O S c hno hlattice
    intro b
    obtain ⟨f, hf, hlarge⟩ := hderivative (‖b‖ / ‖c‖)
    obtain ⟨u, hu, hub⟩ := integral_scale_of_norm_gt O hO c b (f.coeff 1) hc hlarge
    exact ⟨f, ⟨f, hf, rfl⟩, (hO _).mpr (hvalue f hf), u, hu, hub⟩
  have he1 : e = 1 := by omega
  simpa only [he1, pow_one] using he


end SinglePoint

end UnconditionalCounterexample.RadicalConductor
