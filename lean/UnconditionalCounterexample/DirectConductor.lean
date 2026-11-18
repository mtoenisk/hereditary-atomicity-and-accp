import UnconditionalCounterexample.LocalizedPolynomialJets
import UnconditionalCounterexample.LocalAlgebra.ConductorLocalization

/-!
# Direct cancellation of repeated conductor factors

Taylor cancellation gives the conductor in Lemma 6.2. The actual first-jet kernel in a polynomial localization is
exactly the square of its surviving linear factor. Multiplying the literal
Taylor remainder by a scalar multiple of q proves every scalar multiple of
q*(t-a) lies in T whenever q*(t-a)^2 generates an ideal contained in T and first
derivatives are unbounded. Scalar denominator clearing then puts q*(t-a) in
the actual ambient conductor. No CRT or closed-submodule argument is used.
-/

namespace UnconditionalCounterexample.DirectConductor

open Polynomial LocalizedPolynomialJets

variable {K : Type*} [Field K]

theorem square_linear_dvd_iff (a : K) (f : K[X]) :
    (X - C a) ^ 2 ∣ f ↔ f.eval a = 0 ∧ f.derivative.eval a = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    simp [derivative_mul, derivative_pow]
  · rintro ⟨hf, hdf⟩
    obtain ⟨g, rfl⟩ := (dvd_iff_isRoot).mpr hf
    have hg : g.eval a = 0 := by simpa [derivative_mul] using hdf
    obtain ⟨h, rfl⟩ := (dvd_iff_isRoot).mpr hg
    exact ⟨h, by ring⟩

theorem ker_firstJet (a : K) :
    RingHom.ker (firstJet a).toRingHom = Ideal.span {(X - C a) ^ 2} := by
  ext f
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Ideal.mem_span_singleton, square_linear_dvd_iff]
  change (⟨f.eval a, f.derivative.eval a⟩ : DualNumber K) = 0 ↔ _
  constructor
  · intro h
    exact ⟨congrArg TrivSqZeroExt.fst h, congrArg TrivSqZeroExt.snd h⟩
  · rintro ⟨h₁, h₂⟩
    exact TrivSqZeroExt.ext h₁ h₂

variable (M : Submonoid K[X]) (A : Type*) [CommRing A] [Algebra K[X] A]
  [IsLocalization M A] (a : K) (ha : ∀ m : M, (m : K[X]).eval a ≠ 0)

theorem ker_localizedFirstJet :
    RingHom.ker (localizedFirstJet M A a ha) =
      Ideal.span {algebraMap K[X] A (X - C a) ^ 2} := by
  have hcomap : (RingHom.ker (localizedFirstJet M A a ha)).comap
      (algebraMap K[X] A) = RingHom.ker (firstJet a).toRingHom := by
    ext f
    simp only [Ideal.mem_comap, RingHom.mem_ker, localizedFirstJet_algebraMap]
    rfl
  rw [← IsLocalization.map_under M A (RingHom.ker (localizedFirstJet M A a ha)),
    Ideal.under, hcomap, ker_firstJet, Ideal.map_span, Set.image_singleton, map_pow]

/-- Literal first-order Taylor expansion in the actual localization. -/
theorem localized_taylor_remainder_mem_square (z : A) :
    z - algebraMap K[X] A (C (localizedFirstJet M A a ha z).fst) -
        algebraMap K[X] A (C (localizedFirstJet M A a ha z).snd) *
          algebraMap K[X] A (X - C a) ∈
      Ideal.span {algebraMap K[X] A (X - C a) ^ 2} := by
  rw [← ker_localizedFirstJet M A a ha]
  change localizedFirstJet M A a ha _ = 0
  rw [map_sub, map_sub, map_mul, localizedFirstJet_algebraMap,
    localizedFirstJet_algebraMap, localizedFirstJet_algebraMap]
  apply TrivSqZeroExt.ext
  · simp only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul, firstJet_fst,
      eval_C, eval_sub, eval_X, sub_self, mul_zero, TrivSqZeroExt.fst_zero]
  · simp only [TrivSqZeroExt.snd_sub, DualNumber.snd_mul, firstJet_snd, firstJet_fst,
      derivative_C, derivative_sub, derivative_X, eval_zero, eval_one, eval_sub,
      eval_X, eval_C, sub_self, mul_zero, add_zero, sub_zero, mul_one,
      TrivSqZeroExt.snd_zero]

end UnconditionalCounterexample.DirectConductor

namespace UnconditionalCounterexample.DirectConductor


open RadicalConductor

variable {K A : Type*} [NormedField K] [CommRing A] [Algebra K A]

/-- Multiplication by a Taylor remainder cancels one repeated factor using
actual subring membership and arbitrarily large first derivatives. -/
theorem scalar_multiple_mem_of_taylor_unbounded
    (O : Subring K) (hO : ∀ u : K, u ∈ O ↔ ‖u‖ ≤ 1)
    (T : Subring A) (hscalar : ∀ u ∈ O, algebraMap K A u ∈ T)
    (x q : A) (value derivative : A → K)
    (c : K) (hc : c ≠ 0) (hcq : algebraMap K A c * q ∈ T)
    (hI : ∀ y ∈ Ideal.span {q * x ^ 2}, y ∈ T)
    (hvalue : ∀ z ∈ T, value z ∈ O)
    (htaylor : ∀ z ∈ T,
      z - algebraMap K A (value z) - algebraMap K A (derivative z) * x ∈
        Ideal.span {x ^ 2})
    (hderivative : ∀ M : ℝ, ∃ z ∈ T, M < ‖derivative z‖) :
    ∀ b : K, algebraMap K A b * q * x ∈ T := by
  intro b
  obtain ⟨z, hz, hlarge⟩ := hderivative (‖b‖ / ‖c‖)
  obtain ⟨u, hu, hub⟩ := integral_scale_of_norm_gt O hO c b (derivative z) hc hlarge
  have hcuq : algebraMap K A (c * u) * q ∈ T := by
    simpa only [map_mul, mul_left_comm, mul_assoc] using
      T.mul_mem (hscalar u hu) hcq
  have herror : algebraMap K A (c * u) * q *
      (z - algebraMap K A (value z) - algebraMap K A (derivative z) * x) ∈ T := by
    apply hI
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp (htaylor z hz)
    apply Ideal.mem_span_singleton.mpr
    refine ⟨algebraMap K A (c * u) * v, ?_⟩
    rw [hv]
    ring
  have hmem := T.sub_mem
    (T.sub_mem (T.mul_mem hcuq hz) (T.mul_mem (hscalar (value z) (hvalue z hz)) hcuq))
    herror
  have heq :
      (algebraMap K A (c * u) * q * z -
        algebraMap K A (value z) * (algebraMap K A (c * u) * q)) -
      algebraMap K A (c * u) * q *
        (z - algebraMap K A (value z) - algebraMap K A (derivative z) * x) =
      algebraMap K A b * q * x := by
    rw [← hub]
    simp only [map_mul]
    ring
  rwa [heq] at hmem

/-- Scalar clearing converts all scalar multiples of an element in T into
membership in the actual ambient conductor ideal. -/
theorem mem_conductor_of_scalar_multiples
    (T : Subring A) (g : A)
    (hmem : ∀ b : K, algebraMap K A b * g ∈ T)
    (hclear : ∀ y : A, ∃ c : K, c ≠ 0 ∧ algebraMap K A c * y ∈ T) :
    g ∈ conductorIdeal T := by
  intro y
  obtain ⟨c, hc, hcy⟩ := hclear y
  have hprod := T.mul_mem (hmem c⁻¹) hcy
  have heq : (algebraMap K A c⁻¹ * g) * (algebraMap K A c * y) = g * y := by
    calc
      _ = algebraMap K A (c⁻¹ * c) * (g * y) := by rw [map_mul]; ring
      _ = g * y := by rw [inv_mul_cancel₀ hc, map_one, one_mul]
  rwa [heq] at hprod

/-- Direct cancellation of one repeated factor, before any PID classification. -/
theorem cancel_square_into_conductor
    (O : Subring K) (hO : ∀ u : K, u ∈ O ↔ ‖u‖ ≤ 1)
    (T : Subring A) (hscalar : ∀ u ∈ O, algebraMap K A u ∈ T)
    (x q : A) (value derivative : A → K)
    (hclear : ∀ y : A, ∃ c : K, c ≠ 0 ∧ algebraMap K A c * y ∈ T)
    (hI : ∀ y ∈ Ideal.span {q * x ^ 2}, y ∈ T)
    (hvalue : ∀ z ∈ T, value z ∈ O)
    (htaylor : ∀ z ∈ T,
      z - algebraMap K A (value z) - algebraMap K A (derivative z) * x ∈
        Ideal.span {x ^ 2})
    (hderivative : ∀ M : ℝ, ∃ z ∈ T, M < ‖derivative z‖) :
    q * x ∈ conductorIdeal T := by
  obtain ⟨c, hc, hcq⟩ := hclear q
  apply mem_conductor_of_scalar_multiples T (q * x) _ hclear
  intro b
  simpa only [mul_assoc] using
    scalar_multiple_mem_of_taylor_unbounded O hO T hscalar x q value derivative
      c hc hcq hI hvalue htaylor hderivative b


end UnconditionalCounterexample.DirectConductor

namespace UnconditionalCounterexample.DirectConductor

open Polynomial LocalizedPolynomialJets RadicalConductor

/-- The manuscript's repeated-factor cancellation in the actual localization,
using its canonical value and derivative maps. -/
theorem cancel_localized_square_into_conductor
    {K A : Type*} [NormedField K] [CommRing A]
    [Algebra K A] [Algebra K[X] A] [IsScalarTower K K[X] A]
    (M : Submonoid K[X]) [IsLocalization M A]
    (a : K) (ha : ∀ m : M, (m : K[X]).eval a ≠ 0)
    (O : Subring K) (hO : ∀ u : K, u ∈ O ↔ ‖u‖ ≤ 1)
    (T : Subring A) (hscalar : ∀ u ∈ O, algebraMap K A u ∈ T)
    (q : A)
    (hclear : ∀ y : A, ∃ c : K, c ≠ 0 ∧ algebraMap K A c * y ∈ T)
    (hI : ∀ y ∈ Ideal.span {q * algebraMap K[X] A (X - C a) ^ 2}, y ∈ T)
    (hvalue : ∀ z ∈ T, ‖(localizedFirstJet M A a ha z).fst‖ ≤ 1)
    (hderivative : ∀ N : ℝ, ∃ z ∈ T, N < ‖(localizedFirstJet M A a ha z).snd‖) :
    q * algebraMap K[X] A (X - C a) ∈ conductorIdeal T := by
  apply cancel_square_into_conductor O hO T hscalar
    (algebraMap K[X] A (X - C a)) q
    (fun z => (localizedFirstJet M A a ha z).fst)
    (fun z => (localizedFirstJet M A a ha z).snd) hclear hI
    (fun z hz => (hO _).mpr (hvalue z hz)) _ hderivative
  intro z _
  have hc : ∀ c : K, algebraMap K[X] A (C c) = algebraMap K A c := by
    intro c
    exact (IsScalarTower.algebraMap_apply K K[X] A c).symm
  simpa only [hc] using localized_taylor_remainder_mem_square M A a ha z

/-- A repeated nonunit factor would make its strictly smaller power divide one
power less. This is the contradiction used after direct Taylor cancellation. -/
theorem not_square_generator_of_cancelled_mem
    {A : Type*} [CommRing A] [IsDomain A]
    (I : Ideal A) (q x : A) (hq : q ≠ 0) (hx : x ≠ 0) (hxu : ¬ IsUnit x)
    (hcancel : q * x ∈ I) :
    I ≠ Ideal.span {q * x ^ 2} := by
  intro heq
  rw [heq, Ideal.mem_span_singleton] at hcancel
  have hd : x ^ 2 ∣ x ^ 1 := by
    simpa only [pow_one] using (mul_dvd_mul_iff_left hq).mp hcancel
  have : 2 ≤ 1 := (pow_dvd_pow_iff hx hxu).mp hd
  omega

end UnconditionalCounterexample.DirectConductor
