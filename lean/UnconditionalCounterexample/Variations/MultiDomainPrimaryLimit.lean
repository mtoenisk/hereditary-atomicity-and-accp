import UnconditionalCounterexample.Variations.MultiDomainPrimeValuation
import UnconditionalCounterexample.Variations.MultiDomainPlaces
import UnconditionalCounterexample.Variations.PrimaryTuples
import Mathlib.Algebra.MvPolynomial.Division

/-!
# The limiting order along the primary evaluations

At a primary birthday, finitely many integer polynomials whose restrictions
to the first coordinate hyperplane are nonzero are required to evaluate to
units. The increasing birthday lists imply eventual agreement with the
horizontal valuation at that coordinate on every rational function.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open MvPolynomial Filter WithZero IndependentTuples

abbrev IntPolys (r : ℕ) := MvPolynomial (Fin r) ℤ

private def enumScreen (r : ℕ) : ℕ → IntPolys (r+1) := (exists_surjective_nat _).choose

/-- Finite growing part of the primary screening schedule. -/
def primaryTests (r j : ℕ) : Finset (IntPolys (r+1)) := by
  classical exact ((Finset.range (j+1)).image (enumScreen r)).filter (fun f ↦ restrictToCentre r f ≠ 0)

theorem primaryTests_nonvanishing {r j : ℕ} {F : IntPolys (r+1)} (h : F ∈ primaryTests r j) :
    restrictToCentre r F ≠ 0 := (Finset.mem_filter.mp h).2

theorem eventually_primaryTests {r : ℕ} (F : IntPolys (r+1)) (h : restrictToCentre r F ≠ 0) :
    ∀ᶠ j in atTop, F ∈ primaryTests r j := by
  classical
  obtain ⟨k, hk⟩ := (exists_surjective_nat (IntPolys (r+1))).choose_spec F
  exact eventually_atTop.mpr ⟨k, fun j hj ↦ Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hk⟩, h⟩⟩

abbrev rationalize {r : ℕ} : IntPolys r →+* Polys r := MvPolynomial.map (Int.castRingHom ℚ)

theorem clear_polynomial {r : ℕ} (f : Polys r) :
    ∃ n : ℕ, 0 < n ∧ ∃ F : IntPolys r, rationalize F = C (n : ℚ) * f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, a.den_pos, C a.num, ?_⟩
    rw [rationalize, map_C, ← map_mul, Rat.den_mul_eq_num]
    rfl
  | add f g hf hg =>
    obtain ⟨n,hn,F,hF⟩ := hf
    obtain ⟨m,hm,G,hG⟩ := hg
    refine ⟨n*m,Nat.mul_pos hn hm, C (m : ℤ)*F + C (n : ℤ)*G, ?_⟩
    simp only [map_add, map_mul, hF, hG, rationalize, map_C, Int.coe_castRingHom,
      Int.cast_natCast, Nat.cast_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨n,hn,F,hF⟩ := hf
    exact ⟨n, hn, F * X i, by simp [map_mul, hF, rationalize, mul_assoc]⟩

theorem restrict_ne_of_not_dvd {r : ℕ} {F : IntPolys (r+1)} (h : ¬ X 0 ∣ F) :
    restrictToCentre r F ≠ 0 := by
  intro hz
  apply h
  let e := MvPolynomial.finSuccEquiv ℤ r
  have he : Polynomial.constantCoeff.comp e.toRingHom = restrictToCentre r := by
    ext i
    · simp [e, restrictToCentre]
    · refine Fin.cases ?_ (fun j ↦ ?_) i <;>
        simp [e, restrictToCentre, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  have hd : Polynomial.X ∣ e F := Polynomial.X_dvd_iff.mpr (by
    exact (DFunLike.congr_fun he F).trans hz)
  simpa [e, ← MvPolynomial.finSuccEquiv_X_zero] using (map_dvd e.symm hd)

variable {r : ℕ}

abbrev tVal : Valuation (FunctionField (r+1)) ℤᵐ⁰ :=
  PrimeOrders.valuation (MvPolynomial.X_prime (R := ℚ) (i := (0 : Fin (r+1))))

/-- Two integral tests suffice to screen one rational polynomial and its
coefficient denominator. -/
theorem screening_for (f : Polys (r+1)) (hf : ¬ X 0 ∣ f) :
    ∃ s : Finset (IntPolys (r+1)), (∀ F ∈ s, restrictToCentre r F ≠ 0) ∧
      ∀ v : Valuation (FunctionField (r+1)) ℤᵐ⁰,
        (∀ F ∈ s, v (algebraMap _ _ (rationalize F)) = 1) → v (algebraMap _ _ f) = 1 := by
  classical
  obtain ⟨n,hn,F,hF⟩ := clear_polynomial f
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hunit : IsUnit (C (n : ℚ) : Polys (r+1)) := (isUnit_iff_ne_zero.mpr hnq).map C
  have hX : Prime (X 0 : Polys (r+1)) := MvPolynomial.X_prime
  have hFF : ¬ X 0 ∣ F := by
    intro h
    have hd := map_dvd rationalize h
    rw [hF] at hd
    exact hf ((hX.dvd_mul.mp (by simpa using hd)).resolve_left (fun ht ↦ hX.not_isUnit (isUnit_of_dvd_unit ht hunit)))
  refine ⟨{F, C (n : ℤ)}, ?_, fun v hv ↦ ?_⟩
  · intro G hG
    simp only [Finset.mem_insert, Finset.mem_singleton] at hG
    rcases hG with rfl | rfl
    · exact restrict_ne_of_not_dvd hFF
    · simp [restrictToCentre, hn.ne']
  · have hg := hv F (by simp)
    have hn' := hv (C (n : ℤ)) (by simp)
    simp only [rationalize, map_C, Int.coe_castRingHom, Int.cast_natCast] at hn'
    rw [hF, map_mul, map_mul, hn', one_mul] at hg
    exact hg

/-- Agreement on the screened integral tests gives unit values for every
rational polynomial not divisible by the first coordinate. -/
theorem eventually_primary_unit (v : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰)
    (hs : ∀ j F, F ∈ primaryTests r j → v j (algebraMap _ _ (rationalize F)) = 1)
    (f : Polys (r+1)) (hf : ¬ X 0 ∣ f) :
    ∀ᶠ j in atTop, v j (algebraMap _ _ f) = 1 := by
  obtain ⟨s, hregular, hunit⟩ := screening_for f hf
  have hall : ∀ᶠ j in atTop, ∀ F ∈ s, F ∈ primaryTests r j :=
    (eventually_all_finset s).mpr fun F hF ↦ eventually_primaryTests F (hregular F hF)
  filter_upwards [hall] with j hj
  exact hunit (v j) fun F hF ↦ hs j F (hj F hF)

/-- Specialization at every sufficiently late primary gives the intrinsic
order at the prime polynomial X₁, on every element of the fraction field. -/
theorem eventually_primary_horizontal (v : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰)
    (hs : ∀ j F, F ∈ primaryTests r j → v j (algebraMap _ _ (rationalize F)) = 1)
    (ht : ∀ᶠ j in atTop, v j (coordinate 0) = exp (-1))
    (z : FunctionField (r+1)) : ∀ᶠ j in atTop, v j z = tVal z := by
  have hp : Prime (X 0 : Polys (r+1)) := MvPolynomial.X_prime
  have hpoly (f : Polys (r+1)) :
      ∀ᶠ j in atTop, v j (algebraMap _ _ f) = tVal (r := r) (algebraMap _ _ f) := by
    by_cases hzero : f = 0
    · simp [hzero]
    obtain ⟨g,hg,hgd⟩ := (FiniteMultiplicity.of_prime_left hp hzero).exists_eq_pow_mul_and_not_dvd
    filter_upwards [ht, eventually_primary_unit v hs g hgd] with j hj hunit
    change v j (algebraMap _ _ (X 0 : Polys (r+1))) = exp (-1) at hj
    conv_lhs => rw [hg]
    rw [map_mul, map_mul, map_pow, map_pow, hj, hunit, mul_one, PrimeOrders.valuation_of_polynomial hp hzero]
    simp [← exp_nsmul]
  obtain ⟨x,y,_,h⟩ := IsFractionRing.div_surjective (Polys (r+1)) z
  filter_upwards [hpoly x, hpoly y] with j hx hy
  rw [← h, map_div₀, map_div₀, hx, hy]

end UnconditionalCounterexample.Variations.MultiDomain
