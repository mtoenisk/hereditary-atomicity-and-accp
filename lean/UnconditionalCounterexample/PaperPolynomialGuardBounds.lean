import UnconditionalCounterexample.PaperConstruction
import UnconditionalCounterexample.RationalSigns

/-!
# Rational scalar multiples among divisors

For a fixed nonzero rational function, a single positive integer clears its
inverse at every guard. This bounds the denominator of each scalar multiple
integral at the guards. Applying the same argument to the complementary
factor bounds the numerator as well.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperConstruction

open WithZero GuardSupport IntersectionDomain

private abbrev guardValue (p : PrimeIndex) := PairedDomain.vertical places (.inr p)

private theorem integral_at_guards (x : domain) (p : PrimeIndex) : guardValue p (x : RatFunc ℚ) ≤ 1 :=
  ((mem_intersection _ _ _).mp x.property).2 (.inr p)

/-- A fixed denominator suffices for all rational scalar multiples of a given
nonzero rational function that are integral at every guard. -/
theorem bounded_denominator_at_guards (h : RatFunc ℚ) (hh : h ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ q : ℚ,
      (∀ p : PrimeIndex, PairedDomain.vertical places (.inr p) ((q : RatFunc ℚ) * h) ≤ 1) →
      ∃ a : ℤ, (a : ℚ) = n * q := by
  obtain ⟨n, hn, hclear⟩ := exists_nat_mul_integral_of_finite guardValue h⁻¹
    ((guardSupport _ (inv_ne_zero hh)).subset (fun _ h ↦ ne_of_gt h))
    (fun p ↦ exists_nat_mul_integral (guardValue p) p.val p.property.pos (EvaluationDVR.valuation_prime _ _) _)
  refine ⟨n, hn, fun q hq ↦ RationalSigns.integer_of_padic_le_one _ fun p ↦ ?_⟩
  have he : (((n : ℚ) * q : ℚ) : RatFunc ℚ) = (n * h⁻¹) * ((q : RatFunc ℚ) * h) := by
    push_cast
    field_simp
  have hg : guardValue p (((n : ℚ) * q : ℚ) : RatFunc ℚ) ≤ 1 := by
    rw [he, map_mul]
    simpa only [one_mul] using mul_le_mul' (hclear p) (hq p)
  change Padic.mulValuation (guardEvaluation places.guard places.guard_trans p
    (((n : ℚ) * q : ℚ) : RatFunc ℚ)) ≤ 1 at hg
  rw [map_ratCast] at hg
  exact (congrArg (fun v : Valuation ℚ ℤᵐ⁰ ↦ v (n * q))
    (Padic.comap_mulValuation_eq_padicValuation (p := p.val))) ▸ hg

/-- Only finitely many rational multiples of a fixed rational function occur
as actual divisors of a given nonzero element of the paper domain. -/
theorem finite_rational_scalar_divisors (f h : RatFunc ℚ) (hf : f ≠ 0) (hh : h ≠ 0) :
    {q : ℚ | ∃ x y : domain, (x : RatFunc ℚ) = (q : RatFunc ℚ) * h ∧
      (x : RatFunc ℚ) * (y : RatFunc ℚ) = f}.Finite := by
  obtain ⟨n,hn,hnq⟩ := bounded_denominator_at_guards h hh
  obtain ⟨m,hm,hmq⟩ := bounded_denominator_at_guards (f/h) (div_ne_zero hf hh)
  let b : ℤ := (n : ℤ) * m
  have hb : 0 < b := by
    dsimp [b]
    positivity
  apply ((Set.finite_Icc (-b) b).image (fun a : ℤ ↦ (a : ℚ) / n)).subset
  rintro q ⟨x,y,hx,hxy⟩
  have hq : q ≠ 0 := by
    rintro rfl
    simp [hx] at hxy
    exact hf hxy.symm
  have hy : (q⁻¹ : ℚ) * (f / h) = (y : RatFunc ℚ) := by
    rw [← hxy, hx, Rat.cast_inv]
    field_simp
  obtain ⟨a, ha⟩ := hnq q (fun p ↦ hx ▸ integral_at_guards x p)
  obtain ⟨z, hz⟩ := hmq q⁻¹ (fun p ↦ hy ▸ integral_at_guards y p)
  have haz : a * z = b := by
    have H : (a : ℚ) * z = (n : ℚ) * m := by
      rw [ha, hz]
      field_simp
    exact_mod_cast H
  have hd : a ∣ b := ⟨z, haz.symm⟩
  have upper := Int.le_of_dvd hb hd
  have lower := Int.le_of_dvd hb (Int.neg_dvd.mpr hd)
  refine ⟨a, ⟨by omega, upper⟩, ?_⟩
  exact (div_eq_iff (by exact_mod_cast hn.ne')).mpr (ha.trans (mul_comm ..))

end UnconditionalCounterexample.PaperConstruction
