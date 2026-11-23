import UnconditionalCounterexample.Variations.CalibrationPrimes
import UnconditionalCounterexample.GuardSupport
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.Padics.Hensel

/-!
# Fresh rational primes with a number-field embedding

A simple root of a cleared primitive-element polynomial lifts to a root in
the p-adic integers. For a prescribed finite list, bound the denominators of
representations of the elements and their inverses in that generator. The
resulting embedding sends the whole list to p-adic units.
-/

namespace UnconditionalCounterexample.PrivateGuardsNumberField

open Polynomial GuardSupport

private theorem exists_padic_root (f : ℚ[X]) (hirr : Irreducible f) (cutoff : ℕ) :
    ∃ p : PrimeIndex, cutoff < p.val ∧ ∃ z : ℤ_[p.val], aeval (z : ℚ_[p.val]) f = 0 := by
  obtain ⟨b,g,hb,_,heq⟩ := exists_integer_multiple f hirr.ne_zero
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hu : IsUnit (C (b : ℚ) : ℚ[X]) := (isUnit_iff_ne_zero.mpr hbq).map C
  have hd : g.natDegree ≠ 0 := by
    have hd' := congrArg natDegree heq
    rw [natDegree_map_eq_of_injective (f := algebraMap ℤ ℚ) Int.cast_injective, natDegree_C_mul hbq] at hd'
    exact hd' ▸ hirr.natDegree_pos.ne'
  have hc : IsCoprime (g.map (Int.castRingHom ℚ)) (g.derivative.map (Int.castRingHom ℚ)) := by
    change IsCoprime (g.map (algebraMap ℤ ℚ)) (g.derivative.map (algebraMap ℤ ℚ))
    rw [← derivative_map, heq, derivative_C_mul, isCoprime_mul_units_left hu hu]
    exact hirr.separable
  obtain ⟨p, a, hp, hcut, hroot, hder⟩ := Calibration.exists_prime_root_avoiding g g.derivative hd hc cutoff
  let : Fact p.Prime := ⟨hp⟩
  have hev (h : ℤ[X]) : aeval (a : ℤ_[p]) h = ((h.eval a : ℤ) : ℤ_[p]) :=
    eval₂_at_apply (Int.castRingHom ℤ_[p]) a
  have hnorm : ‖aeval (a : ℤ_[p]) g.derivative‖ = 1 := by
    rw [hev]; exact le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt (hder ∘ PadicInt.norm_intCast_lt_one_iff.mp))
  obtain ⟨z,hz,_,_,_⟩ := hensels_lemma (F := g) (a := (a : ℤ_[p])) (by
    rw [hnorm, one_pow, hev]; exact PadicInt.norm_intCast_lt_one_iff.mpr hroot)
  refine ⟨⟨p,hp⟩,hcut,z,?_⟩
  have hz' : aeval (z : ℚ_[p]) g = 0 := by
    have he : aeval (z : ℚ_[p]) g = ((aeval z g : ℤ_[p]) : ℚ_[p]) := aeval_algebraMap_apply ℚ_[p] z g
    simp [he, hz]
  have h := congrArg (aeval (R := ℚ) (z : ℚ_[p])) heq
  rw [aeval_map_algebraMap, hz', map_mul, aeval_C] at h
  exact (mul_eq_zero.mp h.symm).resolve_left ((algebraMap ℚ ℚ_[p]).injective.ne hbq)

private theorem norm_le_at_integral_arg (f : ℚ[X]) :
    ∃ N : ℕ, ∀ (p : PrimeIndex), N < p.val → ∀ z : ℤ_[p.val],
      ‖aeval (z : ℚ_[p.val]) f‖ ≤ 1 := by
  by_cases hf : f = 0
  · exact ⟨0,fun p _ z => by simp [hf]⟩
  obtain ⟨b,g,hb,_,heq⟩ := exists_integer_multiple f hf
  refine ⟨b.natAbs, ?_⟩
  intro p hp z
  have hbn : ¬ (p.val : ℤ) ∣ b := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hb) hp) (Int.natCast_dvd.mp h)
  have hnorm : ‖(b : ℚ_[p.val])‖ = 1 := le_antisymm (Padic.norm_int_le_one _)
    (le_of_not_gt (hbn ∘ Padic.norm_intCast_lt_one_iff.mp))
  have he := congrArg (aeval (R := ℚ) (z : ℚ_[p.val])) heq
  rw [aeval_map_algebraMap, map_mul, aeval_C] at he
  have h := congrArg norm he
  simp only [map_intCast, norm_mul, hnorm, one_mul] at h
  have he' : aeval (z : ℚ_[p.val]) g = ((aeval z g : ℤ_[p.val]) : ℚ_[p.val]) :=
    aeval_algebraMap_apply ℚ_[p.val] z g
  rw [← h, he']; exact PadicInt.norm_le_one _

/-- Arbitrarily large primes admit an embedding of the given number field
in the rational p-adic field, taking every element of the finite nonzero
list to multiplicative valuation one. -/
theorem exists_embedding (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    (S : Finset L) (hS : ∀ s ∈ S, s ≠ 0) (N : ℕ) :
    ∃ p : PrimeIndex, N < p.val ∧ ∃ φ : L →ₐ[ℚ] ℚ_[p.val],
      ∀ s ∈ S, Padic.mulValuation (φ s) = 1 := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ L
  choose repr hrepr using fun s : L => pb.exists_eq_aeval' s
  choose bound hbound using fun s : L => norm_le_at_integral_arg (repr s)
  let T := S ∪ S.image Inv.inv
  obtain ⟨p,hp,z,hz⟩ := exists_padic_root (minpoly ℚ pb.gen)
    (minpoly.irreducible pb.isIntegral_gen) (max N (T.sup bound))
  let φ := pb.lift (z : ℚ_[p.val]) hz
  have hsmall (s : L) (hs : s ∈ T) : ‖φ s‖ ≤ 1 := by
    have hval : φ s = aeval (z : ℚ_[p.val]) (repr s) := by
      conv_lhs => rw [hrepr s]
      exact pb.lift_aeval _ hz _
    rw [hval]; exact hbound s p ((Finset.le_sup hs).trans_lt ((le_max_right ..).trans_lt hp)) z
  refine ⟨p,(le_max_left ..).trans_lt hp,φ,?_⟩
  intro s hs
  apply mulValuation_eq_one_of_norm_eq_one
  have hs1 := hsmall s (Finset.mem_union_left _ hs)
  have hi := hsmall s⁻¹ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs))
  have hpos : 0 < ‖φ s‖ := norm_pos_iff.mpr ((_root_.map_ne_zero φ).mpr (hS s hs))
  rw [map_inv₀, norm_inv] at hi
  exact hs1.antisymm ((inv_le_one₀ hpos).mp hi)

end UnconditionalCounterexample.PrivateGuardsNumberField
