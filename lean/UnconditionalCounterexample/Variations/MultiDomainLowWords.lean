import UnconditionalCounterexample.Variations.MultiDomain
import UnconditionalCounterexample.PrincipalProfiles
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Units of the multivariate horizontal localization

A prime polynomial becomes a unit precisely when it divides a raw
denominator. Unique factorization then expresses every unit as a rational
constant times a finite signed word in the raw polynomials. Triangular
inversion gives the same description in the normalized generators.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open PrincipalProfiles

variable {r : ℕ} (A : Data r)

abbrev rawValue (i : ℕ) : FunctionField r := algebraMap (Polys r) (FunctionField r) (A.raw i)

theorem rawValue_ne_zero (i : ℕ) : rawValue A i ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Polys r) (FunctionField r))).mpr (A.raw_ne i)

variable {ι : Type*} (F : ι → Polys r) (B : Subalgebra (Polys r) (FunctionField r))
  [IsLocalization (Submonoid.closure (Set.range F)) B]

abbrev fieldPolynomial (i : ι) : FunctionField r := algebraMap (Polys r) (FunctionField r) (F i)

private theorem fieldPolynomial_ne_zero (hF : ∀ i, Irreducible (F i)) (i : ι) :
    fieldPolynomial F i ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Polys r) (FunctionField r))).mpr (hF i).ne_zero

private theorem prime_dvd_closure {p : Polys r} (hp : Prime p) :
    (∃ f ∈ Submonoid.closure (Set.range F), p ∣ f) ↔ ∃ i, p ∣ F i := by
  constructor
  · rintro ⟨f, hf, hpf⟩
    induction hf using Submonoid.closure_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact ⟨i, hpf⟩
    | one => exact (hp.not_dvd_one hpf).elim
    | mul _ _ _ _ ha hb => exact (hp.dvd_or_dvd hpf).elim ha hb
  · rintro ⟨i, hi⟩
    exact ⟨_, Submonoid.subset_closure (Set.mem_range_self i), hi⟩

private def RawExpression (x : FunctionField r) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ ∃ e : ι →₀ ℤ, x = algebraMap ℚ (FunctionField r) c * word (fieldPolynomial F) e

private theorem expression_mul (hF : ∀ i, Irreducible (F i)) {x y : FunctionField r}
    (hx : RawExpression F x) (hy : RawExpression F y) : RawExpression F (x*y) := by
  obtain ⟨c, hc, e, rfl⟩ := hx
  obtain ⟨d, hd, f, rfl⟩ := hy
  exact ⟨c*d, mul_ne_zero hc hd, e+f, by rw [map_mul, word_add _ (fieldPolynomial_ne_zero F hF)]; ring⟩

private theorem expression_unit {f : Polys r} (hf : IsUnit f) :
    RawExpression F (algebraMap (Polys r) (FunctionField r) f) := by
  obtain ⟨c, hc, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hf
  exact ⟨c, hc.ne_zero, 0, by simp [word, ← MvPolynomial.algebraMap_eq,
    IsScalarTower.algebraMap_apply ℚ (Polys r) (FunctionField r)]⟩

private theorem expression_of_unitImage (hF : ∀ i, Irreducible (F i)) (f : Polys r)
    (hf : IsUnit (algebraMap (Polys r) B f)) :
    RawExpression F (algebraMap (Polys r) (FunctionField r) f) := by
  classical
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp at hf
  | h₂ f hunit => exact expression_unit F hunit
  | h₃ a p _ hp ih =>
    rw [map_mul, IsUnit.mul_iff] at hf
    obtain ⟨i, hi⟩ := (prime_dvd_closure F hp).mp
      ((IsLocalization.algebraMap_isUnit_iff (Submonoid.closure (Set.range F))).mp hf.1)
    obtain ⟨u, hu⟩ := (hp.irreducible.dvd_irreducible_iff_associated (hF i)).mp hi
    have he : p = F i * (↑u⁻¹ : Polys r) := by
      rw [← hu, mul_assoc, u.mul_inv, mul_one]
    have hr : RawExpression F (fieldPolynomial F i) := ⟨1, one_ne_zero, Finsupp.single i 1, by
      simp [word, Finsupp.prod_single_index]⟩
    rw [map_mul]
    apply expression_mul F hF _ (ih hf.2)
    rw [he, map_mul]
    exact expression_mul F hF hr (expression_unit F u⁻¹.isUnit)

theorem pole_unit_raw_word_of_isLocalization (hF : ∀ i, Irreducible (F i)) (u : Bˣ) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ e : ι →₀ ℤ, (((u : B) : FunctionField r)) =
      algebraMap ℚ (FunctionField r) c * word (fieldPolynomial F) e := by
  obtain ⟨⟨f, d⟩, hd⟩ := IsLocalization.surj (Submonoid.closure (Set.range F)) (u : B)
  have hud := IsLocalization.map_units B d
  have huf := hd ▸ u.isUnit.mul hud
  obtain ⟨c, hc, e, hf⟩ := expression_of_unitImage F B hF f huf
  obtain ⟨b, hb, g, hg⟩ := expression_of_unitImage F B hF d hud
  have hd' : ((u : B) : FunctionField r) * algebraMap (Polys r) (FunctionField r) d =
      algebraMap (Polys r) (FunctionField r) f := congrArg B.subtype hd
  have hne : algebraMap (Polys r) (FunctionField r) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polys r) (FunctionField r))).mpr
      (by
        have h₀ : Submonoid.closure (Set.range F) ≤ nonZeroDivisors (Polys r) := by
          apply Submonoid.closure_le.mpr
          rintro _ ⟨i, rfl⟩
          exact mem_nonZeroDivisors_iff_ne_zero.mpr (hF i).ne_zero
        exact mem_nonZeroDivisors_iff_ne_zero.mp (h₀ d.property))
  rw [← eq_div_iff hne, hf, hg] at hd'
  refine ⟨c/b, div_ne_zero hc hb, e-g, ?_⟩
  rw [hd', map_div₀, word_sub _ (fieldPolynomial_ne_zero F hF)]
  ring

theorem prime_dvd_denominator_iff {p : Polys r} (hp : Prime p) :
    (∃ f ∈ denominators A, p ∣ f) ↔ ∃ i, p ∣ A.raw i :=
  prime_dvd_closure A.raw hp

theorem pole_unit_raw_word (hraw : ∀ i, Irreducible (A.raw i)) (u : (poleAlgebra A)ˣ) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ e : ℕ →₀ ℤ, (((u : poleAlgebra A) : FunctionField r)) =
      algebraMap ℚ (FunctionField r) c * word (rawValue A) e :=
  pole_unit_raw_word_of_isLocalization A.raw (poleAlgebra A) hraw u

/-- Every pole unit has a triangularly normalized signed word, without any
choice of representatives for associate classes of multivariate polynomials. -/
theorem pole_unit_normalized_word (hraw : ∀ i, Irreducible (A.raw i)) (E : ℕ → ℕ)
    (u : (poleAlgebra A)ˣ) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ e : ℕ →₀ ℤ, (((u : poleAlgebra A) : FunctionField r)) =
      algebraMap ℚ (FunctionField r) c * word (RawWords.normalizedFactor (rawValue A) E) e := by
  obtain ⟨c, hc, e, he⟩ := pole_unit_raw_word A hraw u
  obtain ⟨d, hd⟩ := exists_normalized_word (rawValue A) (rawValue_ne_zero A) E e
  exact ⟨c, hc, d, he.trans (congrArg _ hd)⟩

end UnconditionalCounterexample.Variations.MultiDomain
