import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Inverting every predecessor in multivariate recovery

A listed word with numerator a power of a late polynomial and denominator
divisible by a fixed earlier polynomial propagates membership in a maximal
ideal. The empty-intersection test excludes that possibility for every earlier
polynomial. This proves that the earlier polynomials are units in the subalgebra.
-/

namespace UnconditionalCounterexample.MultivariateInversion

open MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] [Finite σ]

/-- Empty common geometric zero locus gives a unit ideal already over the
coefficient field. -/
theorem span_eq_top_of_no_common_zero (S : Set (MvPolynomial σ k))
    (hS : ∀ u : σ → K, ∃ f ∈ S, aeval u f ≠ 0) : Ideal.span S = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  obtain ⟨u, hu⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hm
  obtain ⟨p, hp, hne⟩ := hS u
  have hmem := hle (Ideal.subset_span hp)
  rw [hu] at hmem
  exact hne ((mem_vanishingIdeal_singleton_iff u p).mp hmem)

/-- Each `F j` is a unit in the intermediate ring containing the polynomial
ring and the listed fractions. For a given predecessor there must be
infinitely many word numerators whose denominators it divides. -/
theorem isUnit_of_listed_words {C : Type*} [CommRing C]
    (φ : MvPolynomial σ k →+* C) (F : ℕ → MvPolynomial σ k) (r : ℕ)
    (hgeom : ∀ s : Finset ℕ, s.card = r + 1 → ∀ u : σ → K,
      ∃ i ∈ s, aeval u (F i) ≠ 0)
    (hword : ∀ j, {i | ∃ a : ℕ, 0 < a ∧ φ (F j) ∣ φ (F i) ^ a}.Infinite)
    (j : ℕ) : IsUnit (φ (F j)) := by
  by_contra h
  obtain ⟨m, hm, hj⟩ := exists_max_ideal_of_mem_nonunits h
  obtain ⟨s, hs, hcard⟩ := (hword j).exists_subset_card_eq (r + 1)
  have hspan : Ideal.span (F '' (s : Set ℕ)) = ⊤ := by
    apply span_eq_top_of_no_common_zero (K := K)
    intro u
    obtain ⟨i, hi, hne⟩ := hgeom s hcard u
    exact ⟨F i, ⟨i, hi, rfl⟩, hne⟩
  have hle : Ideal.span (F '' (s : Set ℕ)) ≤ m.comap φ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨a, _, b, hb⟩ := hs hi
    apply hm.isPrime.mem_of_pow_mem a
    rw [hb]; exact m.mul_mem_right b hj
  exact (Ideal.comap_ne_top φ hm.ne_top) (top_unique (hspan ▸ hle))

/-- A localization is generated, over any intermediate subring containing its
polynomial ring, as soon as every generating denominator is a unit there.
The statement supplies the actual equality of rings inside the localization. -/
theorem subalgebra_eq_top_of_denominator_units
    {R L B : Type*} [CommRing R] [CommRing L] [CommRing B] [Algebra R B] [Algebra L B]
    (F : ℕ → R) [IsLocalization (Submonoid.closure (Set.range F)) B]
    (C : Subalgebra L B) (φ : R →+* C) (hφ : ∀ f, (φ f : B) = algebraMap R B f)
    (hunit : ∀ j, IsUnit (φ (F j))) : C = ⊤ := by
  apply top_unique
  intro b _
  obtain ⟨⟨x, d⟩, h⟩ := IsLocalization.surj (Submonoid.closure (Set.range F)) b
  have hUnits : Submonoid.closure (Set.range F) ≤ (IsUnit.submonoid C).comap φ := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨j,rfl⟩; exact hunit j
  obtain ⟨v, hv⟩ := hUnits d.property
  have hB : b * ((v : C) : B) = algebraMap R B x := by
    simpa only [hv, hφ] using h
  have hinv : ((v : C) : B) * ((↑v⁻¹ : C) : B) = 1 := by
    exact congrArg Subtype.val v.mul_inv
  have : b = algebraMap R B x * ((↑v⁻¹ : C) : B) := by
    rw [← hB, mul_assoc, hinv, mul_one]
  rw [this]; exact C.mul_mem ((hφ x) ▸ (φ x).property) (↑v⁻¹ : C).property

/-- If the literal coordinates are integral over the word algebra, the
localization is finite over it. The quotient of each late numerator power
by its listed denominator is required to lie in the given algebra. -/
theorem finite_of_integral_coordinates_and_words {B : Type*} [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B]
    (F : ℕ → MvPolynomial σ k) [IsLocalization (Submonoid.closure (Set.range F)) B]
    (A : Subalgebra k B)
    (hint : ∀ i, IsIntegral A (algebraMap (MvPolynomial σ k) B (X i)))
    (hgeom : ∀ s : Finset ℕ, s.card = Nat.card σ + 1 → ∀ u : σ → K,
      ∃ i ∈ s, aeval u (F i) ≠ 0)
    (hword : ∀ j, {i | ∃ (a : ℕ) (H : MvPolynomial σ k) (w : A), 0 < a ∧ F j ∣ H ∧
      algebraMap (MvPolynomial σ k) B (F i) ^ a = algebraMap (MvPolynomial σ k) B H * w}.Infinite) :
    Module.Finite A B := by
  let x (i : σ) := algebraMap (MvPolynomial σ k) B (X i)
  let E := Algebra.adjoin A (Set.range x)
  have hfg : Module.Finite A E := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x)
    (fun _ ⟨i, hi⟩ => hi ▸ hint i)
  let y (i : σ) : E := ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let φ := (aeval (R := k) y).toRingHom
  have hφall : (E.restrictScalars k).val.comp (aeval (R := k) y) = IsScalarTower.toAlgHom k (MvPolynomial σ k) B := by
    ext i
    change ((aeval (R := k) y (X i) : E) : B) = _
    rw [aeval_X]; rfl
  have hφ (p : MvPolynomial σ k) : (φ p : B) = algebraMap (MvPolynomial σ k) B p :=
    DFunLike.congr_fun hφall p
  have hdiv (j : ℕ) : {i | ∃ a : ℕ, 0 < a ∧ φ (F j) ∣ φ (F i) ^ a}.Infinite := by
    apply (hword j).mono
    rintro i ⟨a,H,w,ha,⟨q,rfl⟩,hw⟩
    refine ⟨a, ha, φ q * algebraMap A E w, Subtype.ext ?_⟩
    change (φ (F i) : B) ^ a = (φ (F j) : B) * ((φ q : B) * w)
    simpa only [hφ, map_mul, mul_assoc] using hw
  have htop := subalgebra_eq_top_of_denominator_units F E φ hφ
    (isUnit_of_listed_words φ F (Nat.card σ) hgeom hdiv)
  apply Module.Finite.of_surjective E.val.toLinearMap
  exact fun b => ⟨⟨b, htop.ge (by trivial)⟩, rfl⟩

end UnconditionalCounterexample.MultivariateInversion
