import UnconditionalCounterexample.Variations.DimensionFlags
import UnconditionalCounterexample.Variations.PrivateGuardsPunctures

/-!
# Dimension of the generic fibre after puncturing

In a Noetherian ring, a prime of height greater than d contains one of height
exactly d+1. A localization meeting all primes of that one height thus has
dimension at most d. For a polynomial ring the retained coordinate flag
supplies the matching lower bound.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial

/-- Meeting all primes of one specified height gives an upper bound for the
dimension of the actual localization. -/
theorem dimension_le_of_punctured {A : Type*} [CommRing A] [IsNoetherianRing A]
    (M : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]
    (d : ℕ) (hmeet : ∀ P : PrimeSpectrum A, P.asIdeal.height = (d+1 : ℕ) →
      ∃ x : M, (x : A) ∈ P.asIdeal) : ringKrullDim B ≤ d := by
  rw [ringKrullDim_le_iff_height_le]
  intro J hJ
  let P : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) ⟨J, hJ⟩
  suffices hle : P.asIdeal.height ≤ d by
    have he : P.asIdeal.height = J.height := IsLocalization.height_under M J
    exact_mod_cast he ▸ hle
  by_contra! h
  have hd : (d+1 : ℕ) ≤ Order.height P := by
    rw [← P.height_eq_orderHeight]
    simpa only [Nat.cast_add, Nat.cast_one] using (ENat.add_one_le_iff (ENat.natCast_ne_top d)).mpr h
  have hfin : Order.height P < ⊤ := by
    rw [← P.height_eq_orderHeight]
    exact P.asIdeal.height_lt_top_of_isPrime
  have hex : ∃ Q ≤ P, Order.height Q = (d+1 : ℕ) := by
    rcases eq_or_lt_of_le hd with he | hlt
    · exact ⟨P,le_rfl,he.symm⟩
    · obtain ⟨Q, hl, hQ⟩ := (Order.coe_lt_height_iff hfin).mp hlt
      exact ⟨Q, hl.le, hQ⟩
  obtain ⟨Q, hQP, hQ⟩ := hex
  obtain ⟨x,hx⟩ := hmeet Q (Q.height_eq_orderHeight.trans hQ)
  exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ (hQP hx) (IsLocalization.map_units B x))

/-- The height of the first d coordinate equations in a polynomial ring. -/
theorem coordinate_height {k : Type*} [Field k] {r : ℕ} (c : Fin r → k) (d : ℕ) (hd : d ≤ r) :
    (coordinatePrime c d).asIdeal.height = d := by
  let l := coordinateFlag c r le_rfl
  have hdim : ringKrullDim (MvPolynomial (Fin r) k) = r := by
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  have hmax : (l.length : ℕ∞) = Order.height l.last := by
    apply le_antisymm Order.length_le_height_last
    have h := Order.height_le_krullDim l.last
    change (Order.height l.last : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin r) k) at h
    rw [hdim] at h
    exact_mod_cast h
  exact (coordinatePrime c d).height_eq_orderHeight.trans
    (Order.height_eq_index_of_length_eq_height_last hmax ⟨d, by change d < r+1; omega⟩)

/-- A surviving coordinate flag of length d and punctures at every prime of
height d+1 certify that this particular rational fibre has dimension exactly d. -/
theorem dimension_eq_of_punctured {k : Type*} [Field k] {r : ℕ} (c : Fin r → k)
    (d : ℕ) (hd : d ≤ r) (M : Submonoid (MvPolynomial (Fin r) k)) (B : Type*) [CommRing B]
    [Algebra (MvPolynomial (Fin r) k) B] [IsLocalization M B]
    (hret : Disjoint (M : Set (MvPolynomial (Fin r) k)) (coordinatePrime c d).asIdeal)
    (hmeet : ∀ P : PrimeSpectrum (MvPolynomial (Fin r) k), P.asIdeal.height = (d+1 : ℕ) →
      ∃ x : M, (x : MvPolynomial (Fin r) k) ∈ P.asIdeal) : ringKrullDim B = d :=
  le_antisymm (dimension_le_of_punctured M B d hmeet)
    (Order.LTSeries.length_le_krullDim (liftPrimeFlag B M (coordinateFlag c d hd) hret))

end UnconditionalCounterexample.Variations.PrivateGuards
