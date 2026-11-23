import Factorization.WeakACCP

/-!
# Realizing the obstruction to a maximal common divisor

For the dyadic example, a late balanced column can be added to any common
divisor profile of the two specified elements. The realization step below
uses the same element for that column in both divisibility tests.
-/

namespace UnconditionalCounterexample.Dyadic

variable {R : Type*} [CommRing R] [IsDomain R]

/-- If a positive column can be added below both target profiles, the element
realizing it strictly extends the given common divisor. The comparison test
uses the entire profile, including any auxiliary valuations. -/
theorem exists_common_divisor_extension_of_profiles {P ι : Type*} [LE P] [Add P] [Zero P]
    (v : R → P) (v_one : v 1 = 0)
    (v_mul : ∀ a b : R, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b)
    (dvd_iff : ∀ a b : R, a ≠ 0 → b ≠ 0 → (a ∣ b ↔ v a ≤ v b))
    (balanced : ι → R) (balanced_ne : ∀ i, balanced i ≠ 0)
    (positive : ∀ i, ¬ v (balanced i) ≤ 0)
    {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (room : ∀ e : R, e ≠ 0 → v e ≤ v x → v e ≤ v y →
      ∃ i, v e + v (balanced i) ≤ v x ∧ v e + v (balanced i) ≤ v y)
    {e : R} (hex : e ∣ x) (hey : e ∣ y) :
    ∃ u : R, ¬ IsUnit u ∧ e * u ∣ x ∧ e * u ∣ y := by
  have he : e ≠ 0 := fun h => hx (zero_dvd_iff.mp (h ▸ hex))
  obtain ⟨i, hix, hiy⟩ := room e he ((dvd_iff e x he hx).mp hex) ((dvd_iff e y he hy).mp hey)
  have hprod := v_mul e (balanced i) he (balanced_ne i)
  have hne := mul_ne_zero he (balanced_ne i)
  refine ⟨balanced i, ?_, (dvd_iff _ _ hne hx).mpr (hprod ▸ hix),
    (dvd_iff _ _ hne hy).mpr (hprod ▸ hiy)⟩
  intro hu
  exact positive i (v_one ▸ (dvd_iff _ _ (balanced_ne i) one_ne_zero).mp
    (isUnit_iff_dvd_one.mp hu))

/-- The strict-extension property of the specified nonzero pair rules out
both strong atomicity and weak ACCP in its ambient domain. -/
theorem obstruction_of_common_divisor_extensions [DecidableEq R]
    {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (extend : ∀ e : R, e ∣ x → e ∣ y →
      ∃ u : R, ¬ IsUnit u ∧ e * u ∣ x ∧ e * u ∣ y) :
    (¬ ∃ e : R, Factorization.IsMaximalCommonDivisor {x, y} e) ∧
      ¬ Factorization.IsStronglyAtomicDomain R ∧ ¬ Factorization.IsWeakACCP R := by
  have hpair : ¬ ∃ e : R, Factorization.IsMaximalCommonDivisor {x, y} e := by
    rintro ⟨e, he⟩
    obtain ⟨u, hnu, hux, huy⟩ := extend e (he.1 x (by simp)) (he.1 y (by simp))
    exact hnu (he.2 u (by simpa using And.intro hux huy))
  have hs : ¬ Factorization.IsStronglyAtomicDomain R := by
    intro h
    obtain ⟨e, a, b, rfl, rfl, hab⟩ := h.2 x y hx hy
    exact hpair ⟨e, (Factorization.isMaximalCommonDivisor_pair_iff
      (left_ne_zero_of_mul hx)).mpr hab⟩
  exact ⟨hpair, hs, fun h => hs h.isStronglyAtomicDomain⟩

end UnconditionalCounterexample.Dyadic
