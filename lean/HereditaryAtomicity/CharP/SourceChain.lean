import HereditaryAtomicity.PrincipalComponents
import HereditaryAtomicity.SemilocalDimension
import Factorization.PrincipalIdeals
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Source chains above a maximal stalk

Failure of ACCP at a maximal localization of a one-dimensional semilocal domain
produces a chain in the original ring. Its nonzero endpoints are supported only at the
chosen maximal ideal, and its consecutive ratios lie in that ideal.

The generic chain transforms retain individual selected ratios and allow
multiplication of every ratio by a source unit. No hereditary-atomicity
hypothesis is imposed on a localization.
-/

open scoped BigOperators

noncomputable section
namespace HereditaryAtomicity
universe u
variable {D : Type u} [CommRing D] [IsDomain D]

/-- Every nonzero principal ideal in a maximal localization of a semilocal
one-dimensional domain contracts to a nonzero principal ideal whose generator
is a unit at every other maximal ideal. -/
theorem exists_generator_contracted_local_principal
    [Finite (MaximalSpectrum D)] [Ring.KrullDimLE 1 D]
    (M : Ideal D) [M.IsMaximal]
    (a : Localization.AtPrime M) (ha : a ≠ 0) :
    ∃ x : D, x ≠ 0 ∧
      Ideal.span {x} = (Ideal.span {a}).under D ∧
      ∀ Q : MaximalSpectrum D, Q.asIdeal ≠ M → x ∉ Q.asIdeal := by
  classical
  let S := Localization.AtPrime M
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj M.primeCompl a
  have hsu : IsUnit (algebraMap D S s) := IsLocalization.map_units S s
  have hr : r ≠ 0 := by
    intro h
    have hprod : a * algebraMap D S s = 0 := by simpa only [h, map_zero] using hrs
    exact (mul_ne_zero ha hsu.ne_zero) hprod
  have hspan : Ideal.span {a} = Ideal.span {algebraMap D S r} := by
    apply Ideal.span_singleton_eq_span_singleton.mpr
    rw [← hrs]
    exact (associated_mul_unit_left a _ hsu).symm
  have hI : (Ideal.span {a}).under D = principalComponent M r := by
    rw [hspan]
    rfl
  let I := principalComponent M r
  let : I.IsPrincipal := principalComponent_isPrincipal M hr
  let x := Submodule.IsPrincipal.generator I
  have hx : Ideal.span {x} = I := Ideal.span_singleton_generator _
  have hx0 : x ≠ 0 := by
    intro hzero
    have hmem : r ∈ Ideal.span {x} := hx.symm ▸ mem_principalComponent_self M r
    exact hr (by simpa [hzero] using hmem)
  refine ⟨x, hx0, hx.trans hI.symm, ?_⟩
  intro Q hQM hxQ
  have hmap := principalComponent_map_other M Q.asIdeal (Ne.symm hQM) hr
  have hunit : IsUnit (algebraMap D (Localization.AtPrime Q.asIdeal) x) := by
    apply Ideal.span_singleton_eq_top.mp
    change Ideal.map (algebraMap D (Localization.AtPrime Q.asIdeal)) I = ⊤ at hmap
    rw [← hx, Ideal.map_span, Set.image_singleton] at hmap
    exact hmap
  exact ((IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime Q.asIdeal) Q.asIdeal x).mp hunit) hxQ

/-- A failed ACCP chain in an actual maximal stalk lifts to source endpoints
supported only at that maximal ideal, with every ratio in the ideal. -/
theorem exists_source_nonunit_chain_of_not_wfDvdMonoid_atPrime
    [Finite (MaximalSpectrum D)] [Ring.KrullDimLE 1 D]
    (M : Ideal D) [M.IsMaximal]
    (hfail : ¬ WfDvdMonoid (Localization.AtPrime M)) :
    ∃ x c : ℕ → D,
      (∀ n, x n ≠ 0) ∧ (∀ n, x n ∈ M) ∧
      (∀ n, c n ∈ M) ∧
      (∀ n, x n = x (n + 1) * c n) ∧
      ∀ (n : ℕ) (Q : MaximalSpectrum D), Q.asIdeal ≠ M → x n ∉ Q.asIdeal := by
  classical
  let S := Localization.AtPrime M
  let f := algebraMap D S
  obtain ⟨a, b, ha, hb, hab⟩ := Factorization.not_wfDvdMonoid_iff_exists_nonunit_chain.mp hfail
  choose x hx0 hx hxQ using fun n => exists_generator_contracted_local_principal M (a n) (ha n)
  have hmap : ∀ n, Ideal.span {f (x n)} = Ideal.span {a n} := by
    intro n
    have h := congrArg (Ideal.map f) (hx n)
    rw [Ideal.map_span, Set.image_singleton] at h
    exact h.trans (IsLocalization.map_under M.primeCompl S (Ideal.span {a n}))
  have hle : ∀ n, Ideal.span {x n} ≤ Ideal.span {x (n + 1)} := by
    intro n
    rw [hx n, hx (n + 1)]
    exact Ideal.comap_mono (Ideal.span_singleton_le_span_singleton.mpr ⟨b n, hab n⟩)
  have hc : ∀ n, ∃ c : D, x n = x (n + 1) * c := by
    intro n
    exact Ideal.span_singleton_le_span_singleton.mp (hle n)
  choose c hc using hc
  have hcM : ∀ n, c n ∈ M := by
    intro n
    by_contra hn
    have hcu : IsUnit (f (c n)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff S M (c n)).mpr hn
    have heq : Ideal.span {a n} = Ideal.span {a (n + 1)} := by
      rw [← hmap n, ← hmap (n + 1), hc n, map_mul]
      exact Ideal.span_singleton_eq_span_singleton.mpr
        (associated_mul_unit_left (f (x (n + 1))) _ hcu)
    have hlt : Ideal.span {a n} < Ideal.span {a (n + 1)} :=
      Ideal.span_singleton_lt_span_singleton.mpr ⟨ha (n + 1), b n, hb n, hab n⟩
    exact hlt.ne heq
  have hxM : ∀ n, x n ∈ M := by
    intro n
    rw [hc n]
    exact M.mul_mem_left _ (hcM n)
  exact ⟨x, c, hx0, hxM, hcM, hc, hxQ⟩

/-- The same source-chain lift with the dimension bound supplied by hereditary
atomicity of the original semilocal domain. -/
theorem semilocal_ha_exists_source_nonunit_chain
    [Finite (MaximalSpectrum D)] (hD : Factorization.IsHereditarilyAtomic D)
    (M : MaximalSpectrum D)
    (hfail : ¬ WfDvdMonoid (Localization.AtPrime M.asIdeal)) :
    ∃ x c : ℕ → D,
      (∀ n, x n ≠ 0) ∧ (∀ n, x n ∈ M.asIdeal) ∧
      (∀ n, c n ∈ M.asIdeal) ∧
      (∀ n, x n = x (n + 1) * c n) ∧
      ∀ (n : ℕ) (Q : MaximalSpectrum D), Q ≠ M → x n ∉ Q.asIdeal := by
  let : Ring.KrullDimLE 1 D := semilocal_dimensionLE_one hD
  obtain ⟨x, c, hx, hxM, hcM, hxc, hxQ⟩ :=
    exists_source_nonunit_chain_of_not_wfDvdMonoid_atPrime M.asIdeal hfail
  refine ⟨x, c, hx, hxM, hcM, hxc, ?_⟩
  intro n Q hQM
  exact hxQ n Q (fun h => hQM (MaximalSpectrum.ext h))

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- Iterating a source chain gives an exact prefix-product identity in the source ring. -/
theorem sourceChain_prefix_product (x a : ℕ → R)
    (hxa : ∀ n, x n = x (n + 1) * a n) (n : ℕ) :
    x 0 = x n * ∏ i ∈ Finset.range n, a i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, mul_right_comm, ← hxa n]
    exact ih

omit [IsDomain R] in
/-- Every source-chain endpoint divides its fixed top inside the source ring. -/
theorem sourceChain_endpoint_dvd_top (x a : ℕ → R)
    (hxa : ∀ n, x n = x (n + 1) * a n) (n : ℕ) : x n ∣ x 0 :=
  ⟨∏ i ∈ Finset.range n, a i, sourceChain_prefix_product x a hxa n⟩

omit [IsDomain R] in
/-- Every individual ratio divides the fixed top inside the source ring. -/
theorem sourceChain_ratio_dvd_top (x a : ℕ → R)
    (hxa : ∀ n, x n = x (n + 1) * a n) (n : ℕ) : a n ∣ x 0 := by
  exact (show a n ∣ x n from ⟨x (n + 1), by rw [hxa n, mul_comm]⟩).trans
    (sourceChain_endpoint_dvd_top x a hxa n)

/-- An arbitrary strictly increasing selection of the ratios of a nonzero source
chain remains a source chain with the same top element. -/
theorem exists_sourceChain_ratio_subsequence (x a : ℕ → R)
    (hx : ∀ n, x n ≠ 0) (hxa : ∀ n, x n = x (n + 1) * a n)
    (f : ℕ → ℕ) (hf : StrictMono f) :
    ∃ y : ℕ → R, y 0 = x 0 ∧ (∀ n, y n ≠ 0) ∧
      ∀ n, y n = y (n + 1) * a (f n) := by
  classical
  have ha : ∀ n, a n ≠ 0 := by
    intro n hn
    exact hx n (by rw [hxa n, hn, mul_zero])
  let P : ℕ → R := fun n => ∏ i ∈ Finset.range n, a (f i)
  have hP0 : ∀ n, P n ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.mpr fun i _ => ha (f i)
  have hPd : ∀ n, P n ∣ x 0 := by
    intro n
    have hsub : (Finset.range n).image f ⊆ Finset.range (f n) := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (hf (Finset.mem_range.mp hi))
    have himage : P n = ∏ j ∈ (Finset.range n).image f, a j := by
      rw [Finset.prod_image hf.injective.injOn]
    rw [himage]
    apply (Finset.prod_dvd_prod_of_subset _ _ a hsub).trans
    exact ⟨x (f n), by simpa only [mul_comm] using sourceChain_prefix_product x a hxa (f n)⟩
  choose y hy using hPd
  refine ⟨y, ?_, ?_, ?_⟩
  · simpa [P] using (hy 0).symm
  · intro n hn
    exact hx 0 (by rw [hy n, hn, mul_zero])
  · intro n
    apply mul_left_cancel₀ (hP0 n)
    calc
      P n * y n = x 0 := (hy n).symm
      _ = P (n + 1) * y (n + 1) := hy (n + 1)
      _ = P n * (y (n + 1) * a (f n)) := by
        simp only [P, Finset.prod_range_succ]
        ac_rfl

/-- Multiplying each ratio by a source unit preserves a source chain and its
top. All inverse factors belong to the source ring itself. -/
theorem exists_sourceChain_unit_twist (x a : ℕ → R)
    (hx : ∀ n, x n ≠ 0) (hxa : ∀ n, x n = x (n + 1) * a n)
    (u : ℕ → Rˣ) :
    ∃ y : ℕ → R, y 0 = x 0 ∧ (∀ n, y n ≠ 0) ∧
      ∀ n, y n = y (n + 1) * ((u n : R) * a n) := by
  let U : ℕ → Rˣ := fun n => ∏ i ∈ Finset.range n, u i
  let y : ℕ → R := fun n => x n * ((U n)⁻¹ : Rˣ)
  refine ⟨y, ?_, ?_, ?_⟩
  · simp [y, U]
  · intro n
    exact mul_ne_zero (hx n) (Units.ne_zero _)
  · intro n
    dsimp only [y]
    have hU : U (n + 1) = U n * u n := Finset.prod_range_succ _ n
    rw [hxa n, hU, mul_inv_rev, Units.val_mul]
    simp only [mul_assoc, mul_left_comm, mul_comm]
    rw [Units.mul_inv_cancel_left]


omit [IsDomain R] in
/-- If the fixed top of a source chain avoids an ideal, every endpoint does. -/
theorem sourceChain_endpoint_not_mem_of_top_not_mem (x a : ℕ → R)
    (hxa : ∀ n, x n = x (n + 1) * a n) (Q : Ideal R)
    (hQ : x 0 ∉ Q) (n : ℕ) : x n ∉ Q := by
  intro hn
  exact hQ (Q.mem_of_dvd (sourceChain_endpoint_dvd_top x a hxa n) hn)

omit [IsDomain R] in
/-- If the fixed top avoids an ideal, every individual ratio does as well. -/
theorem sourceChain_ratio_not_mem_of_top_not_mem (x a : ℕ → R)
    (hxa : ∀ n, x n = x (n + 1) * a n) (Q : Ideal R)
    (hQ : x 0 ∉ Q) (n : ℕ) : a n ∉ Q := by
  intro hn
  exact hQ (Q.mem_of_dvd (sourceChain_ratio_dvd_top x a hxa n) hn)

omit [IsDomain R] in
/-- A chain whose ratios lie in an ideal has every endpoint in that ideal. -/
theorem sourceChain_endpoint_mem_of_ratios_mem (x a : ℕ → R)
    (hxa : ∀ n, x n = x (n + 1) * a n) (M : Ideal R)
    (hM : ∀ n, a n ∈ M) (n : ℕ) : x n ∈ M := by
  rw [hxa n]
  exact M.mul_mem_left _ (hM n)

end HereditaryAtomicity
