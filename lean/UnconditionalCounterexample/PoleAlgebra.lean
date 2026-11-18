import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Localization.AsSubring

/-!
# The actual generated pole algebra

The algebra generated inside `RatFunc k` by `X` and the inverses of a set `S`
of nonzero polynomials is the actual localization of `k[X]` at the multiplicative
closure of `S`. The polynomial algebra structure is the codomain restriction
of the canonical polynomial inclusion. Both the polynomial and ground-field
algebra maps are retained, and the localization equivalence is the identity
on the represented rational functions.

The set `S` may be infinite. Membership is characterized by a fraction with
denominator in its multiplicative closure, or by divisibility of the reduced
denominator into such an element. This supplies the denominator support API
for subsequent spectrum and retained-point calculations.
-/

noncomputable section

namespace UnconditionalCounterexample.PoleAlgebra

open Polynomial

variable {k : Type*} [Field k]

/-- The literal generated algebra used by the generic-curve construction. -/
def generated (S : Set k[X]) : Subalgebra k (RatFunc k) :=
  Algebra.adjoin k (insert (RatFunc.X : RatFunc k)
    ((fun p : k[X] => (algebraMap k[X] (RatFunc k) p)⁻¹) '' S))

theorem X_mem (S : Set k[X]) : (RatFunc.X : RatFunc k) ∈ generated S :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem polynomial_mem (S : Set k[X]) (p : k[X]) :
    algebraMap k[X] (RatFunc k) p ∈ generated S := by
  rw [← RatFunc.aeval_X_left_eq_algebraMap]
  exact (Algebra.adjoin_le (Set.singleton_subset_iff.mpr (X_mem S)))
    (Polynomial.aeval_mem_adjoin_singleton k RatFunc.X)

theorem inverse_mem {S : Set k[X]} {p : k[X]} (hp : p ∈ S) :
    (algebraMap k[X] (RatFunc k) p)⁻¹ ∈ generated S :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, hp, rfl⟩)

theorem inverse_mem_of_closure {S : Set k[X]} {p : k[X]}
    (hp : p ∈ Submonoid.closure S) :
    (algebraMap k[X] (RatFunc k) p)⁻¹ ∈ generated S := by
  induction hp using Submonoid.closure_induction with
  | mem p hp => exact inverse_mem hp
  | one => simp
  | mul p q _ _ hp hq =>
    simpa only [map_mul, mul_inv_rev] using (generated S).mul_mem hq hp

theorem closure_le_nonZeroDivisors (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) :
    Submonoid.closure S ≤ nonZeroDivisors k[X] :=
  Submonoid.closure_le.mpr (fun p hp => mem_nonZeroDivisors_iff_ne_zero.mpr (hS p hp))

/-- The standard localization as a concrete subalgebra of the fraction field. -/
def localized (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) : Subalgebra k[X] (RatFunc k) :=
  Localization.subalgebra.ofField (RatFunc k) (Submonoid.closure S)
    (closure_le_nonZeroDivisors S hS)

/-- The concrete localization and the specified generated algebra have identical elements. -/
theorem localized_eq_generated (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) :
    (localized S hS).restrictScalars k = generated S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, s, hs, rfl⟩ := hx
    exact (generated S).mul_mem (polynomial_mem S a) (inverse_mem_of_closure hs)
  · apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (localized S hS).algebraMap_mem X
    · obtain ⟨p, hp, rfl⟩ := hx
      change ∃ a s : k[X], ∃ hs : s ∈ Submonoid.closure S,
        (algebraMap k[X] (RatFunc k) p)⁻¹ =
          algebraMap k[X] (RatFunc k) a * (algebraMap k[X] (RatFunc k) s)⁻¹
      exact ⟨1, p, Submonoid.subset_closure hp, by simp⟩

/-- Membership uses a finite product of selected denominators, even when `S` is infinite. -/
theorem mem_generated_iff (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) (x : RatFunc k) :
    x ∈ generated S ↔ ∃ a s : k[X], s ∈ Submonoid.closure S ∧
      x = algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) s := by
  rw [← localized_eq_generated S hS]
  change (∃ a s : k[X], ∃ hs : s ∈ Submonoid.closure S,
    x = algebraMap k[X] (RatFunc k) a * (algebraMap k[X] (RatFunc k) s)⁻¹) ↔ _
  simp only [div_eq_mul_inv, exists_prop]

/-- Restrict the canonical polynomial inclusion to the generated algebra. -/
def polynomialMap (S : Set k[X]) : k[X] →ₐ[k] generated S :=
  (IsScalarTower.toAlgHom k k[X] (RatFunc k)).codRestrict (generated S) (polynomial_mem S)

instance polynomialAlgebra (S : Set k[X]) : Algebra k[X] (generated S) :=
  (polynomialMap S).toRingHom.toAlgebra

@[simp] theorem coe_polynomial_algebraMap (S : Set k[X]) (p : k[X]) :
    ((algebraMap k[X] (generated S) p : generated S) : RatFunc k) =
      algebraMap k[X] (RatFunc k) p := rfl

instance scalarTower (S : Set k[X]) : IsScalarTower k k[X] (generated S) :=
  IsScalarTower.of_algebraMap_eq (fun r => ((polynomialMap S).commutes r).symm)

instance scalarTower_fractionField (S : Set k[X]) :
    IsScalarTower k[X] (generated S) (RatFunc k) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The comparison respects the actual polynomial map and ambient inclusion. -/
def generatedEquivLocalized (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) :
    generated S ≃ₐ[k[X]] localized S hS :=
  { (Subalgebra.equivOfEq _ _ (localized_eq_generated S hS).symm).toRingEquiv with
    commutes' _ := rfl }

@[simp] theorem generatedEquivLocalized_coe (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0)
    (x : generated S) : (generatedEquivLocalized S hS x : RatFunc k) = (x : RatFunc k) := rfl

instance localized_isLocalization (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) :
    IsLocalization (Submonoid.closure S) (localized S hS) :=
  inferInstanceAs (IsLocalization (Submonoid.closure S)
    (Localization.subalgebra.ofField (RatFunc k) (Submonoid.closure S)
      (closure_le_nonZeroDivisors S hS)))

/-- The localization property is proved, with nonzero selected polynomials explicit. -/
theorem isLocalization_generated (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) :
    IsLocalization (Submonoid.closure S) (generated S) :=
  IsLocalization.isLocalization_of_algEquiv (Submonoid.closure S)
    (generatedEquivLocalized S hS).symm

/-- The canonical equivalence from the abstract localization to the generated algebra. -/
def localizationEquiv (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) :
    Localization (Submonoid.closure S) ≃ₐ[k[X]] generated S := by
  let : IsLocalization (Submonoid.closure S) (generated S) := isLocalization_generated S hS
  exact IsLocalization.algEquiv (Submonoid.closure S) _ _

@[simp] theorem localizationEquiv_algebraMap
    (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) (p : k[X]) :
    (localizationEquiv S hS (algebraMap k[X] (Localization (Submonoid.closure S)) p) :
      RatFunc k) = algebraMap k[X] (RatFunc k) p := by
  rw [(localizationEquiv S hS).commutes]
  rfl

def localizationEquivOverBase (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0) :
    Localization (Submonoid.closure S) ≃ₐ[k] generated S :=
  (localizationEquiv S hS).restrictScalars k

theorem localizationEquiv_mk' (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0)
    (a : k[X]) (s : Submonoid.closure S) :
    (localizationEquiv S hS (IsLocalization.mk' (Localization (Submonoid.closure S)) a s) :
      RatFunc k) = algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) s := by
  let : IsLocalization (Submonoid.closure S) (generated S) := isLocalization_generated S hS
  change ((IsLocalization.algEquiv (Submonoid.closure S)
    (Localization (Submonoid.closure S)) (generated S)
      (IsLocalization.mk' (Localization (Submonoid.closure S)) a s) : generated S) : RatFunc k) = _
  rw [IsLocalization.algEquiv_mk']
  apply (eq_div_iff (RatFunc.algebraMap_ne_zero
    (mem_nonZeroDivisors_iff_ne_zero.mp (closure_le_nonZeroDivisors S hS s.property)))).mpr
  exact congrArg (fun z : generated S => (z : RatFunc k))
    (IsLocalization.mk'_spec (generated S) a s)

/-- Containing the polynomial ring already supplies the full rational fraction field. -/
instance fractionRing (S : Set k[X]) : IsFractionRing (generated S) (RatFunc k) :=
  IsFractionRing.of_field (generated S) (RatFunc k) (fun z =>
    ⟨algebraMap k[X] (generated S) z.num, algebraMap k[X] (generated S) z.denom,
      by
        change z = algebraMap k[X] (RatFunc k) z.num / algebraMap k[X] (RatFunc k) z.denom
        exact (RatFunc.num_div_denom z).symm⟩)

/-- Exact reduced-denominator characterization, not merely a bound on possible poles. -/
theorem mem_generated_iff_denom_dvd (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0)
    (x : RatFunc k) :
    x ∈ generated S ↔ ∃ s ∈ Submonoid.closure S, x.denom ∣ s := by
  rw [mem_generated_iff S hS]
  constructor
  · rintro ⟨a, s, hs, rfl⟩
    exact ⟨s, hs, RatFunc.denom_div_dvd a s⟩
  · rintro ⟨s, hs, hdvd⟩
    have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp (closure_le_nonZeroDivisors S hS hs)
    obtain ⟨a, ha⟩ := (RatFunc.denom_dvd hs0).mp hdvd
    exact ⟨a, s, hs, ha⟩

theorem exists_selected_factor_of_prime_dvd_closure
    (S : Set k[X]) {p q : k[X]} (hp : Prime p) (hq : q ∈ Submonoid.closure S)
    (hpq : p ∣ q) : ∃ s ∈ S, p ∣ s := by
  induction hq using Submonoid.closure_induction with
  | mem q hq => exact ⟨q, hq, hpq⟩
  | one => exact (hp.not_dvd_one hpq).elim
  | mul a b _ _ ha hb =>
    rcases hp.dvd_mul.mp hpq with h | h
    · exact ha h
    · exact hb h

/-- Every prime in a reduced denominator divides an actual selected polynomial. -/
theorem denom_prime_support (S : Set k[X]) (hS : ∀ p ∈ S, p ≠ 0)
    {x : RatFunc k} (hx : x ∈ generated S) {p : k[X]} (hp : Prime p)
    (hpx : p ∣ x.denom) : ∃ s ∈ S, p ∣ s := by
  obtain ⟨s, hs, hxs⟩ := (mem_generated_iff_denom_dvd S hS x).mp hx
  exact exists_selected_factor_of_prime_dvd_closure S hp hs (hpx.trans hxs)

/-- Inverses of factors of permitted denominators also belong to the generated algebra. -/
theorem inverse_factor_mem {S : Set k[X]} {p q : k[X]}
    (hq : q ∈ Submonoid.closure S) (hq0 : q ≠ 0) (hpq : p ∣ q) :
    (algebraMap k[X] (RatFunc k) p)⁻¹ ∈ generated S := by
  obtain ⟨r, rfl⟩ := hpq
  have hr : algebraMap k[X] (RatFunc k) r ≠ 0 :=
    RatFunc.algebraMap_ne_zero (right_ne_zero_of_mul hq0)
  have hmem := (generated S).mul_mem (polynomial_mem S r) (inverse_mem_of_closure hq)
  simpa only [map_mul, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hr, one_mul] using hmem

end UnconditionalCounterexample.PoleAlgebra
