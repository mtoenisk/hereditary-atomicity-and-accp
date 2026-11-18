import Factorization.Basic
import Factorization.Hereditary
import Factorization.Bounds
import Mathlib.Data.Multiset.Filter

/-!
# Descent with bounded ambient-unit factors

The source factors are nonunits of the source monoid. Some may become units
under a homomorphism. A bound on their number combines with a target bound to
control all source factors. Counts retain multiplicities.
-/

namespace Factorization

universe u v

section Monoids

variable {R : Type u} {S : Type v} [CommMonoid R] [CommMonoid S]

/-- Number, with multiplicity, of factors whose images are target units. -/
noncomputable def ambientUnitFactorCount (f : R →* S) (t : Multiset R) : ℕ := by
  classical
  exact (t.filter (fun a => IsUnit (f a))).card

/-- Every source-nonunit factorization of `x` has uniformly boundedly many
factors which become units under `f`. The bound depends on `f` and `x`. -/
def HasBoundedAmbientUnitFactors (f : R →* S) (x : R) : Prop :=
  ∃ bound : ℕ, ∀ t : Multiset R,
    (∀ a ∈ t, ¬ IsUnit a) → Associated t.prod x →
      ambientUnitFactorCount f t ≤ bound

/-- Associated source elements have the same ambient-unit factor bounds. -/
theorem HasBoundedAmbientUnitFactors.associated {f : R →* S} {x y : R}
    (hx : HasBoundedAmbientUnitFactors f x) (hxy : Associated x y) :
    HasBoundedAmbientUnitFactors f y := by
  obtain ⟨N, hN⟩ := hx
  exact ⟨N, fun t ht hty => hN t ht (hty.trans hxy.symm)⟩

/-- Deleting factors which map to units preserves the target product up to
association. No cancellation or injectivity is required. -/
theorem associated_prod_map_filter_nonunits (f : R →* S) (t : Multiset R)
    [DecidablePred (fun a => ¬ IsUnit (f a))] :
    Associated ((t.filter (fun a => ¬ IsUnit (f a))).map f).prod (f t.prod) := by
  classical
  induction t using Multiset.induction_on with
  | empty => simp
  | @cons a t ih =>
    by_cases ha : IsUnit (f a)
    · simpa [ha] using ih.trans (associated_unit_mul_left (f t.prod) (f a) ha).symm
    · simpa [ha] using ih.mul_left (f a)

/-- The target's nonunit bound plus the source's ambient-unit count bounds the
length of every source-nonunit factorization. -/
theorem factorization_card_le_of_ambientUnitBounds (f : R →* S) {x : R}
    (N M : ℕ)
    (hN : ∀ s : Multiset S, (∀ b ∈ s, ¬ IsUnit b) →
      Associated s.prod (f x) → s.card ≤ N)
    (hM : ∀ t : Multiset R, (∀ a ∈ t, ¬ IsUnit a) →
      Associated t.prod x → ambientUnitFactorCount f t ≤ M)
    (t : Multiset R) (ht : ∀ a ∈ t, ¬ IsUnit a) (htx : Associated t.prod x) :
    t.card ≤ N + M := by
  classical
  let s := (t.filter (fun a => ¬ IsUnit (f a))).map f
  have hs : ∀ b ∈ s, ¬ IsUnit b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    exact (Multiset.mem_filter.mp ha).2
  have hsx : Associated s.prod (f x) := by
    simpa only [s] using (associated_prod_map_filter_nonunits f t).trans (htx.map f)
  have hnon := hN s hs hsx
  have hunit := hM t ht htx
  have hcard := congrArg Multiset.card
    (Multiset.filter_add_not (p := fun a => IsUnit (f a)) t)
  simp only [Multiset.card_add] at hcard
  simp only [s, Multiset.card_map] at hnon
  unfold ambientUnitFactorCount at hunit
  omega

/-- Bounded nonunit factorizations descend if the number of factors which
become target units is also bounded. This elementwise result needs no
injectivity or reflection of target units. -/
theorem hasBoundedFactorizations_of_boundedAmbientUnitFactors
    (f : R →* S) {x : R} (hbudget : HasBoundedAmbientUnitFactors f x)
    (htarget : HasBoundedFactorizations (f x)) : HasBoundedFactorizations x := by
  obtain ⟨M, hM⟩ := hbudget
  obtain ⟨N, hN⟩ := htarget
  exact ⟨N + M, factorization_card_le_of_ambientUnitBounds f N M hN hM⟩

/-- A unit-reflecting map has ambient-unit factor budget zero. -/
theorem hasBoundedAmbientUnitFactors_of_unitReflectingMap
    (f : R →* S) (hf : ∀ a : R, IsUnit (f a) → IsUnit a) (x : R) :
    HasBoundedAmbientUnitFactors f x := by
  classical
  refine ⟨0, fun t ht _ => ?_⟩
  have hempty : t.filter (fun a => IsUnit (f a)) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro a ha hu
    exact ht a ha (hf a hu)
  simp only [ambientUnitFactorCount, hempty, Multiset.card_zero, le_refl]

end Monoids

section Detectors

variable {R : Type u} {S : Type v} [CommMonoidWithZero R] [CommMonoid S]

/-- A finite natural-valued detector family supplies an actual ambient-unit
factor budget. Only source nonunit divisors of the fixed product which become
target units need to be detected. -/
theorem hasBoundedAmbientUnitFactors_of_finite_nat_detectors
    (f : R →* S) {ι : Type*} (indices : Finset ι) (weight : ι → R → ℕ)
    (hunit : ∀ i ∈ indices, ∀ a : R, IsUnit a → weight i a = 0)
    (hmul : ∀ i ∈ indices, ∀ a b : R, a ≠ 0 → b ≠ 0 →
      weight i (a * b) = weight i a + weight i b)
    {x : R} (hx : x ≠ 0)
    (hdetect : ∀ a : R, a ≠ 0 → a ∣ x → ¬ IsUnit a → IsUnit (f a) →
      ∃ i ∈ indices, 0 < weight i a) : HasBoundedAmbientUnitFactors f x := by
  classical
  refine ⟨∑ i ∈ indices, weight i x, fun factors hn hfac => ?_⟩
  apply filter_card_le_sum_nat_of_finite_detectors indices weight hunit hmul
    hx factors hfac (fun a => IsUnit (f a))
  intro a ha hu
  have hdvd : a ∣ x := (Multiset.dvd_prod ha).trans hfac.dvd
  exact hdetect a (ne_zero_of_dvd_ne_zero hx hdvd) hdvd (hn a ha) hu

end Detectors

section Domains

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S]

/-- BF descends along an injective domain map with bounded ambient-unit factors
at every nonzero source element. -/
theorem isBFDomain_of_boundedAmbientUnitFactors
    (f : R →+* S) (hf : Function.Injective f)
    (hbudget : ∀ x : R, x ≠ 0 → HasBoundedAmbientUnitFactors f.toMonoidHom x)
    (hS : IsBFDomain S) : IsBFDomain R := by
  intro x hx
  apply hasBoundedFactorizations_of_boundedAmbientUnitFactors f.toMonoidHom (hbudget x hx)
  apply hS (f x)
  exact fun hzero => hx (hf (hzero.trans f.map_zero.symm))

/-- Uniform availability of ambient-unit budgets in every actual subring turns
ambient BF into hereditary BF. Each budget may depend on the subring and element. -/
theorem isHereditarilyBF_of_boundedAmbientUnitFactors (hR : IsBFDomain R)
    (hbudget : ∀ A : Subring R, ∀ x : A, x ≠ 0 →
      HasBoundedAmbientUnitFactors A.subtype.toMonoidHom x) : IsHereditarilyBF R := by
  intro A
  exact isBFDomain_of_boundedAmbientUnitFactors A.subtype Subtype.val_injective
    (hbudget A) hR

end Domains

end Factorization
