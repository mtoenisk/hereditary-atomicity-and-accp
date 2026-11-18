import HereditaryAtomicity.PrincipalComponents
import Factorization.Basic

/-!
# Ordinary atomicity in semilocal one-dimensional localizations

The principal active components show that every source atom either remains an
atom or becomes a unit. This statement concerns ordinary atomicity; hereditary
atomicity is not assumed to localize.
-/

open scoped nonZeroDivisors

noncomputable section
namespace HereditaryAtomicity

universe u v
variable {R : Type u} [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R]
  [Finite (MaximalSpectrum R)]
variable (M : Submonoid R) (T : Type v) [CommRing T] [IsDomain T]
  [Algebra R T] [IsLocalization M T]

omit [Finite (MaximalSpectrum R)] [IsDomain T] in
private theorem maximal_comap_of_mem_nonzero
    {a : R} (ha : a ≠ 0) (L : Ideal T) [L.IsMaximal]
    (haL : algebraMap R T a ∈ L) : (L.under R).IsMaximal := by
  apply Ideal.IsPrime.isMaximal_of_ne_bot (Ideal.IsPrime.comap (algebraMap R T))
  intro h
  have : a ∈ L.under R := haL
  exact ha (by simpa [h] using this)

omit [IsLocalization M T] [IsDomain T] in
/-- A nonunit localized divisor of a source atom has numerator in the atom's
unique maximal support. -/
theorem nonunit_localization_numerator_mem {a x : R} (ha : Irreducible a)
    (P : Ideal R) [P.IsMaximal] (haP : a ∈ P)
    {z : T} (hz : ¬ IsUnit z) (hza : z ∣ algebraMap R T a)
    (s : M) (hs : z * algebraMap R T s = algebraMap R T x) : x ∈ P := by
  obtain ⟨L, hL, hzL⟩ := exists_max_ideal_of_mem_nonunits hz
  let : L.IsMaximal := hL
  have haL : algebraMap R T a ∈ L := by
    obtain ⟨b, hb⟩ := hza
    rw [hb]
    exact L.mul_mem_right b hzL
  let : (L.under R).IsMaximal := maximal_comap_of_mem_nonzero (T := T) ha.ne_zero L haL
  have hP : L.under R = P := irreducible_unique_maximal ha _ _ haL haP
  rw [← hP]
  change algebraMap R T x ∈ L
  rw [← hs]
  exact L.mul_mem_right _ hzL

include M in
/-- Every source atom remains irreducible or becomes a unit in any domain
localization of a semilocal domain of dimension at most one. -/
theorem irreducible_or_isUnit_of_semilocal_localization {a : R} (ha : Irreducible a) :
    Irreducible (algebraMap R T a) ∨ IsUnit (algebraMap R T a) := by
  classical
  by_cases hau : IsUnit (algebraMap R T a)
  · exact Or.inr hau
  left
  refine ⟨hau, ?_⟩
  intro u v huv
  by_contra! hbad
  obtain ⟨hu, hv⟩ := hbad
  obtain ⟨L, hL, haL⟩ := exists_max_ideal_of_mem_nonunits hau
  let : L.IsMaximal := hL
  let P := L.under R
  let : P.IsMaximal := maximal_comap_of_mem_nonzero (T := T) ha.ne_zero L haL
  have haP : a ∈ P := haL
  have hM : M ≤ R⁰ := le_nonZeroDivisors_of_noZeroDivisors (by
    intro hzero
    have h := IsLocalization.map_units T (⟨0, hzero⟩ : M)
    simp at h)
  have hinj := IsLocalization.injective T hM
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj M u
  obtain ⟨⟨y, t⟩, ht⟩ := IsLocalization.surj M v
  have hxP : x ∈ P := nonunit_localization_numerator_mem M T ha P haP hu
    ⟨v, huv⟩ s hs
  have hyP : y ∈ P := nonunit_localization_numerator_mem M T ha P haP hv
    ⟨u, huv.trans (mul_comm _ _)⟩ t ht
  have hsP : (s : R) ∉ P := by
    intro hsP
    exact hL.ne_top (L.eq_top_of_isUnit_mem hsP (IsLocalization.map_units T s))
  have htP : (t : R) ∉ P := by
    intro htP
    exact hL.ne_top (L.eq_top_of_isUnit_mem htP (IsLocalization.map_units T t))
  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.ne_zero (hM s.property)
  have ht0 : (t : R) ≠ 0 := nonZeroDivisors.ne_zero (hM t.property)
  have heq : a * ((s : R) * t) = x * y := by
    apply hinj
    simp only [map_mul]
    rw [huv, ← hs, ← ht]
    ring
  have hxy0 : x * y ≠ 0 := heq ▸ mul_ne_zero ha.ne_zero (mul_ne_zero hs0 ht0)
  have hx0 : x ≠ 0 := left_ne_zero_of_mul hxy0
  have hy0 : y ≠ 0 := right_ne_zero_of_mul hxy0
  have hcomponents := congrArg (principalComponent P) heq
  rw [principalComponent_mul P ha.ne_zero (mul_ne_zero hs0 ht0),
    principalComponent_mul P hs0 ht0, principalComponent_eq_top_of_not_mem P hsP,
    principalComponent_eq_top_of_not_mem P htP, Ideal.top_mul, Ideal.mul_top,
    principalComponent_irreducible P ha haP, principalComponent_mul P hx0 hy0] at hcomponents
  let : (principalComponent P x).IsPrincipal := principalComponent_isPrincipal P hx0
  let : (principalComponent P y).IsPrincipal := principalComponent_isPrincipal P hy0
  let b := Submodule.IsPrincipal.generator (principalComponent P x)
  let c := Submodule.IsPrincipal.generator (principalComponent P y)
  have hb : Ideal.span {b} = principalComponent P x := Ideal.span_singleton_generator _
  have hc : Ideal.span {c} = principalComponent P y := Ideal.span_singleton_generator _
  have hbP : b ∈ P := by
    rw [← principalComponent_radical P hx0 hxP]
    exact Ideal.le_radical (hb ▸ Ideal.subset_span (Set.mem_singleton b))
  have hcP : c ∈ P := by
    rw [← principalComponent_radical P hy0 hyP]
    exact Ideal.le_radical (hc ▸ Ideal.subset_span (Set.mem_singleton c))
  have hbc : Associated a (b * c) := Ideal.span_singleton_eq_span_singleton.mp (by
    rw [hcomponents, ← hb, ← hc, Ideal.span_singleton_mul_span_singleton])
  have hbcirr : Irreducible (b * c) := hbc.irreducible ha
  rcases hbcirr.isUnit_or_isUnit rfl with hbunit | hcunit
  · exact ‹P.IsMaximal›.ne_top (P.eq_top_of_isUnit_mem hbP hbunit)
  · exact ‹P.IsMaximal›.ne_top (P.eq_top_of_isUnit_mem hcP hcunit)


include M in
/-- Ordinary atomicity localizes for semilocal domains of dimension at most one.
The target is any actual domain localization, including the fraction field. -/
theorem semilocal_isAtomicDomain_localization (hR : Factorization.IsAtomicDomain R) :
    Factorization.IsAtomicDomain T := by
  intro z hz0
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj M z
  have hsu : IsUnit (algebraMap R T s) := IsLocalization.map_units T s
  have hx0 : x ≠ 0 := by
    intro hx
    have hz : z * algebraMap R T s = 0 := by simpa [hx] using hs
    exact (mul_ne_zero hz0 hsu.ne_zero) hz
  obtain ⟨factors, hfactors, hassoc⟩ := hR x hx0
  have hmap : ∀ p ∈ factors, Factorization.HasAtomicFactorization (algebraMap R T p) := by
    intro p hp
    rcases irreducible_or_isUnit_of_semilocal_localization M T (hfactors p hp) with hirr | hu
    · exact Factorization.hasAtomicFactorization_of_irreducible hirr
    · exact Factorization.hasAtomicFactorization_of_isUnit hu
  have hprod : Factorization.HasAtomicFactorization (algebraMap R T factors.prod) := by
    clear hfactors hassoc
    induction factors using Multiset.induction_on with
    | empty => simpa using Factorization.hasAtomicFactorization_of_isUnit (isUnit_one : IsUnit (1 : T))
    | cons p factors ih =>
      rw [Multiset.prod_cons, map_mul]
      apply (hmap p (Multiset.mem_cons_self _ _)).mul
      apply ih
      intro q hq
      exact hmap q (Multiset.mem_cons_of_mem hq)
  have hx : Factorization.HasAtomicFactorization (algebraMap R T x) :=
    hprod.associated (hassoc.map (algebraMap R T).toMonoidHom)
  apply hx.associated
  rw [← hs]
  exact associated_mul_unit_left z _ hsu

/-- In particular, every maximal localization of a semilocal atomic domain of
dimension at most one is atomic. -/
theorem semilocal_isAtomicDomain_atPrime (hR : Factorization.IsAtomicDomain R)
    (P : Ideal R) [P.IsPrime] : Factorization.IsAtomicDomain (Localization.AtPrime P) :=
  semilocal_isAtomicDomain_localization P.primeCompl (Localization.AtPrime P) hR

end HereditaryAtomicity
