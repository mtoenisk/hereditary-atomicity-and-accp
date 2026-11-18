import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Noetherian.OfPrime
import Factorization.Definitions
import Mathlib.Tactic.Ring

/-!
# The exponent-two Prüfer comparison

The two conclusions of Proposition 8.1 are `atom_radical_or_square_maximal` and
`dedekind_of_atomic_prufer_picard_two`.

`IsPruferDomain` is the standard intrinsic property that every nonzero
finitely generated integral ideal is invertible as a fractional ideal in the
canonical fraction field. Mathlib has no existing Prüfer-domain predicate at
the pinned revision. `PicardExponentTwo` uses mathlib's actual Picard group;
principal squares are proved through its equivalence with the ideal class
group. The proof constructs all ideal factors and proves maximality, finite
generation of primes, and Noetherianity. No such conclusions are assumed.

Mathlib's `IsDedekindDomain` includes fields. Thus its final conclusion is
exactly the manuscript's "Dedekind domain or field" with the usual convention
that excludes fields from the first alternative.
-/

noncomputable section
open scoped nonZeroDivisors
namespace UnconditionalCounterexample.ExponentTwo

universe u
variable {R : Type u} [CommRing R] [IsDomain R]

abbrev FracIdeal (R : Type u) [CommRing R] :=
  FractionalIdeal R⁰ (FractionRing R)

/-- Every nonzero finitely generated integral ideal is invertible. -/
def IsPruferDomain (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ I : Ideal R, I.FG → I ≠ ⊥ → IsUnit (I : FracIdeal R)

/-- Exponent two is imposed on mathlib's actual Picard group. -/
def PicardExponentTwo (R : Type u) [CommRing R] : Prop :=
  ∀ x : CommRing.Pic R, x ^ 2 = 1

theorem principal_square (hPic : PicardExponentTwo R) (I : Ideal R)
    (hI : IsUnit (I : FracIdeal R)) : (I ^ 2).IsPrincipal := by
  have hc : ∀ x : ClassGroup R, x ^ 2 = 1 := by
    intro x
    apply (ClassGroup.equivPic R).injective
    simpa only [map_pow, map_one] using hPic (ClassGroup.equivPic R x)
  have hcl : ClassGroup.mk (FractionRing R) (hI.unit ^ 2) = 1 := by
    simpa only [map_pow] using hc (ClassGroup.mk (FractionRing R) hI.unit)
  have hsub := ClassGroup.mk_eq_one_iff.mp hcl
  change (((hI.unit ^ 2 : (FracIdeal R)ˣ) : FracIdeal R) :
    Submodule R (FractionRing R)).IsPrincipal at hsub
  rw [Units.val_pow_eq_pow_val, hI.unit_spec, ← FractionalIdeal.coeIdeal_pow,
    FractionalIdeal.coe_coeIdeal] at hsub
  exact (IsFractionRing.coeSubmodule_isPrincipal (R := R) (K := FractionRing R)
    (I := I ^ 2)).mp hsub

theorem integral_factor {I J : Ideal R} (hIJ : I ≤ J)
    (hJ : IsUnit (J : FracIdeal R)) :
    ∃ K : Ideal R, (K : FracIdeal R) = (I : FracIdeal R) * (J : FracIdeal R)⁻¹ ∧ J * K = I := by
  have hinv : (J : FracIdeal R) * (J : FracIdeal R)⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing R)).mpr hJ
  have hle : (I : FracIdeal R) * (J : FracIdeal R)⁻¹ ≤ 1 := by
    rw [← hinv]
    exact mul_le_mul_left ((FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing R)).mpr hIJ) _
  obtain ⟨K, hK⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  refine ⟨K, hK, FractionalIdeal.coeIdeal_injective (K := FractionRing R) ?_⟩
  change ((J * K : Ideal R) : FracIdeal R) = (I : FracIdeal R)
  rw [FractionalIdeal.coeIdeal_mul, hK, mul_left_comm, hinv, mul_one]

theorem principal_eq_of_atom {a : R} (ha : Irreducible a) {I : Ideal R}
    (hI : I.IsPrincipal) (hproper : I ≠ ⊤) (hcontain : Ideal.span {a} ≤ I) :
    I = Ideal.span {a} := by
  let := hI
  obtain ⟨b, rfl⟩ := Submodule.IsPrincipal.principal I
  have hb : ¬ IsUnit b := fun h => hproper (Ideal.span_singleton_eq_top.mpr h)
  obtain hunit | hassoc := ha.dvd_iff.mp (Ideal.span_singleton_le_span_singleton.mp hcontain)
  · exact (hb hunit).elim
  · exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm

theorem principal_product_not_atom {a : R} (ha : Irreducible a) {I J : Ideal R}
    (hI : I.IsPrincipal) (hJ : J.IsPrincipal) (hIp : I ≠ ⊤) (hJp : J ≠ ⊤) :
    I * J ≠ Ideal.span {a} := by
  let := hI
  let := hJ
  obtain ⟨b, rfl⟩ := Submodule.IsPrincipal.principal I
  obtain ⟨c, rfl⟩ := Submodule.IsPrincipal.principal J
  intro heq
  rw [Ideal.span_singleton_mul_span_singleton] at heq
  have hac : Irreducible (b * c) :=
    (Ideal.span_singleton_eq_span_singleton.mp heq).irreducible_iff.mpr ha
  obtain hb | hc := of_irreducible_mul hac
  · exact hIp (Ideal.span_singleton_eq_top.mpr hb)
  · exact hJp (Ideal.span_singleton_eq_top.mpr hc)

theorem principal_invertible {a : R} (ha : a ≠ 0) :
    IsUnit ((Ideal.span {a} : Ideal R) : FracIdeal R) :=
  (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing R)).mp
    (FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing R) ha)

omit [IsDomain R] in
theorem factor_invertible {I J K : Ideal R} (hI : IsUnit (I : FracIdeal R))
    (hJK : J * K = I) : IsUnit (K : FracIdeal R) := by
  apply isUnit_of_mul_isUnit_right (x := (J : FracIdeal R))
  rw [← FractionalIdeal.coeIdeal_mul, hJK]
  exact hI

omit [IsDomain R] in
theorem square_proper {I : Ideal R} (hI : I ≠ ⊤) : I ^ 2 ≠ ⊤ := by
  intro h
  exact hI (top_le_iff.mp (h ▸ Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0)))

omit [IsDomain R] in
theorem pair_square_le {a b : R} (hb : b ^ 2 ∈ Ideal.span {a}) :
    Ideal.span {a, b} ^ 2 ≤ Ideal.span {a} := by
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro r hr s hs
  obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.mp hr
  obtain ⟨z, w, rfl⟩ := Ideal.mem_span_pair.mp hs
  have heq : (x * a + y * b) * (z * a + w * b) =
      a * (x * z * a + x * w * b + y * z * b) + (y * w) * b ^ 2 := by ring
  rw [heq]
  exact (Ideal.span {a}).add_mem
    ((Ideal.span {a}).mul_mem_right _ (Ideal.subset_span (Set.mem_singleton a)))
    ((Ideal.span {a}).mul_mem_left _ hb)

theorem atom_nonradical_square (hPrufer : IsPruferDomain R)
    (hPic : PicardExponentTwo R) {a : R} (ha : Irreducible a)
    (hnonrad : ¬ (Ideal.span {a}).IsRadical) :
    ∃ K : Ideal R, IsUnit (K : FracIdeal R) ∧ K ≠ ⊤ ∧ Ideal.span {a} = K ^ 2 := by
  classical
  have hn : ¬ ∀ b : R, b ^ 2 ∈ Ideal.span {a} → b ∈ Ideal.span {a} :=
    fun h => hnonrad ((Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr h)
  push Not at hn
  obtain ⟨b, hb2, hb⟩ := hn
  let I : Ideal R := Ideal.span {a, b}
  have haI : a ∈ I := Ideal.subset_span (by simp)
  have hbI : b ∈ I := Ideal.subset_span (by simp)
  have hAI : Ideal.span {a} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr haI
  have hI0 : I ≠ ⊥ := fun h => ha.ne_zero (by simpa [h] using haI)
  have hI : IsUnit (I : FracIdeal R) := hPrufer I
    (Submodule.fg_span (Set.toFinite {a, b})) hI0
  obtain ⟨K, _, hIK⟩ := integral_factor hAI hI
  have hK : IsUnit (K : FracIdeal R) := factor_invertible (principal_invertible ha.ne_zero) hIK
  have hKp : K ≠ ⊤ := by
    intro h
    have hIA : I = Ideal.span {a} := by simpa [h] using hIK
    exact hb (hIA ▸ hbI)
  have hI2 : I ^ 2 ≤ Ideal.span {a} := pair_square_le hb2
  have hA2 : Ideal.span {a} ≤ K ^ 2 := by
    apply (Ideal.span_singleton_mul_right_mono ha.ne_zero).mp
    calc
      Ideal.span {a} * Ideal.span {a} = (I * K) ^ 2 := by rw [hIK, pow_two]
      _ = I ^ 2 * K ^ 2 := mul_pow I K 2
      _ ≤ Ideal.span {a} * K ^ 2 := mul_le_mul_left hI2 _
  exact ⟨K, hK, hKp, (principal_eq_of_atom ha (principal_square hPic K hK)
    (square_proper hKp) hA2).symm⟩

omit [IsDomain R] in
theorem invertible_fg {I : Ideal R} (hI : IsUnit (I : FracIdeal R)) : I.FG :=
  Ideal.fg_of_isUnit (S := R⁰) (IsFractionRing.injective R (FractionRing R)) I hI

theorem atom_square_maximal (hPrufer : IsPruferDomain R) (hPic : PicardExponentTwo R)
    {a : R} (ha : Irreducible a) {K : Ideal R} (hK : IsUnit (K : FracIdeal R))
    (hKp : K ≠ ⊤) (hAK : Ideal.span {a} = K ^ 2) : K.IsMaximal := by
  classical
  obtain ⟨N, hN, hKN⟩ := Ideal.exists_le_maximal K hKp
  suffices K = N by simpa only [this] using hN
  by_contra hne
  have hnle : ¬ N ≤ K := fun h => hne (le_antisymm hKN h)
  obtain ⟨z, hzN, hzK⟩ := SetLike.not_le_iff_exists.mp hnle
  let J : Ideal R := K ⊔ Ideal.span {z}
  have hKJ : K ≤ J := le_sup_left
  have hzJ : z ∈ J := (show Ideal.span {z} ≤ J from le_sup_right) (Ideal.subset_span (Set.mem_singleton z))
  have hJN : J ≤ N := sup_le hKN ((Ideal.span_singleton_le_iff_mem N).mpr hzN)
  have hJp : J ≠ ⊤ := fun h => hN.ne_top (top_le_iff.mp (h ▸ hJN))
  have hK0 : K ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp hK.ne_zero
  have hJ0 : J ≠ ⊥ := fun h => hK0 (bot_unique (h ▸ hKJ))
  have hJ : IsUnit (J : FracIdeal R) := hPrufer J
    (Submodule.FG.sup (invertible_fg hK) (Submodule.fg_span_singleton z)) hJ0
  obtain ⟨L, _, hJL⟩ := integral_factor hKJ hJ
  have hL : IsUnit (L : FracIdeal R) := factor_invertible hK hJL
  have hLp : L ≠ ⊤ := by
    intro h
    have hJK : J = K := by simpa [h] using hJL
    exact hzK (hJK ▸ hzJ)
  apply principal_product_not_atom ha (principal_square hPic J hJ)
    (principal_square hPic L hL) (square_proper hJp) (square_proper hLp)
  rw [← mul_pow, hJL, hAK]

/-- The first assertion of manuscript Proposition exponent-two, with the
standard intrinsic Prüfer property and mathlib's actual Picard group. -/
theorem atom_radical_or_square_maximal (hPrufer : IsPruferDomain R)
    (hPic : PicardExponentTwo R) {a : R} (ha : Irreducible a) :
    (Ideal.span {a}).IsRadical ∨ ∃ K : Ideal R,
      K.IsMaximal ∧ IsUnit (K : FracIdeal R) ∧ Ideal.span {a} = K ^ 2 := by
  by_cases hrad : (Ideal.span {a}).IsRadical
  · exact Or.inl hrad
  · obtain ⟨K, hK, hKp, hAK⟩ := atom_nonradical_square hPrufer hPic ha hrad
    exact Or.inr ⟨K, atom_square_maximal hPrufer hPic ha hK hKp hAK, hK, hAK⟩

/-- Noetherian Prüfer domains are Dedekind in mathlib's convention, which
includes fields. Every fractional ideal is explicitly cleared to an integral ideal. -/
theorem dedekind_of_noetherian_prufer [IsNoetherianRing R]
    (hPrufer : IsPruferDomain R) : IsDedekindDomain R := by
  apply (isDedekindDomain_iff_mul_inv_cancel (K := FractionRing R)).mpr
  intro I hI
  apply (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing R)).mpr
  obtain ⟨a, J, ha, hrepr⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply hI
    simp [hrepr, h]
  have hJ : IsUnit (J : FracIdeal R) := hPrufer J (Ideal.fg_of_isNoetherianRing J) hJ0
  have hamap : algebraMap R (FractionRing R) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr ha
  have hspan : IsUnit (FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) a)⁻¹) :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing R)).mp
      (FractionalIdeal.spanSingleton_mul_inv (FractionRing R) (inv_ne_zero hamap))
  rw [hrepr]
  exact hspan.mul hJ

theorem exists_irreducible_mem_and_dvd
    (hR : Factorization.IsAtomicDomain R) (P : Ideal R) (hP : P.IsPrime)
    (x : R) (hx : x ≠ 0) (hxP : x ∈ P) :
    ∃ a : R, Irreducible a ∧ a ∈ P ∧ a ∣ x := by
  obtain ⟨f, hf, hassoc⟩ := hR x hx
  have hprod : f.prod ∈ P := P.mem_of_dvd hassoc.symm.dvd hxP
  obtain ⟨a, haf, haP⟩ := (hP.multiset_prod_mem_iff_exists_mem f).mp hprod
  exact ⟨a, hf a haf, haP, (Multiset.dvd_prod haf).trans hassoc.dvd⟩

theorem prime_fg_of_atomic_atom_dichotomy
    (hR : Factorization.IsAtomicDomain R)
    (hatom : ∀ a : R, Irreducible a → (Ideal.span {a}).IsRadical ∨
      ∃ M : Ideal R, M.IsMaximal ∧ M.FG ∧ Ideal.span {a} = M ^ 2)
    (hsquare : ∀ I : Ideal R, I.FG → I ≠ ⊥ → (I ^ 2).IsPrincipal)
    (P : Ideal R) (hP : P.IsPrime) : P.FG := by
  classical
  by_contra hnotfg
  have : P.IsPrime := hP
  have hP0 : P ≠ ⊥ := by
    intro h
    exact hnotfg (h ▸ Submodule.fg_bot)
  have hradical (a : R) (ha : Irreducible a) (haP : a ∈ P) :
      (Ideal.span {a}).IsRadical := by
    rcases hatom a ha with hrad | ⟨M, hM, hMfg, haM⟩
    · exact hrad
    · have hM2 : M ^ 2 ≤ P := by
        rw [← haM]
        exact (Ideal.span_singleton_le_iff_mem P).mpr haP
      have hMP : M ≤ P := Ideal.IsPrime.le_of_pow_le hM2
      have hMeq : M = P := hM.eq_of_le hP.ne_top hMP
      exact False.elim (hnotfg (hMeq ▸ hMfg))
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨a, ha, haP, _⟩ := exists_irreducible_mem_and_dvd hR P hP x hx0 hxP
  have hPa : ¬ P ≤ Ideal.span {a} := by
    intro h
    have heq : P = Ideal.span {a} :=
      le_antisymm h ((Ideal.span_singleton_le_iff_mem P).mpr haP)
    exact hnotfg (heq ▸ Submodule.fg_span_singleton a)
  obtain ⟨b, hbP, hba⟩ := SetLike.not_le_iff_exists.mp hPa
  let J : Ideal R := Ideal.span {a} ⊔ Ideal.span {b}
  have haJ : a ∈ J := (show Ideal.span {a} ≤ J from le_sup_left)
    (Ideal.subset_span (by simp))
  have hbJ : b ∈ J := (show Ideal.span {b} ≤ J from le_sup_right)
    (Ideal.subset_span (by simp))
  have hJP : J ≤ P := sup_le ((Ideal.span_singleton_le_iff_mem P).mpr haP)
    ((Ideal.span_singleton_le_iff_mem P).mpr hbP)
  have hJfg : J.FG := (Submodule.fg_span_singleton a).sup (Submodule.fg_span_singleton b)
  have hJ0 : J ≠ ⊥ := by
    intro h
    exact ha.ne_zero (by simpa only [h, Ideal.mem_bot] using haJ)
  have : (J ^ 2).IsPrincipal := hsquare J hJfg hJ0
  obtain ⟨c, hc⟩ := Submodule.IsPrincipal.principal (J ^ 2)
  have hc0 : c ≠ 0 := by
    intro h
    have hJ2 : J ^ 2 = ⊥ := by simpa only [h, Ideal.span_singleton_zero] using hc
    exact hJ0 ((Ideal.pow_eq_bot (by decide : 2 ≠ 0)).mp hJ2)
  have hcP : c ∈ P := by
    apply hJP
    apply Ideal.pow_le_self (by decide : 2 ≠ 0)
    rw [hc]
    exact Ideal.subset_span (by simp)
  obtain ⟨y, hy, hyP, hyc⟩ := exists_irreducible_mem_and_dvd hR P hP c hc0 hcP
  have hJ2y : J ^ 2 ≤ Ideal.span {y} := by
    rw [hc]
    exact Ideal.span_singleton_le_span_singleton.mpr hyc
  have hJy : J ≤ Ideal.span {y} := by
    intro z hz
    exact hradical y hy hyP ⟨2, hJ2y (Ideal.pow_mem_pow hz 2)⟩
  have hya : y ∣ a := Ideal.mem_span_singleton.mp (hJy haJ)
  rcases ha.dvd_iff.mp hya with hyunit | hassoc
  · exact hy.not_isUnit hyunit
  · have hspan : Ideal.span {a} = Ideal.span {y} :=
      Ideal.span_singleton_eq_span_singleton.mpr hassoc
    apply hba
    rw [hspan]
    exact hJy hbJ

theorem noetherian_of_atomic_atom_dichotomy
    (hR : Factorization.IsAtomicDomain R)
    (hatom : ∀ a : R, Irreducible a → (Ideal.span {a}).IsRadical ∨
      ∃ M : Ideal R, M.IsMaximal ∧ M.FG ∧ Ideal.span {a} = M ^ 2)
    (hsquare : ∀ I : Ideal R, I.FG → I ≠ ⊥ → (I ^ 2).IsPrincipal) :
    IsNoetherianRing R :=
  IsNoetherianRing.of_prime (prime_fg_of_atomic_atom_dichotomy hR hatom hsquare)


/-- The Noetherian conclusion in manuscript Proposition exponent-two. -/
theorem noetherian_of_atomic_prufer_picard_two (hPrufer : IsPruferDomain R)
    (hPic : PicardExponentTwo R) (hAtomic : Factorization.IsAtomicDomain R) :
    IsNoetherianRing R := by
  apply noetherian_of_atomic_atom_dichotomy hAtomic
  · intro a ha
    rcases atom_radical_or_square_maximal hPrufer hPic ha with hrad | ⟨M, hM, hunit, heq⟩
    · exact Or.inl hrad
    · exact Or.inr ⟨M, hM, invertible_fg hunit, heq⟩
  · intro I hfg hne
    exact principal_square hPic I (hPrufer I hfg hne)

/-- The second assertion of manuscript Proposition exponent-two. Mathlib's
Dedekind definition includes fields, so no extra non-field hypothesis is needed. -/
theorem dedekind_of_atomic_prufer_picard_two (hPrufer : IsPruferDomain R)
    (hPic : PicardExponentTwo R) (hAtomic : Factorization.IsAtomicDomain R) :
    IsDedekindDomain R := by
  let := noetherian_of_atomic_prufer_picard_two hPrufer hPic hAtomic
  exact dedekind_of_noetherian_prufer hPrufer

end UnconditionalCounterexample.ExponentTwo
