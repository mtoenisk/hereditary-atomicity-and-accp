import UnconditionalCounterexample.Variations.MultiDomainLowProfiles
import UnconditionalCounterexample.EscapingProfiles

/-!
# Bounded listed words from a non-BF multivariate subring

The intrinsic unbounded factorization lengths in the source subring produce
unsigned listed words at arbitrarily late stages of the multivariate
schedule, with one bound on every word exponent. This also applies to a
subring of the point pullback via its injection into the ordinary domain.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain.ProfileChoices

open DiscreteOrders PrincipalProfiles StageExponents RawWords
variable {r : ℕ} {A : Data (r+1)} (C : ProfileChoices A)

theorem infinitely_many_bounded_words {T : Type*} [CommRing T] [IsDomain T]
    (f : T →+* ordinary A) (hf : Function.Injective f) (hT : ¬ Factorization.IsBFDomain T) :
    ∃ k : ℕ, 0 < k ∧ {n : ℕ | ∃ w : StageWord n (n+1), w.latestExponent ≤ 2*k ∧
      (∀ j, |w.oldExponent j| ≤ (2*k : ℕ)) ∧ ∃ y : T, (f y : FunctionField (r+1)) =
        C.generator n ^ w.latestExponent * ∏ j ∈ Finset.range n, C.generator j ^ w.oldExponent j}.Infinite := by
  classical
  let e := RingEquiv.ofBijective f.rangeRestrict ⟨fun _ _ h ↦ hf (congrArg f.range.subtype h), f.rangeRestrict_surjective⟩
  have hbad : ¬ Factorization.IsBFDomain f.range := by
    intro h
    apply hT
    intro x hx
    apply Factorization.hasBoundedFactorizations_of_unitReflectingMap e.toMonoidHom
      (fun y hy ↦ (MulEquiv.isUnit_map e.toMulEquiv).mp hy) (h (e x) ((map_ne_zero_iff _ e.injective).mpr hx))
  unfold Factorization.IsBFDomain at hbad
  push Not at hbad
  obtain ⟨x, hx, hlen⟩ := hbad
  obtain ⟨k, hk, hesc⟩ := C.profile.exists_escaping_primary_divisors f.range
    (UnitSigns.subring_reflects_units C.signs _) hx hlen
  refine ⟨k, hk, Set.infinite_of_forall_exists_gt ?_⟩
  intro N
  obtain ⟨z, hz⟩ := hesc (2 * max N (2*k) + 2)
  have hzR : (z : ordinary A) ≠ 0 := fun h ↦ hz.ne_zero (Subtype.ext h)
  have hzK : ((z : ordinary A) : FunctionField (r+1)) ≠ 0 := fun h ↦ hzR (Subtype.ext h)
  let g (j : ℕ) : ℤ := C.profile.value (.primary j) z
  have hcz (p) := C.profile_cast p hzR
  obtain ⟨d, hd, hrep⟩ := C.signed_word hzK
    (by rw [← hcz .limit, hz.limit_zero]; rfl)
    (fun i ↦ by rw [← hcz (.outside i), hz.outside_zero]; rfl)
  have hg : (fun j ↦ order (A.primary j) ((z : ordinary A) : FunctionField (r+1))) = g :=
    funext fun j ↦ (hcz (.primary j)).symm
  rw [hg] at hrep
  obtain ⟨j, hj⟩ := hz.nonempty_support
  obtain ⟨n, hn, w, hw, hl, ht, hb, hprev⟩ := exists_bounded_listed_word_beyond d g hrep k N
    (fun j ↦ ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (hz.primary_bound j)⟩)
    ⟨j, by dsimp [g]; exact_mod_cast hj.ne'⟩ (fun j h ↦ by simp [g, hz.prefix_zero j h])
  refine ⟨n, ⟨w, hb, hprev, ?_⟩, hn⟩
  obtain ⟨y, hy⟩ := z.property
  have hword := prod_eq_listed_word C.generator d n (n+1) w hw hl ht
  cases hd with
  | inl he => exact ⟨y, (congrArg (ordinary A).subtype hy).trans (he.trans hword)⟩
  | inr he =>
    refine ⟨-y, ?_⟩
    rw [map_neg, Subring.coe_neg, hy, he, neg_neg]
    exact hword

end UnconditionalCounterexample.Variations.MultiDomain.ProfileChoices
