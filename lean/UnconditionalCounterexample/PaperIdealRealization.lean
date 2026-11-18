import UnconditionalCounterexample.PaperIdealSingletons
import UnconditionalCounterexample.PrincipalProfileImage
import UnconditionalCounterexample.ProfileElimination
/-!
# Every restricted profile is realized by an actual invertible ideal

The vertical singletons are the actual two-generator ideals already constructed.
Nonzero principal fractional ideals have exactly their rational-function profiles,
so surviving horizontal polynomials and t provide the remaining lifts. Finite
profile elimination proves surjectivity of the actual ideal-profile map. Together
with its proved injectivity, this is the complete profile-group equivalence for
the same PaperConstruction.domain, without remaining constructor hypotheses.
-/

namespace UnconditionalCounterexample.PaperIdealProfiles

open WithZero CompleteProfiles PaperConstruction FractionalIdealProfiles PicardProfiles GuardSupport
open scoped nonZeroDivisors
local instance : IsFractionRing domain (RatFunc ℚ) := fractionRing

/-- An attained actual ideal profile identifies its canonical restricted tuple. -/
theorem profileMap_eq_of_hasProfile (I : Fractionalˣ) (f : Profile (Outside poles))
    (hI : HasProfile v I.val (coordinate f)) : profileMap (Additive.ofMul I) = f := by
  apply coordinate_injective
  rw [coordinate_profileMap]
  funext l
  exact (value_spec (v l) (integral l) I).unique (hI l)

/-- The actual ideal-profile image contains every primary singleton. -/
theorem primary_single_mem (j : ℕ) :
    primary (O := Outside poles) (Finsupp.single j 1) ∈ profileMap.range := by
  obtain ⟨I, hI⟩ := exists_vertical_singleton (.inl j)
  refine ⟨Additive.ofMul I, profileMap_eq_of_hasProfile I _ ?_⟩
  intro l
  have h := hI l
  cases l with
  | limit =>
    change HasValue I.val (v .limit) 0
    simpa [verticalLabel] using h
  | primary k =>
    rw [coordinate_primary_embed]
    simpa [verticalLabel, Finsupp.single_apply, eq_comm] using h
  | outside o =>
    change HasValue I.val (v (.outside o)) 0
    simpa [verticalLabel] using h

/-- The actual ideal-profile image contains every guard singleton. -/
theorem guard_single_mem (p : PrimeIndex) :
    ((0, 0, Finsupp.single (Sum.inl p) 1) : Profile (Outside poles)) ∈ profileMap.range := by
  obtain ⟨I, hI⟩ := exists_vertical_singleton (.inr p)
  refine ⟨Additive.ofMul I, profileMap_eq_of_hasProfile I _ ?_⟩
  intro l
  have h := hI l
  cases l with
  | limit => simpa [coordinate, verticalLabel] using h
  | primary k => simpa [coordinate, verticalLabel] using h
  | outside o => simpa [coordinate, verticalLabel, Finsupp.single_apply, eq_comm] using h

/-- The actual principal-ideal map agrees with the actual rational-function
profile hom used in the principal subgroup calculation. -/
theorem principal_profile_eq (u : (RatFunc ℚ)ˣ) :
    profileMap (Additive.ofMul (toPrincipalIdeal domain (RatFunc ℚ) u)) =
      PrincipalProfileImage.profile (Additive.ofMul u) := by
  apply coordinate_injective
  funext l
  rw [principal_profile, PrincipalProfileImage.coordinate_profile]
  rfl

/-- Every actual principal profile is in the actual invertible-ideal image. -/
theorem principals_le_range : PrincipalProfileImage.principals ≤ profileMap.range := by
  intro f hf
  obtain ⟨u, hu⟩ := (PrincipalProfileImage.mem_principals_iff f).mp hf
  exact ⟨Additive.ofMul (toPrincipalIdeal domain (RatFunc ℚ) u), (principal_profile_eq u).trans hu⟩

/-- Primary singleton ideals, actual horizontal principal lifts, guard
singletons and the actual profile of t span all restricted integer profiles. -/
theorem profileMap_range : profileMap.range = ⊤ := by
  apply ProfileElimination.eq_top_of_lifts profileMap.range primary_single_mem
  · intro p
    exact ⟨(0, 0, Finsupp.single (Sum.inl p) 1), guard_single_mem p, rfl⟩
  · intro h
    obtain ⟨x, hx, hcol⟩ := PrincipalProfileImage.horizontal_lift h
    exact ⟨x, principals_le_range hx, hcol⟩
  · exact principals_le_range PrincipalProfileImage.tProfile_mem

theorem profileMap_surjective : Function.Surjective profileMap := by
  intro f
  have hf : f ∈ profileMap.range := by rw [profileMap_range]; trivial
  exact hf

/-- The complete actual invertible fractional ideal group is exactly the
restricted profile group of the manuscript. -/
noncomputable def profileEquiv : Additive Fractionalˣ ≃+ Profile (Outside poles) :=
  AddEquiv.ofBijective profileMap ⟨profileMap_injective, profileMap_surjective⟩

@[simp] theorem profileEquiv_apply (I : Additive Fractionalˣ) : profileEquiv I = profileMap I := rfl

/-- Every restricted tuple is realized by an actual invertible fractional ideal. -/
theorem exists_invertible_profile (f : Profile (Outside poles)) :
    ∃ I : Fractionalˣ, HasProfile v I.val (coordinate f) := by
  obtain ⟨I, hI⟩ := profileMap_surjective f
  refine ⟨I.toMul, ?_⟩
  have h := profileHom_spec v integral I
  change HasProfile v I.toMul.val (profileFunction I) at h
  rw [← coordinate_profileMap I, hI] at h
  exact h

/-- Function-form realization uses exactly the eventual-primary and finite
outside conditions stated in the paper, including negative coordinates. -/
theorem exists_invertible_of_restricted (f : Label → ℤ) (hf : Restricted f) :
    ∃ I : Fractionalˣ, HasProfile v I.val f := by
  obtain ⟨I, hI⟩ := exists_invertible_profile (ofCoordinates f hf)
  exact ⟨I, by simpa only [coordinate_ofCoordinates] using hI⟩

end UnconditionalCounterexample.PaperIdealProfiles
