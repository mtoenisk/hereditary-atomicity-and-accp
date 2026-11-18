import UnconditionalCounterexample.SparseIdealSingletons
import UnconditionalCounterexample.SparsePrincipalProfiles
import UnconditionalCounterexample.ProfileElimination

/-!
# Every restricted sparse profile is realized by an invertible ideal

For a single realized sparse construction, actual primary and guard singleton
ideals and actual principal horizontal and coordinate profiles generate the
whole restricted group. The resulting equivalence classifies the actual
invertible fractional ideals and identifies their principal profile map.
-/

namespace UnconditionalCounterexample.SparseIdealProfiles

open WithZero SparseProfiles SparseProfileData FractionalIdealProfiles PicardProfiles GuardSupport
open scoped nonZeroDivisors
variable (A : Data)
local instance : IsFractionRing A.domain (RatFunc ℚ) := A.fractionRing

/-- An attained actual ideal profile identifies its canonical restricted tuple. -/
theorem profileMap_eq_of_hasProfile (I : (Fractional A)ˣ) (f : Profile (A.Outside))
    (hI : HasProfile (v A) I.val (coordinate f)) : profileMap A (Additive.ofMul I) = f := by
  apply coordinate_injective
  rw [coordinate_profileMap A]
  funext l
  exact (value_spec (v A l) (integral A l) I).unique (hI l)

/-- The actual ideal-profile image contains every primary singleton. -/
theorem primary_single_mem (j : ℕ) :
    primary (O := A.Outside) (Finsupp.single j 1) ∈ (profileMap A).range := by
  obtain ⟨I, hI⟩ := exists_vertical_singleton A (.inl j)
  refine ⟨Additive.ofMul I, profileMap_eq_of_hasProfile A I _ ?_⟩
  intro l
  have h := hI l
  cases l with
  | limit =>
    change HasValue I.val (v A .limit) 0
    simpa [verticalLabel] using h
  | primary k =>
    rw [coordinate_primary_embed]
    simpa [verticalLabel, Finsupp.single_apply, eq_comm] using h
  | outside o =>
    change HasValue I.val (v A (.outside o)) 0
    simpa [verticalLabel] using h

/-- The actual ideal-profile image contains every guard singleton. -/
theorem guard_single_mem (p : PrimeIndex) :
    ((0, 0, Finsupp.single (Sum.inl p) 1) : Profile (A.Outside)) ∈ (profileMap A).range := by
  obtain ⟨I, hI⟩ := exists_vertical_singleton A (.inr p)
  refine ⟨Additive.ofMul I, profileMap_eq_of_hasProfile A I _ ?_⟩
  intro l
  have h := hI l
  cases l with
  | limit => simpa [coordinate, verticalLabel] using h
  | primary k => simpa [coordinate, verticalLabel] using h
  | outside o => simpa [coordinate, verticalLabel, Finsupp.single_apply, eq_comm] using h

/-- The actual principal-ideal map agrees with the actual rational-function
profile hom used in the principal subgroup calculation. -/
theorem principal_profile_eq (u : (RatFunc ℚ)ˣ) :
    profileMap A (Additive.ofMul (toPrincipalIdeal A.domain (RatFunc ℚ) u)) =
      SparsePrincipalProfiles.profile A (Additive.ofMul u) := by
  apply coordinate_injective
  funext l
  rw [principal_profile A, SparsePrincipalProfiles.coordinate_profile A]
  rfl

/-- Every actual principal profile is in the actual invertible-ideal image. -/
theorem principals_le_range : SparsePrincipalProfiles.principals A ≤ (profileMap A).range := by
  intro f hf
  obtain ⟨u, hu⟩ := (SparsePrincipalProfiles.mem_principals_iff A f).mp hf
  exact ⟨Additive.ofMul (toPrincipalIdeal A.domain (RatFunc ℚ) u), (principal_profile_eq A u).trans hu⟩

/-- Primary singleton ideals, actual horizontal principal lifts, guard
singletons and the actual profile of t span all restricted integer profiles. -/
theorem profileMap_range : (profileMap A).range = ⊤ := by
  apply ProfileElimination.eq_top_of_lifts (profileMap A).range (primary_single_mem A)
  · intro p
    exact ⟨(0, 0, Finsupp.single (Sum.inl p) 1), guard_single_mem A p, rfl⟩
  · intro h
    obtain ⟨x, hx, hcol⟩ := SparsePrincipalProfiles.horizontal_lift A h
    exact ⟨x, principals_le_range A hx, hcol⟩
  · exact principals_le_range A (SparsePrincipalProfiles.tProfile_mem A)

theorem profileMap_surjective : Function.Surjective (profileMap A) := by
  intro f
  have hf : f ∈ (profileMap A).range := by rw [profileMap_range]; trivial
  exact hf

/-- The complete actual invertible fractional ideal group is exactly the
restricted profile group of the manuscript. -/
noncomputable def profileEquiv : Additive (Fractional A)ˣ ≃+ Profile (A.Outside) :=
  AddEquiv.ofBijective (profileMap A) ⟨profileMap_injective A, profileMap_surjective A⟩

@[simp] theorem profileEquiv_apply (I : Additive (Fractional A)ˣ) : profileEquiv A I = profileMap A I := rfl

/-- Every restricted tuple is realized by an actual invertible fractional ideal. -/
theorem exists_invertible_profile (f : Profile (A.Outside)) :
    ∃ I : (Fractional A)ˣ, HasProfile (v A) I.val (coordinate f) := by
  obtain ⟨I, hI⟩ := profileMap_surjective A f
  refine ⟨I.toMul, ?_⟩
  have h := profileHom_spec (v A) (integral A) I
  change HasProfile (v A) I.toMul.val (profileFunction A I) at h
  rw [← coordinate_profileMap A I, hI] at h
  exact h

/-- Function-form realization uses exactly the eventual-primary and finite
outside conditions stated in the paper, including negative coordinates. -/
theorem exists_invertible_of_restricted (f : A.Label → ℤ) (hf : Restricted f) :
    ∃ I : (Fractional A)ˣ, HasProfile (v A) I.val f := by
  obtain ⟨I, hI⟩ := exists_invertible_profile A (ofCoordinates f hf)
  exact ⟨I, by simpa only [coordinate_ofCoordinates] using hI⟩

end UnconditionalCounterexample.SparseIdealProfiles
