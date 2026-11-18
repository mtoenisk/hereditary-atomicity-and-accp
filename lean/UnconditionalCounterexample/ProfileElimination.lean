import UnconditionalCounterexample.PrimaryProfileQuotient

/-!
# Clearing horizontal, guard and limit entries of ideal profiles

A surviving horizontal polynomial can have extra guard and primary values.
Clear the horizontal entries first, use rational primes to remove the guard
entries, and finally subtract the appropriate multiple of the profile of t.
The remaining finite primary tuple represents the original ideal class.
-/

noncomputable section
namespace UnconditionalCounterexample.ProfileElimination

open PicardProfiles

private theorem lift_finite {A I : Type*} [AddCommGroup A] (P : AddSubgroup A)
    (π : A →+ (I →₀ ℤ)) (h : ∀ i, ∃ x ∈ P, π x = Finsupp.single i 1)
    (v : I →₀ ℤ) : ∃ x ∈ P, π x = v := by
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0, P.zero_mem, map_zero _⟩
  | add _ _ hv hw =>
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨y, hy, rfl⟩ := hw
    exact ⟨x+y, P.add_mem hx hy, map_add _ _ _⟩
  | single i k =>
    obtain ⟨x, hx, he⟩ := h i
    refine ⟨k • x, P.zsmul_mem hx k, ?_⟩
    rw [map_zsmul, he]
    classical
    ext j
    by_cases hj : i = j <;> simp [hj]

private def project {G H I : Type*} (l : I → G ⊕ H) (hl : Function.Injective l) :
    Profile (G ⊕ H) →+ (I →₀ ℤ) :=
  (Finsupp.comapDomain.addMonoidHom hl).comp ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))

/-- The order of elimination allows arbitrary guard values on horizontal
lifts and arbitrary primary values on all three types of principal lifts. -/
theorem clear_to_primary {G H : Type*} (P : AddSubgroup (Profile (G ⊕ H)))
    (hguard : ∀ g : G, ∃ x ∈ P, x.2.2 = Finsupp.single (.inl g) 1)
    (hhoriz : ∀ h : H, ∃ x ∈ P, ∀ k : H, x.2.2 (.inr k) = Finsupp.single h 1 k)
    (ht : tProfile ∈ P) (x : Profile (G ⊕ H)) :
    ∃ a : ℕ →₀ ℤ, x - primary a ∈ P := by
  classical
  let hproj := project (Sum.inr : H → G ⊕ H) Sum.inr_injective
  let gproj := project (Sum.inl : G → G ⊕ H) Sum.inl_injective
  obtain ⟨y, hy, hey⟩ := lift_finite P hproj (fun h => by
    obtain ⟨z, hz, he⟩ := hhoriz h
    exact ⟨z, hz, Finsupp.ext he⟩) (hproj x)
  let P₀ := P ⊓ hproj.ker
  have hg (g : G) : ∃ z ∈ P₀, gproj z = Finsupp.single g 1 := by
    obtain ⟨z, hz, he⟩ := hguard g
    refine ⟨z, ⟨hz, ?_⟩, ?_⟩
    · apply Finsupp.ext
      intro k
      change z.2.2 (.inr k) = 0
      simp [he]
    · apply Finsupp.ext
      intro k
      change z.2.2 (.inl k) = _
      simp [he, Finsupp.single_apply]
  obtain ⟨z, hz, hez⟩ := lift_finite P₀ gproj hg (gproj (x - y))
  let r := x - y - z
  have hr : r.2.2 = 0 := by
    ext o
    cases o with
    | inl g =>
      have h := DFunLike.congr_fun hez g
      change z.2.2 (.inl g) = x.2.2 (.inl g) - y.2.2 (.inl g) at h
      change x.2.2 (.inl g) - y.2.2 (.inl g) - z.2.2 (.inl g) = 0
      exact sub_eq_zero.mpr h.symm
    | inr h =>
      have h1 := DFunLike.congr_fun hey h
      have h2 := DFunLike.congr_fun (show hproj z = 0 from hz.2) h
      change y.2.2 (.inr h) = x.2.2 (.inr h) at h1
      change z.2.2 (.inr h) = 0 at h2
      change x.2.2 (.inr h) - y.2.2 (.inr h) - z.2.2 (.inr h) = 0
      rw [h1, h2, sub_self, sub_zero]
  let t := r.1 • (tProfile : Profile (G ⊕ H))
  have he : r - t = primary ((r - t).2.1) := by
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · change r.1 - r.1 • (1 : ℤ) = 0
      simp
    · change r.2.2 - r.1 • (0 : G ⊕ H →₀ ℤ) = 0
      simp [hr]
  refine ⟨(r - t).2.1, ?_⟩
  rw [← he, show x - (r - t) = y + z + t by dsimp only [r]; abel]
  exact P.add_mem (P.add_mem hy hz.1) (P.zsmul_mem ht _)

/-- The pure primary singleton profiles span all finite primary tuples. -/
theorem mem_primary_of_singles {O : Type*} (P : AddSubgroup (Profile O))
    (hs : ∀ n : ℕ, primary (Finsupp.single n 1) ∈ P) (a : ℕ →₀ ℤ) : primary a ∈ P := by
  let Q := P.comap primary
  obtain ⟨v, hv, rfl⟩ := lift_finite Q (AddMonoidHom.id _) (fun n => ⟨_, hs n, rfl⟩) a
  exact hv

/-- The actual ideal profile image is all restricted profiles once it contains
the primary singletons, the horizontal and guard lifts, and the profile of t. -/
theorem eq_top_of_lifts {G H : Type*} (P : AddSubgroup (Profile (G ⊕ H)))
    (hs : ∀ n : ℕ, primary (Finsupp.single n 1) ∈ P)
    (hguard : ∀ g : G, ∃ x ∈ P, x.2.2 = Finsupp.single (.inl g) 1)
    (hhoriz : ∀ h : H, ∃ x ∈ P, ∀ k : H, x.2.2 (.inr k) = Finsupp.single h 1 k)
    (ht : tProfile ∈ P) : P = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha⟩ := clear_to_primary P hguard hhoriz ht x
  exact sub_add_cancel x (primary a) ▸ P.add_mem ha (mem_primary_of_singles P hs a)

end UnconditionalCounterexample.ProfileElimination
