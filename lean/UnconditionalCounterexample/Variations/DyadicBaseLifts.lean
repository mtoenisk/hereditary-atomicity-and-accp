import UnconditionalCounterexample.Variations.DyadicIntersections

/-!
# Clearing horizontals and guards before dyadic column elimination

Each retained horizontal polynomial contributes a singleton horizontal value
and may have guard values. Correct those guard values afterwards using scalar
prime powers. A prime must leave the already assigned horizontal data unchanged.
-/

noncomputable section
namespace UnconditionalCounterexample.DyadicDeviations

open DyadicProfiles (Site)
open DiscreteOrders WithZero

variable {J : Bool → Type*} {G H F : Type*}

/-- The horizontal indices include the two distinguished centres. -/
abbrev HorizontalIndex (H : Type*) := Bool ⊕ H

/-- There is exactly one index for each prescribed guard. -/
abbrev GuardIndex (J : Bool → Type*) (G : Type*) :=
  (Bool × ℕ) ⊕ ((Bool × ℕ) ⊕ ((Σ k, J k) ⊕ G))

def horizontalSite : HorizontalIndex H → Site (Supplement J G H)
  | .inl k => .centre k
  | .inr h => .other (.horizontal h)

def guardSite : GuardIndex J G → Site (Supplement J G H)
  | .inl (k,n) => .other (.plusGuard k n)
  | .inr (.inl (k,n)) => .other (.minusGuard k n)
  | .inr (.inr (.inl ⟨k,j⟩)) => .other (.auxiliaryGuard k j)
  | .inr (.inr (.inr g)) => .other (.loneGuard g)

def Profile.horizontalPart (p : Profile J G H) : HorizontalIndex H →₀ ℤ :=
  (Finsupp.equivFunOnFinite.symm p.height).sumElim p.horizontal

def Profile.guardPart (p : Profile J G H) : GuardIndex J G →₀ ℤ :=
  (Finsupp.equivFunOnFinite.symm p.guards.plus).uncurry.sumElim <|
    (Finsupp.equivFunOnFinite.symm p.guards.minus).uncurry.sumElim <|
      (Finsupp.sigmaFinsuppEquivPiFinsupp.symm p.guards.auxiliary).sumElim p.guards.lone

theorem Profile.horizontalPart_apply (p : Profile J G H) (i : HorizontalIndex H) :
    p.horizontalPart i = p.signedValues (horizontalSite i) := by cases i <;> rfl

theorem Profile.guardPart_apply (p : Profile J G H) (i : GuardIndex J G) :
    p.guardPart i = p.signedValues (guardSite i) := by
  rcases i with ⟨k,n⟩ | ⟨k,n⟩ | ⟨k,j⟩ | g <;> rfl

private theorem mem_of_singletons {I : Type*} (S : AddSubgroup (I →₀ ℤ))
    (h : ∀ i, Finsupp.single i 1 ∈ S) (s : I →₀ ℤ) : s ∈ S := by
  induction s using Finsupp.induction_linear with
  | zero => exact S.zero_mem
  | add _ _ ha hb => exact S.add_mem ha hb
  | single i m =>
    have he : (Finsupp.singleAddHom i) (m • (1 : ℤ)) ∈ S := by
      rw [map_zsmul]
      exact S.zsmul_mem (h i) m
    simpa using he

/-- First prescribe a horizontal profile. The residual discrepancy at the guards
can then be lifted inside the horizontal kernel. -/
private theorem exists_coarse_lift {A I B : Type*} [AddCommGroup A]
    (p : A →+ I →₀ ℤ) (q : A →+ B →₀ ℤ)
    (hp : ∀ i, ∃ a, p a = Finsupp.single i 1)
    (hq : ∀ i, ∃ a, p a = 0 ∧ q a = Finsupp.single i 1)
    (x : I →₀ ℤ) (y : B →₀ ℤ) : ∃ a, p a = x ∧ q a = y := by
  obtain ⟨a, ha⟩ : x ∈ p.range := mem_of_singletons p.range hp x
  have hg (i : B) : Finsupp.single i 1 ∈ p.ker.map q := by
    obtain ⟨g, hpg, hqg⟩ := hq i
    exact ⟨g, hpg, hqg⟩
  obtain ⟨g, hpg, hqg⟩ := mem_of_singletons (p.ker.map q) hg (y - q a)
  refine ⟨a+g, ?_, ?_⟩
  · rw [map_add, ha, show p g = 0 from hpg, add_zero]
  · rw [map_add, hqg]
    abel

variable [Field F] (v : Site (Supplement J G H) → Valuation F ℤᵐ⁰)
    (signed : Fˣ → Profile J G H)
    (hval : ∀ (u : Fˣ) i, (signed u).signedValues i = order (v i) (u : F))

private def orderProjection {I : Type*} (site : I → Site (Supplement J G H))
    (part : Profile J G H → I →₀ ℤ) (he : ∀ p i, part p i = p.signedValues (site i)) :
    Additive Fˣ →+ I →₀ ℤ where
  toFun u := part (signed u.toMul)
  map_zero' := by
    ext i
    change part (signed 1) i = 0
    rw [he, hval, Units.val_one, order_one]
  map_add' a b := by
    ext i
    change part (signed (a.toMul * b.toMul)) i = part (signed a.toMul) i + part (signed b.toMul) i
    rw [he, he, he, hval, hval, hval, Units.val_mul, order_mul _ a.toMul.ne_zero b.toMul.ne_zero]

include hval in
/-- On the prescribed valuations, singleton horizontals and singleton guards
with zero horizontal values supply every horizontal/guard lift used by the
column realization theorem. -/
theorem exists_horizontal_guard_lift
    (hpoly : ∀ i, ∃ u, (signed u).horizontalPart = Finsupp.single i 1)
    (hprime : ∀ i, ∃ u, (signed u).horizontalPart = 0 ∧ (signed u).guardPart = Finsupp.single i 1)
    (t : Profile J G H) :
    ∃ b, (signed b).height = t.height ∧ (signed b).guards = t.guards ∧
      (signed b).horizontal = t.horizontal := by
  let P := orderProjection v signed hval horizontalSite Profile.horizontalPart
    Profile.horizontalPart_apply
  let Q := orderProjection v signed hval guardSite Profile.guardPart Profile.guardPart_apply
  obtain ⟨b, hh, hg⟩ := exists_coarse_lift P Q (fun i => hpoly i) (fun i => hprime i)
    t.horizontalPart t.guardPart
  refine ⟨b.toMul, funext (fun k => DFunLike.congr_fun hh (.inl k)), ?_, ?_⟩
  · apply Guards.ext_of_components
    · ext k n
      exact DFunLike.congr_fun hg (.inl (k,n))
    · ext k n
      exact DFunLike.congr_fun hg (.inr (.inl (k,n)))
    · ext k j
      exact DFunLike.congr_fun hg (.inr (.inr (.inl ⟨k,j⟩)))
    · ext g
      exact DFunLike.congr_fun hg (.inr (.inr (.inr g)))
  · ext h
    exact DFunLike.congr_fun hh (.inr h)

end UnconditionalCounterexample.DyadicDeviations
