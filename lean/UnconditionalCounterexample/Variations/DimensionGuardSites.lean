import UnconditionalCounterexample.Variations.DimensionGuardGeometry
import UnconditionalCounterexample.Variations.MultivariateSelectionSites

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations

variable {r : ℕ} {p : PrimeIndex} {τ : Type*}

namespace ScreenedGuard

/-- The guard and the additional rational points at the same prime. -/
abbrev Field (G : ScreenedGuard r p) : Option τ → Type
  | none => GuardUnramified.LocalField p.val (GaloisField p.val G.degree)
  | some _ => ℚ_[p.val]

@[reducible] instance (G : ScreenedGuard r p) (i : Option τ) : NontriviallyNormedField (G.Field i) :=
  match i with
  | none => inferInstanceAs (NontriviallyNormedField (GuardUnramified.LocalField p.val (GaloisField p.val G.degree)))
  | some _ => inferInstanceAs (NontriviallyNormedField ℚ_[p.val])
@[reducible] instance (G : ScreenedGuard r p) (i : Option τ) : NormedAlgebra ℚ_[p.val] (G.Field i) :=
  match i with
  | none => inferInstanceAs (NormedAlgebra ℚ_[p.val] (GuardUnramified.LocalField p.val (GaloisField p.val G.degree)))
  | some _ => inferInstanceAs (NormedAlgebra ℚ_[p.val] ℚ_[p.val])
instance (G : ScreenedGuard r p) (i : Option τ) : FiniteDimensional ℚ_[p.val] (G.Field i) :=
  match i with
  | none => inferInstanceAs (FiniteDimensional ℚ_[p.val] (GuardUnramified.LocalField p.val (GaloisField p.val G.degree)))
  | some _ => inferInstanceAs (FiniteDimensional ℚ_[p.val] ℚ_[p.val])
instance (G : ScreenedGuard r p) (i : Option τ) : CharZero (G.Field i) :=
  match i with
  | none => inferInstanceAs (CharZero (GuardUnramified.LocalField p.val (GaloisField p.val G.degree)))
  | some _ => inferInstanceAs (CharZero ℚ_[p.val])
instance (G : ScreenedGuard r p) (i : Option τ) : IsUltrametricDist (G.Field i) :=
  match i with
  | none => inferInstanceAs (IsUltrametricDist (GuardUnramified.LocalField p.val (GaloisField p.val G.degree)))
  | some _ => inferInstanceAs (IsUltrametricDist ℚ_[p.val])

def points (G : ScreenedGuard r p) (x : τ → Fin (r+1) → ℚ_[p.val]) :
    (i : Option τ) → Fin (r+1) → G.Field i
  | none => fun j ↦ algebraMap _ (GuardUnramified.LocalField p.val _) (G.w j)
  | some t => x t

theorem points_generate (G : ScreenedGuard r p) (x : τ → Fin (r+1) → ℚ_[p.val]) (i : Option τ) :
    Algebra.adjoin ℚ_[p.val] (Set.range (G.points x i)) = ⊤ := by
  cases i with
  | none => exact GuardUnramified.adjoin_tuple_eq_top G.w G.generates
  | some t => exact top_unique fun v _ ↦ (Algebra.adjoin ℚ_[p.val] (Set.range (x t))).algebraMap_mem v

private theorem guard_kernel_ne (G : ScreenedGuard r p) (x : τ → Fin (r+1) → ℚ_[p.val]) (t : τ) :
    RingHom.ker (aeval (R := ℚ_[p.val]) (G.points x none)).toRingHom ≠
      RingHom.ker (aeval (R := ℚ_[p.val]) (G.points x (some t))).toRingHom := by
  intro he
  let f : MvPolynomial (Fin (r+1)) ℚ_[p.val] := X 0 - C (x t 0)
  have hr : f ∈ RingHom.ker (aeval (R := ℚ_[p.val]) (G.points x (some t))).toRingHom := by
    change aeval (x t) f = 0
    simp [f]
  have hg : f ∈ RingHom.ker (aeval (R := ℚ_[p.val]) (G.points x none)).toRingHom := he ▸ hr
  have h : aeval (R := ℚ_[p.val]) (G.points x none) f = 0 := hg
  change aeval (fun j ↦ algebraMap _ (GuardUnramified.LocalField p.val _) (G.w j)) f = 0 at h
  simp only [f, map_sub, aeval_X, aeval_C, sub_eq_zero] at h
  exact GuardUnramified.first_ne_scalar (G.w 0) G.outside _ h

theorem points_distinct (G : ScreenedGuard r p) (x : τ → Fin (r+1) → ℚ_[p.val])
    (hx : Function.Injective x) : Function.Injective fun i ↦
      RingHom.ker (aeval (R := ℚ_[p.val]) (G.points x i)).toRingHom := by
  intro i j he
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some t => exact (guard_kernel_ne G x t he).elim
  | some s =>
    cases j with
    | none => exact (guard_kernel_ne G x s he.symm).elim
    | some t =>
      apply congrArg some
      apply hx
      funext l
      let F := X l - C (x t l)
      have ht : F ∈ RingHom.ker (aeval (R := ℚ_[p.val]) (G.points x (some t))).toRingHom := by
        change aeval (x t) F = 0
        simp [F]
      change RingHom.ker (aeval (R := ℚ_[p.val]) (G.points x (some s))).toRingHom = _ at he
      have hm : F ∈ RingHom.ker (aeval (R := ℚ_[p.val]) (G.points x (some s))).toRingHom := by
        rw [he]
        exact ht
      have hs : aeval (x s) F = 0 := hm
      simpa [F, sub_eq_zero] using hs

end ScreenedGuard
end UnconditionalCounterexample.MultivariateSelection
