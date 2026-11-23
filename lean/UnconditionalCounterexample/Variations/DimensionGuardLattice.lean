import UnconditionalCounterexample.Variations.DimensionGuardSites
import UnconditionalCounterexample.Variations.DimensionTensorLattices

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection.ScreenedGuard

open GuardSupport Variations
variable {r : ℕ} {p : PrimeIndex} {τ : Type*} (G : ScreenedGuard r p)

abbrev Integers : Option τ → Type
  | none => WittVector p.val (GaloisField p.val G.degree)
  | some _ => ℤ_[p.val]

@[reducible] instance (i : Option τ) : CommRing (G.Integers i) := match i with
  | none => inferInstanceAs (CommRing (WittVector p.val (GaloisField p.val G.degree)))
  | some _ => inferInstanceAs (CommRing ℤ_[p.val])

@[reducible] instance (i : Option τ) : Algebra ℤ_[p.val] (G.Integers i) := match i with
  | none => inferInstanceAs (Algebra ℤ_[p.val] (WittVector p.val (GaloisField p.val G.degree)))
  | some _ => inferInstanceAs (Algebra ℤ_[p.val] ℤ_[p.val])

instance (i : Option τ) : Module.Finite ℤ_[p.val] (G.Integers i) := match i with
  | none => inferInstanceAs (Module.Finite ℤ_[p.val] (WittVector p.val (GaloisField p.val G.degree)))
  | some _ => inferInstanceAs (Module.Finite ℤ_[p.val] ℤ_[p.val])

@[reducible] instance (i : Option τ) : Algebra ℤ_[p.val] (G.Field i) := match i with
  | none => inferInstanceAs (Algebra ℤ_[p.val] (GuardUnramified.LocalField p.val _))
  | some _ => inferInstanceAs (Algebra ℤ_[p.val] ℚ_[p.val])

instance (i : Option τ) : IsScalarTower ℤ_[p.val] ℚ_[p.val] (G.Field i) := match i with
  | none => inferInstanceAs (IsScalarTower ℤ_[p.val] ℚ_[p.val] (GuardUnramified.LocalField p.val _))
  | some _ => inferInstanceAs (IsScalarTower ℤ_[p.val] ℚ_[p.val] ℚ_[p.val])

def integerMap (i : Option τ) : G.Integers i →ₐ[ℤ_[p.val]] G.Field i := match i with
  | none => IsScalarTower.toAlgHom ℤ_[p.val] (WittVector p.val (GaloisField p.val G.degree)) _
  | some _ => Algebra.ofId _ _

theorem exists_integerMap_iff (i : Option τ) (z : G.Field i) :
    z ∈ Set.range (G.integerMap i) ↔ ‖z‖ ≤ 1 := by
  cases i with
  | none =>
    exact (GuardUnramified.integral_iff p.val (GaloisField p.val G.degree) z).symm.trans
      (GuardUnramified.norm_le_one_iff_valuation p.val (GaloisField p.val G.degree) z).symm
  | some s =>
    exact ⟨fun ⟨v,hv⟩ ↦ hv ▸ v.property,fun h ↦ ⟨⟨z,h⟩,rfl⟩⟩

def integerProductMap : (∀ i : Option τ, G.Integers i) →ₐ[ℤ_[p.val]] (∀ i : Option τ, G.Field i) :=
  AlgHom.pi fun i ↦ (G.integerMap i).comp (Pi.evalAlgHom ℤ_[p.val] _ i)

theorem exists_integerProductMap_iff (z : ∀ i : Option τ, G.Field i) :
    z ∈ Set.range G.integerProductMap ↔ ∀ i, ‖z i‖ ≤ 1 := by
  constructor
  · rintro ⟨v,rfl⟩ i
    exact (G.exists_integerMap_iff i _).mp ⟨v i,rfl⟩
  · intro h
    choose a ha using fun i ↦ (G.exists_integerMap_iff i _).mpr (h i)
    exact ⟨a,funext ha⟩

end UnconditionalCounterexample.MultivariateSelection.ScreenedGuard
