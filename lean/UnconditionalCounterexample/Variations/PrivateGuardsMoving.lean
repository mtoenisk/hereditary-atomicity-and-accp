import UnconditionalCounterexample.Variations.PrivateGuardsDomain
import UnconditionalCounterexample.Variations.MultiDomainLocalReturns

/-!
# The moving divisors of the punctured domain

Every normalized main generator is a unit of the enlarged horizontal
localization. Its values on the public and private branches give the
orders of each moving element, including at both evaluations of a private prime.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection IntersectionDomain WithZero MultiDomain NormalizedWords

variable {r d : ℕ} {c : Fin (r+1) → ℚ} {M : ℕ → Type*} (C : Config r d) (L : Rule r M c)

local notation "B" => horizontal C L
local notation "K" => FunctionField (r+1)
abbrev normalizedMainValue := (family C L).generator mixedPower
local notation "U" => normalizedMainValue C L

private def rawUnit (f : Poly r) (h : f ∈ inverted (Set.range (main C L)) (family C L).puncture) : (B)ˣ :=
  (IsLocalization.map_units (B) (⟨f,h⟩ : inverted (Set.range (main C L)) (family C L).puncture)).unit

def mixedUnit (n : ℕ) : (B)ˣ :=
  rawUnit C L (main C L n) (Submonoid.subset_closure (Or.inl ⟨n,rfl⟩)) /
    ∏ j ∈ Finset.range n,
      (rawUnit C L (main C L j) (Submonoid.subset_closure (Or.inl ⟨j,rfl⟩)) *
       rawUnit C L ((family C L).puncture j) (Submonoid.subset_closure (Or.inr ⟨j,rfl⟩))) ^ mixedPower n

theorem mixedUnit_val (n : ℕ) : ((mixedUnit C L n : B) : K) = U n := by
  let f := Units.map (horizontal C L).subtype.toMonoidHom
  change ((f (mixedUnit C L n) : Kˣ) : K) = _
  simp only [mixedUnit, map_div, map_prod, map_pow, map_mul, Units.val_div_eq_div_val,
    Units.coe_prod, Units.val_pow_eq_pow_val, Units.val_mul]
  change _ = normalizedMain _ _ _ n
  simp only [f, Units.coe_map, normalizedMain]
  rfl

theorem mixed_inverse_mem (n : ℕ) : (U n)⁻¹ ∈ horizontal C L := by
  let u := mixedUnit C L n
  have hi : (((u⁻¹ : (B)ˣ) : B) : K) = (U n)⁻¹ := by
    rw [← mixedUnit_val]
    exact eq_inv_of_mul_eq_one_left (congrArg (horizontal C L).subtype u.inv_mul)
  exact hi ▸ ((u⁻¹ : (B)ˣ) : B).property

theorem mixed_mem (n : ℕ) : U n ∈ horizontal C L := mixedUnit_val C L n ▸ (mixedUnit C L n : B).property

theorem mixed_ne (n : ℕ) : U n ≠ 0 := fun h ↦ (mixedUnit C L n).ne_zero (Subtype.ext ((mixedUnit_val C L n).trans h))

theorem mixed_horizontal (v : Valuation K ℤᵐ⁰) (hv : ∀ x ∈ horizontal C L, v x ≤ 1) (n : ℕ) : v (U n) = 1 :=
  (DiscreteOrders.order_eq_zero_iff _ (mixed_ne C L n)).mp
    (mixedUnit_val C L n ▸ DiscreteOrders.order_eq_zero_of_isUnit (horizontal C L).toSubring v hv (mixedUnit C L n).isUnit)

def branchLabel : Branch → Option ℕ
  | .inl (.inl j) => some j
  | _ => none

structure MovingValues (C : Config r d) (L : Rule r M c)
    (π : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰) (γ : PrimeIndex → Valuation (FunctionField (r+1)) ℤᵐ⁰) : Prop where
  seed (i : Branch) : branchVal C L π γ i (coordinate 0) = exp (-Targets.seedOrder (branchLabel i))
  generator (i : Branch) (n : ℕ) : branchVal C L π γ i (normalizedMainValue C L n) = exp (-(Targets.order (Targets.generator n) (branchLabel i) : ℤ))

def movingValue (n : ℕ) : K := Targets.moving (coordinate 0) (U) n

theorem moving_horizontal (v : Valuation K ℤᵐ⁰) (hv : ∀ x ∈ horizontal C L, v x ≤ 1) (n : ℕ) :
    v (movingValue C L n) = v (coordinate 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [movingValue,Targets.moving,map_div₀,map_mul,mixed_horizontal C L v hv,mul_one,div_one] at ih ⊢; exact ih

theorem moving_pole (n : ℕ) : movingValue C L n ∈ horizontal C L := by
  induction n with
  | zero => exact (horizontal C L).algebraMap_mem _
  | succ n ih => exact (horizontal C L).mul_mem ((horizontal C L).mul_mem ih (mixed_mem C L _)) (mixed_inverse_mem C L _)

variable (π : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰) (γ : PrimeIndex → Valuation (FunctionField (r+1)) ℤᵐ⁰)

local notation "V" => branchVal C L π γ
local notation "D" => domain C L π γ

theorem moving_branch (H : MovingValues C L π γ) (i n) :
    (V) i (movingValue C L n) = exp (-Targets.movingOrder n (branchLabel i)) :=
  Targets.moving_value _ _ _ _ (H.seed i) (H.generator i) n

theorem moving_mem (H : MovingValues C L π γ) (n : ℕ) : movingValue C L n ∈ D := by
  apply (mem_intersection _ _ _).mpr
  refine ⟨moving_pole C L n,fun i ↦ ?_⟩
  change (V) i (movingValue C L n) ≤ 1
  rw [moving_branch C L π γ H, exp_le_one_iff]
  cases branchLabel i with
  | none => exact neg_nonpos.mpr le_rfl
  | some j => exact neg_nonpos.mpr (primaryAtomProfile_nonneg n j)

def movingElement (H : MovingValues C L π γ) (n : ℕ) : D := ⟨movingValue C L n,moving_mem C L π γ H n⟩

theorem movingElement_ne (H : MovingValues C L π γ) (n : ℕ) : movingElement C L π γ H n ≠ 0 := by
  intro hz
  have h := congrArg (domain C L π γ).subtype hz
  have hv := moving_branch C L π γ H (.inl (.inl 0)) n
  change movingValue C L n = 0 at h
  exact exp_ne_zero (hv.symm.trans ((congrArg _ h).trans (map_zero _)))

end UnconditionalCounterexample.Variations.PrivateGuards.Live
