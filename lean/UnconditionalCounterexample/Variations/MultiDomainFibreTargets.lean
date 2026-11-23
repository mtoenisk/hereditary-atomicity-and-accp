import UnconditionalCounterexample.Variations.DimensionGuardSites
import UnconditionalCounterexample.Variations.MultiDomainStageTargets
import UnconditionalCounterexample.Variations.GuardNorm

/-!
# Arithmetic prescriptions on the complete finite fibre at a prime

The guard lives in its unramified field. A primary, or the additional
rational evaluation at the reserved prime, supplies the rational p-adic
component. Each component receives its own raw target and return precision
from the same polynomial history.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection.Fibre

open MvPolynomial GuardSupport Variations MultiDomain WithZero
open scoped Topology

variable {r : ℕ} {p : PrimeIndex} (F : Fibre r p)

abbrev Side (extra : Bool) := {_u : Unit // (F.primary.isSome || extra) = true}

/-- At the reserved prime the table is guard-only, so its optional second
component specializes the coordinates at the rational point. -/
def sidePoints (c : Fin (r+1) → ℚ) (extra : Bool) (_ : F.Side extra) : Fin (r+1) → ℚ_[p.val] :=
  F.primary.elim (fun i ↦ (c i : ℚ_[p.val])) (fun z ↦ z.2.x)

abbrev Component (extra : Bool) := Option (F.Side extra)

def label {extra : Bool} : F.Component extra → Option ℕ
  | none => none
  | some _ => F.primary.map Prod.fst

def localValuation {extra : Bool} (i : F.Component extra) : Valuation (F.guard.Field i) ℤᵐ⁰ := by
  cases i with
  | none => exact GuardUnramified.valuation p.val _
  | some _ => exact Padic.mulValuation

theorem localValuation_prime {extra : Bool} (i : F.Component extra) :
    F.localValuation i (p.val : F.guard.Field i) = exp (-1) := by
  cases i with
  | none => exact GuardUnramified.valuation_prime p.val _
  | some _ =>
    change Padic.mulValuation (p.val : ℚ_[p.val]) = _
    exact EvaluationDVR.valuation_prime p.val (RingHom.id ℚ_[p.val])

private theorem lt_iff_norm_lt {L : Type*} [NormedField L] (v : Valuation L ℤᵐ⁰)
    (h : ∀ a : L, ‖a‖ ≤ 1 ↔ v a ≤ 1) (a b : L) : v a < v b ↔ ‖a‖ < ‖b‖ := by
  rw [← not_le, ← not_le (a := ‖b‖)]
  apply not_congr
  by_cases ha : a = 0
  · simp [ha]
  rw [← div_le_one₀ (v.pos_iff.mpr ha), ← map_div₀, ← h, norm_div, div_le_one₀ (norm_pos_iff.mpr ha)]

theorem localValuation_compat {extra : Bool} (i : F.Component extra) (a b : F.guard.Field i) :
    F.localValuation i a < F.localValuation i b ↔ ‖a‖ < ‖b‖ := by
  cases i with
  | none => exact lt_iff_norm_lt _ (GuardUnramified.norm_le_one_iff_valuation p.val _) a b
  | some _ => exact Padic.norm_lt_norm_iff_mulValuation_lt.symm

def componentEval (c : Fin (r+1) → ℚ) (extra : Bool) (i : F.Component extra) : Polys (r+1) →+* F.guard.Field i :=
  eval₂Hom (Rat.castHom _) (F.guard.points (F.sidePoints c extra) i)

theorem componentEval_ne_zero (c : Fin (r+1) → ℚ) (extra : Bool) (i : F.Component extra)
    (g : Polys (r+1)) (hg : g ≠ 0) (hc : MvPolynomial.eval c g ≠ 0) :
    F.componentEval c extra i g ≠ 0 := by
  cases i with
  | none =>
    intro he
    apply hg
    apply F.guard.independent
    rw [map_zero]
    let L := GuardUnramified.LocalField p.val (GaloisField p.val F.guard.degree)
    change eval₂ (Rat.castHom L) _ g = 0 at he
    change eval₂ (algebraMap ℚ L) _ g = 0
    rwa [show algebraMap ℚ L = Rat.castHom L from Subsingleton.elim ..]
  | some u =>
    cases h : F.primary with
    | none =>
      have he : F.componentEval c extra (some u) = (Rat.castHom ℚ_[p.val]).comp (MvPolynomial.eval c) := by
        ext i <;> simp [componentEval, ScreenedGuard.points, sidePoints, h]
      rw [he]
      exact Rat.cast_ne_zero.mpr hc
    | some j =>
      intro he
      apply hg
      apply j.2.independent
      rw [map_zero]
      change eval₂ (Rat.castHom ℚ_[p.val]) (F.sidePoints c extra u) g = 0 at he
      change eval₂ (algebraMap ℚ ℚ_[p.val]) j.2.x g = 0
      simpa only [sidePoints, h, Option.elim_some,
        show algebraMap ℚ ℚ_[p.val] = Rat.castHom _ from Subsingleton.elim ..] using he

theorem points_injective (c : Fin (r+1) → ℚ) (extra : Bool) :
    Function.Injective fun i : F.Component extra ↦
      RingHom.ker (aeval (R := ℚ_[p.val]) (F.guard.points (F.sidePoints c extra) i)).toRingHom :=
  F.guard.points_distinct _ (fun _ _ _ ↦ Subsingleton.elim _ _)

variable {M : ℕ → Type*} {n : ℕ}

def target (h : History r M n) (c : Fin (r+1) → ℚ) (extra : Bool) (i : F.Component extra) : F.guard.Field i :=
  Targets.rawTarget h (F.componentEval c extra i) (F.localValuation i) p.val (F.label i)

def targetSet (h : History r M n) (c : Fin (r+1) → ℚ) (extra : Bool) (i : F.Component extra) : Set (F.guard.Field i) :=
  Targets.rawNeighborhood h (F.componentEval c extra i) (F.localValuation i) p.val (F.label i)

theorem target_ne_zero (h : History r M n) (c : Fin (r+1) → ℚ) (extra : Bool) (i : F.Component extra)
    (hF : ∀ j : Fin n, F.componentEval c extra i ((h j).raw j.val) ≠ 0) :
    F.target h c extra i ≠ 0 :=
  Targets.rawTarget_ne_zero _ _ _ _ _ (F.localValuation_prime i) hF

theorem targetSet_mem (h : History r M n) (c : Fin (r+1) → ℚ) (extra : Bool) (i : F.Component extra)
    (hF : ∀ j : Fin n, F.componentEval c extra i ((h j).raw j.val) ≠ 0) :
    F.targetSet h c extra i ∈ 𝓝 (F.target h c extra i) :=
  Targets.rawNeighborhood_mem _ _ _ _ _ (F.localValuation_prime i) (F.localValuation_compat i) hF

end UnconditionalCounterexample.MultivariateSelection.Fibre
