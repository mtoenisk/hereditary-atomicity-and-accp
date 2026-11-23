import UnconditionalCounterexample.Variations.MultiDomainSelected
import UnconditionalCounterexample.Variations.MultiDomainFibreTargets

/-!
# Evaluating normalized fractions on the frozen fibres

The normalized polynomial values in the local input agree with evaluation
of the global fractions. This also holds at the rational point after
restricting evaluation to the horizontal localization.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain WithZero

variable {r : ℕ}

theorem map_normalized {K L : Type*} [Field K] [Field L] (e : K →+* L) (P : ℕ → K)
    (E : ℕ → ℕ) (i : ℕ) :
    e (RawWords.normalizedFactor P E i) = RawWords.normalizedFactor (fun j ↦ e (P j)) E i := by
  simp [RawWords.normalizedFactor, map_prod]

theorem localTuple_normalized {L : Type*} [Field L] [Algebra ℚ L] {v : Valuation L ℤᵐ⁰}
    (T : LocalTuple r v) (F : ℕ → Polys r) (E : ℕ → ℕ) (i : ℕ) :
    T.valuation (RawWords.normalizedFactor (fun j ↦ algebraMap _ (FunctionField r) (F j)) E i) =
      v (RawWords.normalizedFactor (fun j ↦ aeval T.x (F j)) E i) := by
  let e := IndependentTuples.evaluation T.x T.independent
  change v (e _) = _
  rw [map_normalized]
  have he (j : ℕ) : e (algebraMap _ _ (F j)) = aeval T.x (F j) :=
    IsFractionRing.lift_algebraMap (K := FunctionField r) (g := (aeval T.x : Polys r →ₐ[ℚ] L).toRingHom)
      T.independent (F j)
  simp only [he]

namespace Fibre

variable {p : PrimeIndex} (F : Fibre r p)

theorem componentEval_baseChange (c : Fin (r+1) → ℚ) {extra : Bool} (i : F.Component extra)
    (g : Polys (r+1)) :
    aeval (F.guard.points (F.sidePoints c extra) i) (map (algebraMap ℚ ℚ_[p.val]) g) =
      F.componentEval c extra i g := by
  change eval₂ _ _ (map _ g) = eval₂ _ _ g
  rw [eval₂_map]
  congr 1
  exact Subsingleton.elim _ _

theorem guard_eval (c : Fin (r+1) → ℚ) (extra : Bool) (g : Polys (r+1)) :
    F.componentEval c extra none g = aeval F.guard.tuple.x g := by
  let L := GuardUnramified.LocalField p.val (GaloisField p.val F.guard.degree)
  change eval₂ (Rat.castHom L) _ g = eval₂ (algebraMap ℚ L) _ g
  rw [show Rat.castHom L = algebraMap ℚ L from Subsingleton.elim ..]
  rfl

def primarySide (extra : Bool) {j : ℕ} {T : LocalTuple (r+1) (Padic.mulValuation (p := p.val))}
    (h : F.primary = some (j,T)) : F.Side extra := ⟨(), by simp [h]⟩

theorem primary_eval (c : Fin (r+1) → ℚ) (extra : Bool) {j : ℕ}
    {T : LocalTuple (r+1) (Padic.mulValuation (p := p.val))} (h : F.primary = some (j,T))
    (g : Polys (r+1)) :
    F.componentEval c extra (some (F.primarySide extra h)) g = aeval T.x g := by
  change eval₂ (Rat.castHom ℚ_[p.val]) (F.sidePoints c extra (F.primarySide extra h)) g = eval₂ (algebraMap ℚ ℚ_[p.val]) T.x g
  simp only [sidePoints, h, Option.elim_some, show Rat.castHom ℚ_[p.val] = algebraMap ℚ _ from Subsingleton.elim ..]

def pointSide : F.Side true := ⟨(), by simp⟩

theorem point_eval (c : Fin (r+1) → ℚ) {extra : Bool} (i : F.Side extra) (h : F.primary = none) (g : Polys (r+1)) :
    F.componentEval c extra (some i) g = ((eval c g : ℚ) : ℚ_[p.val]) := by
  have he : F.componentEval c extra (some i) = (Rat.castHom ℚ_[p.val]).comp (eval c) := by
    ext i <;> simp [componentEval, ScreenedGuard.points, sidePoints, h]
  exact DFunLike.congr_fun he g

end Fibre
end UnconditionalCounterexample.MultivariateSelection
