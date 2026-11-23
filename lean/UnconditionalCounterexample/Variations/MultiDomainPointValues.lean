import UnconditionalCounterexample.Variations.MultiDomainRealizedReturns

/-!
# The extra rational component of the upper-dimensional example

Its specialization is the literal evaluation of the selected fractions at
the flag point, where every normalized factor is a unit at the reserved
prime and the moving terms satisfy integer returns.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open GuardSupport Variations MultiDomain WithZero Filter NormalizedWords MvPolynomial

variable {r : ℕ} (q : PrimeIndex)

local notation "L" => realizedLocal r q true
local notation "G" => standardGeometry r
local notation "A" => selectedData L G
local notation "C" => realizedChoices (r := r) q true
local notation "c" => flagPoint r
local notation "ev" => MultivariateFibres.pointEval (denominators A) (poleAlgebra A) c (flagPoint_retained L)

private def reservedSide : (permanentFibre L G q).Side (withPoint true q q) :=
  ⟨(),by simp [withPoint]⟩

theorem realized_point_value (n : ℕ) : Padic.mulValuation ((ev (selectedUnit L G n) : ℚ) : ℚ_[q.val]) = 1 := by
  let f := (Rat.castHom ℚ_[q.val]).comp (ev).toRingHom
  let F := permanentFibre L G q
  let s := reservedSide (r := r) q
  let i := some s
  have hF : F.primary = none := reserved_guard_only L G
  have h := (processed_normalized q true (valid_batch L G n).reserved i).1
  have hl : (permanentFibre L G q).label i = none := by
    change F.primary.map Prod.fst = none
    rw [hF]; rfl
  have he (g : Polys (r+1)) : f (algebraMap _ _ g) = F.componentEval c _ i g := by
    rw [F.point_eval c s hF]
    exact congrArg (Rat.castHom ℚ_[q.val]) (MultivariateFibres.pointEval_polynomial (denominators A) (poleAlgebra A) c (flagPoint_retained L) g)
  change Padic.mulValuation (f (selectedUnit L G n)) = 1
  rw [pole_normalized]
  simp only [he]
  rw [hl] at h
  simp only [Targets.order,Nat.cast_zero,neg_zero,exp_zero] at h
  exact h

theorem realized_point_unit (n : ℕ) : ∃ u : (PointPullback.localRationals q.val)ˣ,
    ((u : PointPullback.localRationals q.val) : ℚ) = ev (selectedUnit L G n) :=
  rational_point_unit q (realized_point_value q n)

theorem realized_moving_point_unit (n : ℕ) : ∃ u : (PointPullback.localRationals q.val)ˣ,
    ((u : PointPullback.localRationals q.val) : ℚ) = point A c (flagPoint_retained L) ((C).movingElement n) :=
  (C).moving_point_unit c (flagPoint_retained L) q.val (flagPoint_zero r)
    (fun k ↦ realized_point_unit q (Generator.b k).stage) (fun k ↦ realized_point_unit q (Generator.q k).stage) n

theorem realized_point_return (m : ℕ) (hm : 0 < m) : ∀ᶠ n in atTop,
    (point A c (flagPoint_retained L) ((C).movingElement n) - 1) / m ∈ PointPullback.localRationals q.val := by
  let f := (Rat.castHom ℚ_[q.val]).comp (ev).toRingHom
  let F := permanentFibre L G q
  let s := reservedSide (r := r) q
  let i := some s
  have hF : F.primary = none := reserved_guard_only L G
  have hl : (permanentFibre L G q).label i = none := by
    change F.primary.map Prod.fst = none
    rw [hF]; rfl
  have he (g : Polys (r+1)) : f (algebraMap _ _ g) = F.componentEval c _ i g := by
    rw [F.point_eval c s hF]
    exact congrArg (Rat.castHom ℚ_[q.val]) (MultivariateFibres.pointEval_polynomial (denominators A) (poleAlgebra A) c (flagPoint_retained L) g)
  have h := component_return q true q i f he (by
    rw [hl]
    have ht : f (algebraMap _ _ (X 0 : Polys (r+1))) = 1 := by
      rw [he,F.point_eval c s hF, MvPolynomial.eval_X,flagPoint_zero,Rat.cast_one]
    rw [ht,map_one]
    simp [Targets.seedOrder])
    (fun k ↦ by simp only [hl,Targets.order,Nat.cast_zero,neg_zero,exp_zero]; exact realized_point_value (r := r) q k)
  exact rational_point_integer_return q _ h m hm

theorem realized_pullback_chain : ∃ t : pullback A c (flagPoint_retained L) q.val,
    (t : FunctionField (r+1)) = coordinate 0 ∧ HasStrictChainAt (t^3) :=
  (C).pullback_chain c (flagPoint_retained L) (flagPoint_zero r) q.val (fun k ↦ realized_point_unit q (Generator.b k).stage)

end UnconditionalCounterexample.MultivariateSelection
