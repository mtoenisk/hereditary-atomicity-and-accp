import UnconditionalCounterexample.Variations.MultivariateWordRecovery
import UnconditionalCounterexample.Variations.DimensionClosedPoints

namespace UnconditionalCounterexample.Variations

open MvPolynomial MultivariateWordRecovery MultivariateRecovery

/-- Extend evaluation at a closed point over any residue extension to a surviving
polynomial localization. -/
noncomputable def closedPointEval {K E σ : Type*} [Field K] [Field E] [Algebra K E]
    (M : Submonoid (MvPolynomial σ K)) (A : Type*) [CommRing A] [Algebra K A]
    [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A] [IsLocalization M A]
    (u : σ → E) (h : ∀ m : M, aeval u m.val ≠ 0) : A →ₐ[K] E :=
  IsLocalization.liftAlgHom (f := aeval u) (fun m ↦ isUnit_iff_ne_zero.mpr (h m))

@[simp] theorem closedPointEval_polynomial {K E σ : Type*} [Field K] [Field E] [Algebra K E]
    (M : Submonoid (MvPolynomial σ K)) (A : Type*) [CommRing A] [Algebra K A]
    [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A] [IsLocalization M A]
    (u : σ → E) (h : ∀ m : M, aeval u m.val ≠ 0) (f : MvPolynomial σ K) :
    closedPointEval M A u h (algebraMap _ A f) = aeval u f := by
  simp [closedPointEval, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

/-- A rational sequence with nonzero values at the listed residue tuple is disjoint
from its point ideal after extension to the local coefficient field. -/
theorem retained_of_factor_values {k K E σ : Type*} [Field k] [Field K] [Field E] [Algebra k K]
    [Algebra K E] [Algebra k E] [IsScalarTower k K E]
    (P : ℕ → MvPolynomial σ k) (u : σ → E) (h : ∀ n, aeval u (P n) ≠ 0) :
    ∀ m : (Submonoid.closure (Set.range P)).map (MvPolynomial.map (algebraMap k K)),
      aeval u m.val ≠ 0 := by
  rintro ⟨m, y, hy, rfl⟩
  change eval₂Hom _ _ (MvPolynomial.map _ _) ≠ 0
  rw [eval₂Hom_map_hom, ← IsScalarTower.algebraMap_eq k K E]
  change aeval u y ≠ 0
  induction hy using Submonoid.closure_induction with
  | mem y hy => obtain ⟨n,rfl⟩ := hy; exact h n
  | one => simp
  | mul x y _ _ hx hy => simpa using mul_ne_zero hx hy

/-- The local closed-point evaluation of an original element agrees with the given
rational evaluation on the localization. This verifies the norm condition on T using
its original valuation at this place. -/
theorem closedPointEval_baseElement {k K E σ : Type*} [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
    (M : Submonoid (MvPolynomial σ k)) {B : Type*} [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization M B]
    (A : Type*) [CommRing A] [Algebra K A] [Algebra (MvPolynomial σ K) A]
    [IsScalarTower K (MvPolynomial σ K) A] [IsLocalization (M.map (MvPolynomial.map (algebraMap k K))) A]
    (u : σ → E) (h : ∀ m : M.map (MvPolynomial.map (algebraMap k K)), aeval u m.val ≠ 0)
    (ev : B →+* E) (hev : ∀ f : MvPolynomial σ k, ev (algebraMap _ B f) = aeval u f)
    (b : B) : closedPointEval _ A u h (baseElement (K := K) M A b) = ev b := by
  let incl := Algebra.TensorProduct.includeRight (R := k) (A := K) (B := B)
  let g := (closedPointEval _ A u h).toRingHom.comp ((tensorEquiv (K := K) M B A).toRingHom.comp incl.toRingHom)
  have hg : g = ev := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro f
    change closedPointEval _ A u h (baseElement (K := K) M A (algebraMap _ B f)) = ev (algebraMap _ B f)
    rw [baseElement_polynomial, closedPointEval_polynomial, hev]
    change eval₂Hom _ _ (MvPolynomial.map _ _) = _
    rw [eval₂Hom_map_hom, ← IsScalarTower.algebraMap_eq k K E]
    rfl
  exact RingHom.congr_fun hg b

end UnconditionalCounterexample.Variations
