import UnconditionalCounterexample.Variations.MultivariateFibres
import UnconditionalCounterexample.Variations.MultivariateInfinity
import UnconditionalCounterexample.Variations.MultivariateInversion
import UnconditionalCounterexample.ScalarExtension
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Recovery of the multivariate generic fibre

This module combines the valuative bound, inversion of the raw polynomials,
finite fibres, and faithful scalar descent for the localized multivariate
polynomial ring. Geometric tests and the existence of words in
the subalgebra are hypotheses for the construction to supply.
-/

noncomputable section

namespace UnconditionalCounterexample.MultivariateRecovery

open MvPolynomial TensorProduct
open MultivariateInfinity MultivariateInversion MultivariateFibres

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension of an arbitrary polynomial localization by its actual
denominator monoid. The target inverts the coefficientwise images. -/
noncomputable def tensorEquiv
    (M : Submonoid (MvPolynomial σ k)) (B : Type*) [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization M B]
    (E : Type*) [CommRing E] [Algebra K E] [Algebra (MvPolynomial σ K) E]
    [IsScalarTower K (MvPolynomial σ K) E] [IsLocalization (M.map (map (algebraMap k K))) E] :
    K ⊗[k] B ≃ₐ[K] E := by
  let e := algebraTensorAlgEquiv (σ := σ) k K
  let : Algebra (K ⊗[k] MvPolynomial σ k) E :=
    ((algebraMap (MvPolynomial σ K) E).comp e.toRingHom).toAlgebra
  let : IsScalarTower K (K ⊗[k] MvPolynomial σ k) E := by
    apply IsScalarTower.of_algebraMap_eq (R := K) (S := K ⊗[k] MvPolynomial σ k) (A := E)
    intro a
    change algebraMap K E a = algebraMap (MvPolynomial σ K) E (e (algebraMap K _ a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have hM : (M.map (Algebra.TensorProduct.includeRight (R := k) (A := K))).map e.toRingHom =
      M.map (map (algebraMap k K)) := by
    ext f
    constructor
    · rintro ⟨_, ⟨p,hp,rfl⟩, rfl⟩
      exact ⟨p,hp,by change MvPolynomial.map (algebraMap k K) p = e (1 ⊗ₜ[k] p); simp [e]⟩
    · rintro ⟨p,hp,rfl⟩
      refine ⟨1 ⊗ₜ[k] p, ⟨p,hp,rfl⟩, ?_⟩
      change e (1 ⊗ₜ[k] p) = MvPolynomial.map (algebraMap k K) p
      simp [e]
  let : IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := k) (A := K))) E :=
    IsLocalization.of_ringEquiv_left e.toRingEquiv hM (fun _ => rfl)
  exact IsLocalization.tensorProductEquivOfMapIncludeRight k K M B E

/-- Embedding of the original localization in its coefficient extension. -/
def baseElement
    (M : Submonoid (MvPolynomial σ k)) {B : Type*} [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization M B]
    (E : Type*) [CommRing E] [Algebra K E] [Algebra (MvPolynomial σ K) E]
    [IsScalarTower K (MvPolynomial σ K) E] [IsLocalization (M.map (map (algebraMap k K))) E]
    (b : B) : E :=
  tensorEquiv M B E ((1 : K) ⊗ₜ[k] b)

theorem baseElement_mem_baseChange
    (M : Submonoid (MvPolynomial σ k)) {B : Type*} [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization M B]
    (E : Type*) [CommRing E] [Algebra K E] [Algebra (MvPolynomial σ K) E]
    [IsScalarTower K (MvPolynomial σ K) E] [IsLocalization (M.map (map (algebraMap k K))) E]
    (A : Subalgebra k B) (a : A) :
    baseElement (K := K) M E (a : B) ∈ (ScalarExtension.subalgebraBaseChange k K A).map (tensorEquiv (K := K) M B E).toAlgHom := by
  refine ⟨1 ⊗ₜ[k] (a : B), ?_, rfl⟩
  exact ⟨1 ⊗ₜ[k] a, by simp⟩

variable [Fintype σ] [IsAlgClosed K]

/-- Multivariate generic recovery over the original coefficient field.
The first two geometric requirements are no common zero of any `r+1` raws,
and retained points on all surviving positive-dimensional prime loci.
Separation and directional derivatives are evaluated on base changes of
actual elements of `A`. The word condition allows any unbounded subsequence:
for each fixed predecessor infinitely many of its listed denominators
must be divisible by that predecessor. -/
theorem recover
    (F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ)
    (B : Type*) [CommRing B] [IsDomain B] [Algebra k B] [Algebra (MvPolynomial σ k) B]
    [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization (Submonoid.closure (Set.range F)) B]
    (E : Type*) [CommRing E] [Algebra K E] [Algebra (MvPolynomial σ K) E]
    [IsScalarTower K (MvPolynomial σ K) E]
    [IsLocalization ((Submonoid.closure (Set.range F)).map (MvPolynomial.map (algebraMap k K))) E]
    (A : Subalgebra k B)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (htop : ∀ i, ∃ p : MvPolynomial σ k, p.totalDegree < d i ∧ F i = l i ^ d i + p)
    (hlin : ∀ s : Finset ℕ, s.card = Fintype.card σ → ∀ j : σ,
      ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i)
    (hgeom : ∀ s : Finset ℕ, s.card = Nat.card σ + 1 → ∀ u : σ → K,
      ∃ i ∈ s, aeval u (F i) ≠ 0)
    (hword : ∀ j, {i | ∃ (a : ℕ) (H : MvPolynomial σ k) (w : A),
      H.totalDegree < a * d i ∧ F j ∣ H ∧
      algebraMap (MvPolynomial σ k) B (F i) ^ a = algebraMap (MvPolynomial σ k) B H * w}.Infinite)
    (hpoints : let M := (Submonoid.closure (Set.range F)).map (MvPolynomial.map (algebraMap k K))
      ∀ P : Ideal (MvPolynomial σ K), P.IsPrime → ¬ P.IsMaximal →
        Disjoint (M : Set (MvPolynomial σ K)) (P : Set (MvPolynomial σ K)) →
        ∃ u : σ → K, Retained M u ∧ P ≤ pointIdeal u)
    (hsep : let M := Submonoid.closure (Set.range F)
      let N := M.map (MvPolynomial.map (algebraMap k K))
      ∀ u v : σ → K, ∀ hu : Retained N u, ∀ hv : Retained N v, u ≠ v →
        ∃ a : A, pointEval N E u hu (baseElement (K := K) M E (a : B)) ≠
          pointEval N E v hv (baseElement (K := K) M E (a : B)))
    (hdir : let M := Submonoid.closure (Set.range F)
      let N := M.map (MvPolynomial.map (algebraMap k K))
      ∀ u : σ → K, Retained N u → ∀ v : σ → K, v ≠ 0 →
        ∃ a : A, ∃ p q : MvPolynomial σ K,
          algebraMap (MvPolynomial σ K) E p = baseElement (K := K) M E (a : B) * algebraMap _ E q ∧
          quotientDerivativeNumerator u v p q ≠ 0) : A = ⊤ := by
  let M := Submonoid.closure (Set.range F)
  let N := M.map (MvPolynomial.map (algebraMap k K))
  let x (i : σ) := algebraMap (MvPolynomial σ k) B (X i)
  have heval : aeval (R := k) x = IsScalarTower.toAlgHom k (MvPolynomial σ k) B := by
    ext i; simp [x]
  have hint (j : σ) : IsIntegral A (x j) := by
    apply integral_coordinates_in_domain A x F l d hl htop hlin _ j
    apply (hword 0).mono
    rintro i ⟨a,H,w,hd,_,hw⟩
    exact ⟨a,H,w,hd,heval ▸ hw⟩
  let : Module.Finite A B := finite_of_integral_coordinates_and_words F A hint hgeom (by
    intro j; apply (hword j).mono
    rintro i ⟨a,H,w,hd,hdiv,hw⟩
    have ha : a ≠ 0 := by rintro rfl; simp at hd
    exact ⟨a,H,w,Nat.pos_of_ne_zero ha,hdiv,hw⟩)
  let e := tensorEquiv (K := K) M B E
  let A' := (ScalarExtension.subalgebraBaseChange k K A).map e.toAlgHom
  let : Module.Finite A' E := ScalarExtension.finite_mapped_subalgebraBaseChange k K A e
  let lift (a : A) : A' := ⟨baseElement (K := K) M E (a : B), baseElement_mem_baseChange M E A a⟩
  apply ScalarExtension.subalgebra_eq_top_of_mapped_baseChange_eq_top k K A e
  apply subalgebra_eq_top_of_separation_and_tangents N E A' (retainedPoint_of_prime N hpoints)
  · intro u v hu hv hne
    obtain ⟨a,ha⟩ := hsep u v hu hv hne
    exact ⟨lift a,ha⟩
  · intro u hu v hv
    obtain ⟨a,p,q,hfrac,hd⟩ := hdir u hu v hv
    obtain ⟨f,hf,hdf⟩ := cleared_tangent N E u hu v (lift a : E) p q hfrac hd
    exact ⟨lift a,f,q,hf,hdf⟩

end UnconditionalCounterexample.MultivariateRecovery
