import UnconditionalCounterexample.Variations.DimensionClosedPoints
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.FieldTheory.Separable

/-!
# First derivatives at separable closed points

Interpolation at the closed residue fields supplies selectors. Multiplying a
squared selector by a coordinate minimal polynomial and a correction factor
constructs one designated unit derivative while all other jets vanish. This
proves simultaneous first-order interpolation and the generator-gradient span
required for the local conductor argument.
-/

namespace UnconditionalCounterexample.Variations

open MvPolynomial

variable {k σ ι : Type*} [Field k] [Finite ι] {E : ι → Type*}
  [∀ i, Field (E i)] [∀ i, Algebra k (E i)] [∀ i, Algebra.IsSeparable k (E i)]

/-- A polynomial vanishing at all the closed points with one prescribed unit derivative
at a single point and all other first derivatives zero. -/
theorem exists_closedPoint_coordinate_jet [DecidableEq ι] [DecidableEq σ]
    (γ : ∀ i, σ → E i) (hgen : ∀ i, Algebra.adjoin k (Set.range (γ i)) = ⊤)
    (hdist : Function.Injective (fun i ↦ RingHom.ker (aeval (R := k) (γ i)).toRingHom))
    (s : ι) (j : σ) : ∃ H : MvPolynomial σ k,
      (∀ i, aeval (γ i) H = 0) ∧
      ∀ i l, aeval (γ i) (pderiv l H) = if i = s ∧ l = j then 1 else 0 := by
  classical
  let ev i := aeval (R := k) (γ i)
  let f := minpoly k (γ s j)
  let g := Polynomial.aeval (X j : MvPolynomial σ k) f
  let a := Polynomial.aeval (γ s j) f.derivative
  have ha : a ≠ 0 := (Algebra.IsSeparable.isSeparable k (γ s j)).aeval_derivative_ne_zero
    (minpoly.aeval k (γ s j))
  have hev (P : Polynomial k) : ev s (Polynomial.aeval (X j : MvPolynomial σ k) P) =
      Polynomial.aeval (γ s j) P := by
    rw [← Polynomial.aeval_algHom_apply, show ev s (X j) = _ from aeval_X _ _]
  have hg : ev s g = 0 := (hev f).trans (minpoly.aeval k (γ s j))
  obtain ⟨b, hb⟩ := closedPointValues_surjective γ hgen hdist (Pi.single s (1 : E s))
  obtain ⟨c, hc⟩ := closedPointValues_surjective γ hgen hdist (Pi.single s a⁻¹)
  have hb' (i : ι) : ev i b = Pi.single s (1 : E s) i := congrFun hb i
  have hc' : ev s c = a⁻¹ := by simpa using congrFun hc s
  use b * b * c * g
  constructor
  · intro i
    change ev i _ = 0
    by_cases h : i = s
    · subst i
      simp [hg]
    · simp [hb', Pi.single_eq_of_ne h]
  · intro i l
    change ev i (pderiv l _) = _
    by_cases h : i = s
    · subst i
      simp only [Derivation.leibniz, smul_eq_mul, map_mul, map_add, hg, hb',
        Pi.single_eq_same, hc', mul_one, one_mul, zero_mul, add_zero]
      change a⁻¹ * ev s (pderiv l (Polynomial.aeval (X j) f)) = _
      rw [Derivation.comp_aeval_eq, smul_eq_mul, map_mul, hev]
      by_cases h : l = j
      · subst l
        simp [a, ha]
      · simp [pderiv_X_of_ne (Ne.symm h), h]
    · simp [Derivation.leibniz, smul_eq_mul, hb', h]

/-- Any independently prescribed values and gradients are simultaneously attainable. -/
theorem closedPointJets_surjective [Finite σ]
    (γ : ∀ i, σ → E i) (hgen : ∀ i, Algebra.adjoin k (Set.range (γ i)) = ⊤)
    (hdist : Function.Injective (fun i ↦ RingHom.ker (aeval (R := k) (γ i)).toRingHom))
    (v : ∀ i, E i) (w : ∀ i, σ → E i) :
    ∃ F : MvPolynomial σ k, (∀ i, aeval (γ i) F = v i) ∧
      ∀ i l, aeval (γ i) (pderiv l F) = w i l := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  let ev i := aeval (R := k) (γ i)
  obtain ⟨G, hG⟩ := closedPointValues_surjective γ hgen hdist v
  choose H hzero hjet using exists_closedPoint_coordinate_jet γ hgen hdist
  have hcoeff (s : ι) (j : σ) : ∃ P : MvPolynomial σ k, ev s P = w s j - ev s (pderiv j G) := by
    obtain ⟨P, hp⟩ := closedPointValues_surjective γ hgen hdist
      (Pi.single s (w s j - ev s (pderiv j G)))
    exact ⟨P, by simpa using congrFun hp s⟩
  choose P hP using hcoeff
  let D := ∑ s, ∑ j, P s j * H s j
  use G + D
  constructor
  · intro i
    simp [D, hzero, show aeval (γ i) G = v i from congrFun hG i]
  · intro i l
    simp [D, Derivation.leibniz, smul_eq_mul, hzero, hjet, mul_ite, ite_and, Finset.sum_ite_irrel]
    change ev i (pderiv l G) + ev i (P i l) = _
    rw [hP, add_sub_cancel]

/-- Gradients of any generating list of the intersection of the retained point ideals
span the full vector space at each point. This works over the closed residue fields
without splitting them over an algebraic closure. -/
theorem closedPoint_generator_gradients_span [Finite σ] {m : ℕ}
    (γ : ∀ i, σ → E i) (hgen : ∀ i, Algebra.adjoin k (Set.range (γ i)) = ⊤)
    (hdist : Function.Injective (fun i ↦ RingHom.ker (aeval (R := k) (γ i)).toRingHom))
    (H : Fin m → MvPolynomial σ k)
    (hI : Ideal.span (Set.range H) = ⨅ i, RingHom.ker (aeval (R := k) (γ i)).toRingHom)
    (s : ι) : Submodule.span (E s) (Set.range (fun j l ↦ aeval (γ s) (pderiv l (H j)))) = ⊤ := by
  classical
  let grad (f : MvPolynomial σ k) (l : σ) := aeval (γ s) (pderiv l f)
  let U := Submodule.span (E s) (Set.range (fun j ↦ grad (H j)))
  have hzero (f : MvPolynomial σ k) (hf : f ∈ Ideal.span (Set.range H)) : aeval (γ s) f = 0 :=
    Ideal.mem_iInf.mp (hI ▸ hf) s
  have hspan (f : MvPolynomial σ k) (hf : f ∈ Ideal.span (Set.range H)) : grad f ∈ U := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨j, rfl⟩ := hf
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero =>
      convert U.zero_mem using 1
      ext l
      simp [grad]
    | add f g _ _ hf hg =>
      convert U.add_mem hf hg using 1
      ext l
      simp [grad]
    | smul a f hf h =>
      convert U.smul_mem (aeval (γ s) a) h using 1
      ext l
      simp [grad, Derivation.leibniz, smul_eq_mul, hzero _ hf]
  apply top_unique
  intro v _
  obtain ⟨F, hF, hdF⟩ := closedPointJets_surjective γ hgen hdist 0 (Pi.single s v)
  have hv : grad F = v := funext fun l ↦ by simpa [grad] using hdF s l
  rw [← hv]
  apply hspan
  rw [hI, Ideal.mem_iInf]
  exact fun i ↦ hF i

end UnconditionalCounterexample.Variations
