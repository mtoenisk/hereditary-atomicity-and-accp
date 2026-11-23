import UnconditionalCounterexample.Variations.MultivariateListedWords

/-! # Countably many geometric test configurations

Every pair and tangent test is a nonvanishing condition on a rational
polynomial in the two tuples of coordinates. Two configurations with the
same rational evaluation kernel therefore give the same tests. Noetherianity
over the countable ground field makes the set of these kernels countable,
even when the test field is uncountable.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuardsRecovery

open MvPolynomial MultivariateFibres MultivariateStage MultivariateListedWords

variable {k K σ : Type} [Field k] [Field K] [Algebra k K]

abbrev Config (σ K : Type) := (σ → K) × (σ → K)

private def joint (x : Config σ K) : MvPolynomial (σ ⊕ σ) k →ₐ[k] K :=
  aeval (Sum.elim x.1 x.2)

/-- Equality of rational polynomial relations in the two tuples. -/
def SameTests (x y : Config σ K) := RingHom.ker (joint (k := k) x).toRingHom =
  RingHom.ker (joint (k := k) y).toRingHom

/-- A sequence of configurations representing the rational relations of
every pair of geometric tuples. -/
theorem exists_configurations [Fintype σ] [Countable k] :
    ∃ R : ℕ → Config σ K, ∀ x, ∃ n, SameTests (k := k) (R n) x := by
  let ker (x : Config σ K) := RingHom.ker (joint (k := k) x).toRingHom
  obtain ⟨I, hI⟩ := MultivariateReservations.exists_ideal_enumeration (k := k) (σ := σ ⊕ σ)
  classical
  let R (n : ℕ) := if h : ∃ x, ker x = I n then h.choose else (0,0)
  refine ⟨R, fun x => ?_⟩
  obtain ⟨n, hn⟩ := hI (ker x)
  have h : ∃ y, ker y = I n := ⟨x,hn.symm⟩
  exact ⟨n,show ker (R n) = ker x from (by simp only [R,h,↓reduceDIte]; exact h.choose_spec.trans hn)⟩

namespace SameTests
variable {x y : Config σ K} (h : SameTests (k := k) x y)
include h

private theorem nonzero (p : MvPolynomial (σ ⊕ σ) k) : joint x p ≠ 0 ↔ joint y p ≠ 0 :=
  not_congr (show p ∈ RingHom.ker (joint (k := k) x).toRingHom ↔
    p ∈ RingHom.ker (joint (k := k) y).toRingHom from h ▸ Iff.rfl)

omit h in
private theorem first (p : MvPolynomial σ k) (x : Config σ K) :
    joint x (rename (Sum.inl : σ → σ ⊕ σ) p) = eval x.1 (extend (K := K) p) := by
  rw [joint, aeval_rename, extend, eval_map]; rfl

omit h in
private theorem second (p : MvPolynomial σ k) (x : Config σ K) :
    joint x (rename (Sum.inr : σ → σ ⊕ σ) p) = eval x.2 (extend (K := K) p) := by
  rw [joint, aeval_rename, extend, eval_map]; rfl

private theorem separate : x.1 ≠ x.2 ↔ y.1 ≠ y.2 := by
  simp only [Function.ne_iff]
  apply exists_congr
  intro i
  have he := h.nonzero (X (Sum.inl i) - X (Sum.inr i))
  simp only [map_sub,sub_ne_zero] at he
  simpa [joint] using he

private theorem direction : x.2 ≠ 0 ↔ y.2 ≠ 0 := by
  simp only [Function.ne_iff, Pi.zero_apply]
  exact exists_congr fun i => by simpa [joint] using h.nonzero (X (Sum.inr i))

theorem pair_valid (H : MvPolynomial σ k) (a : ℕ) :
    (Test.pair x.1 x.2 a (extend (K := K) H)).Valid ↔ (Test.pair y.1 y.2 a (extend H)).Valid := by
  have hl := h.nonzero (rename (Sum.inl : σ → σ ⊕ σ) H)
  have hr := h.nonzero (rename (Sum.inr : σ → σ ⊕ σ) H)
  simp only [first] at hl
  simp only [second] at hr
  exact and_congr h.separate (and_congr Iff.rfl (and_congr hl hr))

theorem tangent_valid (H : MvPolynomial σ k) (a : ℕ) :
    (Test.tangent x.1 x.2 a (extend (K := K) H)).Valid ↔ (Test.tangent y.1 y.2 a (extend H)).Valid := by
  have hl := h.nonzero (rename (Sum.inl : σ → σ ⊕ σ) H)
  simp only [first] at hl
  exact and_congr h.direction (and_congr Iff.rfl hl)

variable [Fintype σ]

theorem pair_holds (F H : MvPolynomial σ k) (a : ℕ) :
    (Test.pair x.1 x.2 a (extend (K := K) H)).Holds (extend F) ↔
    (Test.pair y.1 y.2 a (extend H)).Holds (extend F) := by
  let L := rename (Sum.inl : σ → σ ⊕ σ) (R := k)
  let R := rename (Sum.inr : σ → σ ⊕ σ) (R := k)
  simpa only [L,R,map_pow,map_mul,map_sub,first,second,sub_ne_zero,Test.Holds] using
    h.nonzero ((L F)^a * R H - (R F)^a * L H)

private def dpoly (f : MvPolynomial σ k) : MvPolynomial (σ ⊕ σ) k :=
  ∑ i, rename (Sum.inl : σ → σ ⊕ σ) (pderiv i f) * X (Sum.inr i)

omit h in
private theorem eval_dpoly (f : MvPolynomial σ k) (x : Config σ K) :
    joint x (dpoly f) = directional x.1 x.2 (extend f) := by
  simp only [dpoly,directional,gradient,map_sum,map_mul,first,extend,pderiv_map]
  simp [joint]

theorem tangent_holds (F H : MvPolynomial σ k) (a : ℕ) :
    (Test.tangent x.1 x.2 a (extend (K := K) H)).Holds (extend F) ↔
    (Test.tangent y.1 y.2 a (extend H)).Holds (extend F) := by
  let L := rename (Sum.inl : σ → σ ⊕ σ) (R := k)
  change (directional x.1 x.2 ((extend F)^a) * eval x.1 (extend H) -
    eval x.1 ((extend F)^a) * directional x.1 x.2 (extend H) ≠ 0) ↔ _
  have hf : extend (K := K) (F^a) = (extend F)^a := map_pow _ _ _
  simpa only [Test.Holds,quotientDerivativeNumerator,L,map_sub,map_mul,first,eval_dpoly,hf,
    directional] using h.nonzero (dpoly (F^a) * L H - L (F^a) * dpoly H)

end SameTests
end UnconditionalCounterexample.Variations.PrivateGuardsRecovery
