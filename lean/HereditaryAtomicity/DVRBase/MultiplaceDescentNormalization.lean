import HereditaryAtomicity.DVRBase.JointSelectionBox

/-!
# Nonnegative weights for restricted-support class descent

Subtracting the minimum of a nonconstant finite integer vector gives natural weights
with nonempty proper support. If the total place class is constant, this translates
every fibre by a fixed class and preserves infinitude. Natural exponents then give
products of integral ideals.
-/

noncomputable section
open scoped BigOperators
namespace HereditaryAtomicity.DVRBase

/-- A nonconstant integer coefficient vector has an exact natural
normalization with at least one zero and at least one positive coordinate. -/
theorem exists_nat_normalization_of_nonconstant
    {ι : Type*} [Fintype ι] [Nonempty ι] (η : ι → ℤ) (hη : JointNonconstant η) :
    ∃ (c : ℤ) (e : ι → ℕ),
      (∀ i, (e i : ℤ) = η i - c) ∧ (∃ i, e i = 0) ∧ (∃ i, 0 < e i) := by
  obtain ⟨m, hm⟩ := Finite.exists_min η
  let c := η m
  let e (i : ι) := (η i - c).toNat
  have he : ∀ i, (e i : ℤ) = η i - c := fun i => Int.toNat_of_nonneg (sub_nonneg.mpr (hm i))
  refine ⟨c, e, he, ⟨m, by simp [e, c]⟩, ?_⟩
  by_contra hpos
  push Not at hpos
  obtain ⟨i, j, hij⟩ := hη
  apply hij
  have hei : e i = 0 := by have := hpos i; omega
  have hej : e j = 0 := by have := hpos j; omega
  have hi := he i
  have hj := he j
  rw [hei, Int.natCast_zero] at hi
  rw [hej, Int.natCast_zero] at hj
  omega

/-- The normalization changes a weighted class by exactly the minimum
coefficient times the total class. -/
theorem sum_nat_normalization
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (η : ι → ℤ) (c : ℤ) (e : ι → ℕ) (he : ∀ i, (e i : ℤ) = η i - c)
    (v : ι → G) :
    (∑ i, e i • v i) = (∑ i, η i • v i) - c • (∑ i, v i) := by
  simp only [← natCast_zsmul, he, sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]

/-- An infinite nonconstant integer-weight fiber becomes an infinite
natural-weight fiber with nonempty proper support. Only constant total class
is needed, so a nonzero common total is permitted. -/
theorem exists_nat_weights_infinite_fiber
    {ι G : Type*} [Fintype ι] [Nonempty ι] [AddCommGroup G]
    (θ : ℕ → ι → G) (S : G) (hsum : ∀ n, ∑ i, θ n i = S)
    (η : ι → ℤ) (hη : JointNonconstant η) (g : G)
    (hfiber : Set.Infinite {n | ∑ i, η i • θ n i = g}) :
    ∃ (e : ι → ℕ) (g' : G),
      (∃ i, e i = 0) ∧ (∃ i, 0 < e i) ∧
      Set.Infinite {n | ∑ i, e i • θ n i = g'} := by
  obtain ⟨c, e, he, hz, hp⟩ := exists_nat_normalization_of_nonconstant η hη
  refine ⟨e, g - c • S, hz, hp, hfiber.mono ?_⟩
  intro n hn
  change (∑ i, e i • θ n i) = g - c • S
  rw [sum_nat_normalization η c e he, hsum, hn]

/-- Failure of the joint finite fibres yields natural weights with a zero
and a positive coordinate, and an infinite weighted class fiber. -/
theorem exists_nat_weights_infinite_fiber_of_not_jointFiniteFibers
    {ι G : Type*} [Fintype ι] [Nonempty ι] [AddCommGroup G]
    (θ : ℕ → ι → G) (hsum : ∀ n, ∑ i, θ n i = 0)
    (hfailure : ¬ JointFiniteFibers θ) :
    ∃ (e : ι → ℕ) (g : G),
      (∃ i, e i = 0) ∧ (∃ i, 0 < e i) ∧
      Set.Infinite {n | ∑ i, e i • θ n i = g} := by
  unfold JointFiniteFibers at hfailure
  push Not at hfailure
  obtain ⟨η, hη, g, hg⟩ := hfailure
  exact exists_nat_weights_infinite_fiber θ 0 hsum η hη g hg

/-- The support in the preceding theorem is a literal nonempty proper
finite subset, ready for a product of positive powers of component ideals. -/
theorem exists_proper_nat_support_infinite_fiber_of_not_jointFiniteFibers
    {ι G : Type*} [Fintype ι] [Nonempty ι] [AddCommGroup G]
    (θ : ℕ → ι → G) (hsum : ∀ n, ∑ i, θ n i = 0)
    (hfailure : ¬ JointFiniteFibers θ) :
    ∃ (e : ι → ℕ) (U : Finset ι) (g : G),
      U.Nonempty ∧ U ⊂ Finset.univ ∧ (∀ i, i ∈ U ↔ 0 < e i) ∧
      Set.Infinite {n | ∑ i, e i • θ n i = g} := by
  classical
  obtain ⟨e, g, ⟨i₀, hi₀⟩, ⟨i₁, hi₁⟩, hf⟩ :=
    exists_nat_weights_infinite_fiber_of_not_jointFiniteFibers θ hsum hfailure
  refine ⟨e, Finset.univ.filter (fun i => 0 < e i), g,
    ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₁⟩⟩, ?_, ?_, hf⟩
  · exact Finset.filter_ssubset.mpr ⟨i₀, Finset.mem_univ _, by simp [hi₀]⟩
  · intro i
    simp

end HereditaryAtomicity.DVRBase
