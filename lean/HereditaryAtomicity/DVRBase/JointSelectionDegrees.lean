import HereditaryAtomicity.DVRBase.BlockDegrees
import Mathlib.Data.Nat.Nth

/-!
# Simultaneous degree choices for finitely many places

Bounded strictly increasing orders force each bounded-degree exceptional set to
be finite. Thus finitely many places admit one common, arbitrarily late source
block satisfying all their relative-degree requirements. The fields, embeddings,
and finite old levels may differ between places. No simultaneous-selection
hypothesis is assumed.
-/

noncomputable section
open scoped NNReal BigOperators
namespace HereditaryAtomicity.DVRBase

/-- Only finitely many terms can have bounded minimal-polynomial degree when
nonzero algebraic terms have bounded strictly increasing orders. -/
theorem finite_minpoly_natDegree_le_of_strictMono_order
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    (v : Valuation L ℝ≥0)
    (hcoeff : ∀ a : k, a ≠ 0 → ∃ z : ℤ,
      realValuationOrder v (algebraMap k L a) = z)
    (x : ℕ → L) (hx : ∀ n, x n ≠ 0) (halg : ∀ n, IsAlgebraic k (x n))
    (hmono : StrictMono fun n => realValuationOrder v (x n))
    (hbounded : BddAbove (Set.range fun n => realValuationOrder v (x n)))
    (M : ℕ) : Set.Finite {n | (minpoly k (x n)).natDegree ≤ M} := by
  by_contra hinfinite
  let f := Nat.nth (fun n => (minpoly k (x n)).natDegree ≤ M)
  have hf : StrictMono f := Nat.nth_strictMono hinfinite
  have hmem : ∀ n, (minpoly k (x (f n))).natDegree ≤ M :=
    Nat.nth_mem_of_infinite hinfinite
  obtain ⟨n, hn⟩ := minpoly_natDegree_unbounded_of_strictMono_order k L v hcoeff
    (x ∘ f) (fun n => hx (f n)) (fun n => halg (f n)) (hmono.comp hf)
    (hbounded.mono (by
      rintro _ ⟨j, rfl⟩
      exact Set.mem_range_self (f j))) M
  exact (not_lt_of_ge (hmem n)) hn

section Relative
variable (k F L : Type*) [Field k] [Field F] [Field L]
  [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L]
  [FiniteDimensional k F]

/-- The low relative-degree exceptional set is finite at any fixed finite
old level; algebraicity of the entire ambient field is unnecessary. -/
theorem finite_relative_adjoin_finrank_le_of_strictMono_order
    (v : Valuation L ℝ≥0)
    (hcoeff : ∀ a : k, a ≠ 0 → ∃ z : ℤ,
      realValuationOrder v (algebraMap k L a) = z)
    (x : ℕ → L) (hx : ∀ n, x n ≠ 0) (halg : ∀ n, IsAlgebraic k (x n))
    (hmono : StrictMono fun n => realValuationOrder v (x n))
    (hbounded : BddAbove (Set.range fun n => realValuationOrder v (x n)))
    (M : ℕ) :
    Set.Finite {n | Module.finrank F (IntermediateField.adjoin F {x n}) ≤ M} := by
  apply (finite_minpoly_natDegree_le_of_strictMono_order k L v hcoeff x hx halg
    hmono hbounded (Module.finrank k F * M)).subset
  intro n hn
  exact (minpoly_natDegree_le_relative_adjoin k F L (x n) ((halg n).tower_top F)).trans
    (Nat.mul_le_mul_left _ hn)

/-- Every sufficiently late term meets a prescribed relative-degree bound. -/
theorem eventually_relative_adjoin_finrank_mul_ge
    (v : Valuation L ℝ≥0)
    (hcoeff : ∀ a : k, a ≠ 0 → ∃ z : ℤ,
      realValuationOrder v (algebraMap k L a) = z)
    (x : ℕ → L) (hx : ∀ n, x n ≠ 0) (halg : ∀ n, IsAlgebraic k (x n))
    (hmono : StrictMono fun n => realValuationOrder v (x n))
    (hbounded : BddAbove (Set.range fun n => realValuationOrder v (x n)))
    {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N,
      B ≤ (Module.finrank F (IntermediateField.adjoin F {x n}) : ℝ) * ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
  obtain ⟨N, hN⟩ := (finite_relative_adjoin_finrank_le_of_strictMono_order k F L
    v hcoeff x hx halg hmono hbounded M).bddAbove
  refine ⟨N + 1, fun n hn => ?_⟩
  have hd : M < Module.finrank F (IntermediateField.adjoin F {x n}) := by
    by_contra hd
    have := hN (not_lt.mp hd)
    omega
  have hd' : (M : ℝ) < Module.finrank F (IntermediateField.adjoin F {x n}) := by
    exact_mod_cast hd
  exact ((div_lt_iff₀ hε).mp (hM.trans hd')).le
end Relative

section Simultaneous
variable {ι : Type*} [Fintype ι]
    (k F L : ι → Type*) [∀ i, Field (k i)] [∀ i, Field (F i)] [∀ i, Field (L i)]
    [∀ i, Algebra (k i) (F i)] [∀ i, Algebra (F i) (L i)] [∀ i, Algebra (k i) (L i)]
    [∀ i, IsScalarTower (k i) (F i) (L i)] [∀ i, FiniteDimensional (k i) (F i)]

/-- A finite family of places admits one common tail on which all relative
extension degrees satisfy their individual quantitative requirements. -/
theorem eventually_simultaneous_relative_adjoin_finrank_mul_ge
    (v : ∀ i, Valuation (L i) ℝ≥0)
    (hcoeff : ∀ i (a : k i), a ≠ 0 → ∃ z : ℤ,
      realValuationOrder (v i) (algebraMap (k i) (L i) a) = z)
    (x : ∀ i, ℕ → L i) (hx : ∀ i n, x i n ≠ 0)
    (halg : ∀ i n, IsAlgebraic (k i) (x i n))
    (hmono : ∀ i, StrictMono fun n => realValuationOrder (v i) (x i n))
    (hbounded : ∀ i, BddAbove (Set.range fun n => realValuationOrder (v i) (x i n)))
    (ε B : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i,
      B i ≤ (Module.finrank (F i) (IntermediateField.adjoin (F i) {x i n}) : ℝ) * ε i := by
  classical
  choose N hN using fun i => eventually_relative_adjoin_finrank_mul_ge
    (k i) (F i) (L i) (v i) (hcoeff i) (x i) (hx i) (halg i) (hmono i)
      (hbounded i) (hε i) (B i)
  refine ⟨Finset.univ.sup N, fun n hn i => hN i n ?_⟩
  exact (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn

/-- Simultaneous high degrees can additionally be selected in any prescribed
infinite set of candidate block lengths. -/
theorem exists_simultaneous_relative_adjoin_finrank_mul_ge
    (v : ∀ i, Valuation (L i) ℝ≥0)
    (hcoeff : ∀ i (a : k i), a ≠ 0 → ∃ z : ℤ,
      realValuationOrder (v i) (algebraMap (k i) (L i) a) = z)
    (x : ∀ i, ℕ → L i) (hx : ∀ i n, x i n ≠ 0)
    (halg : ∀ i n, IsAlgebraic (k i) (x i n))
    (hmono : ∀ i, StrictMono fun n => realValuationOrder (v i) (x i n))
    (hbounded : ∀ i, BddAbove (Set.range fun n => realValuationOrder (v i) (x i n)))
    (ε B : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (candidates : Set ℕ) (hinfinite : candidates.Infinite) :
    ∃ n ∈ candidates, ∀ i,
      B i ≤ (Module.finrank (F i) (IntermediateField.adjoin (F i) {x i n}) : ℝ) * ε i := by
  obtain ⟨N, hN⟩ := eventually_simultaneous_relative_adjoin_finrank_mul_ge
    k F L v hcoeff x hx halg hmono hbounded ε B hε
  obtain ⟨n, hn, hlt⟩ := hinfinite.exists_gt N
  exact ⟨n, hn, hN n hlt.le⟩
end Simultaneous

/-- Finite simultaneous block-degree selection for literal consecutive source
ratios. Each place may have its own uniformizer, endpoint chain, completion,
and preceding finite level; the selected source block is common to all places.
The arbitrary infinite candidate set permits additional independent finite
avoidance conditions. -/
theorem exists_simultaneous_sourceBlock_degree_mul_ge
    {ι : Type*} [Fintype ι] {R : Type*} [CommRing R] [IsDomain R]
    (k F L : ι → Type*) [∀ i, Field (k i)] [∀ i, Field (F i)] [∀ i, Field (L i)]
    [∀ i, Algebra (k i) (F i)] [∀ i, Algebra (F i) (L i)] [∀ i, Algebra (k i) (L i)]
    [∀ i, IsScalarTower (k i) (F i) (L i)] [∀ i, FiniteDimensional (k i) (F i)]
    {π : ι → R} {t : ℕ → R} (C : ∀ i, UniformizerChainData (π i) t)
    (f : ∀ i, R →+* L i) (hf : ∀ i, Function.Injective (f i))
    (v : ∀ i, Valuation (L i) ℝ≥0)
    (hcoeff : ∀ i (a : k i), a ≠ 0 → ∃ z : ℤ,
      realValuationOrder (v i) (algebraMap (k i) (L i) a) = z)
    (halg : ∀ i (r : R), IsAlgebraic (k i) (f i r))
    (hfloor : ∀ i n, 1 ≤ realValuationOrder (v i) (f i ((C i).endpoint n)))
    (ht : ∀ i n, 0 < realValuationOrder (v i) (f i (t n)))
    (a : ℕ) (B : ι → ℝ) (candidates : Set ℕ) (hinfinite : candidates.Infinite) :
    ∃ n ∈ candidates, ∀ i,
      B i ≤ (Module.finrank (F i)
        (IntermediateField.adjoin (F i) {f i (sourceBlock t a n)}) : ℝ) *
          realValuationOrder (v i) (f i (t a)) := by
  exact exists_simultaneous_relative_adjoin_finrank_mul_ge k F L v hcoeff
    (fun i n => f i (sourceBlock t a n))
    (fun i n => (map_ne_zero_iff (f i) (hf i)).mpr ((C i).sourceBlock_ne_zero a n))
    (fun i n => halg i (sourceBlock t a n))
    (fun i => (C i).strictMono_sourceBlock_order (f i) (hf i) (v i) (ht i) a)
    (fun i => (C i).bddAbove_sourceBlock_order (f i) (hf i) (v i) (hfloor i) a)
    (fun i => realValuationOrder (v i) (f i (t a))) B (fun i => ht i a)
    candidates hinfinite

end HereditaryAtomicity.DVRBase
