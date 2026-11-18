import HereditaryAtomicity.CharP.LevelProfilesLattice
import HereditaryAtomicity.DVRBase.Chain
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.SuccPred

/-!
# Unbounded degrees along bounded increasing value sequences

A uniform bound on the relative degrees would put every valuation in a single
factorial-denominator lattice. Such a lattice admits no bounded strictly increasing
sequence. Only the elements in the sequence must be algebraic over the base, so the
argument applies inside a completion.
-/

noncomputable section
open scoped NNReal

namespace HereditaryAtomicity.DVRBase

/-- A strictly increasing bounded real sequence cannot have all its values
in the lattice obtained by dividing the integers by one fixed positive real. -/
theorem strictMono_not_fixed_integer_lattice
    (s : ℕ → ℝ) (hs : StrictMono s) (hbounded : BddAbove (Set.range s))
    (e : ℝ) (he : 0 < e) :
    ¬ ∀ n : ℕ, ∃ z : ℤ, e * s n = z := by
  intro h
  choose z hz using h
  have hmono : StrictMono z := by
    intro i j hij
    have hlt : (z i : ℝ) < (z j : ℝ) := by
      rw [← hz i, ← hz j]
      exact mul_lt_mul_of_pos_left (hs hij) he
    exact_mod_cast hlt
  obtain ⟨b, hb⟩ := hbounded
  obtain ⟨m, hm⟩ := exists_int_gt (e * b)
  apply hmono.not_bddAbove_range_of_isSuccArchimedean
  refine ⟨m, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hle : (z n : ℝ) ≤ e * b := by
    rw [← hz n]
    exact mul_le_mul_of_nonneg_left (hb (Set.mem_range_self n)) he.le
  have hlt : z n < m := by exact_mod_cast hle.trans_lt hm
  exact hlt.le

/-- For every positive natural denominator, some value of a strictly
increasing bounded real sequence does not belong to its integer lattice. -/
theorem exists_not_integer_multiple_of_strictMono_bddAbove
    (s : ℕ → ℝ) (hs : StrictMono s) (hbounded : BddAbove (Set.range s))
    (e : ℕ) (he : 0 < e) :
    ∃ n : ℕ, ¬ ∃ z : ℤ, (e : ℝ) * s n = z := by
  exact not_forall.mp
    (strictMono_not_fixed_integer_lattice s hs hbounded (e : ℝ) (by exact_mod_cast he))

/-- Bounded strictly increasing orders force unbounded minimal-polynomial
degrees over any base whose nonzero elements have integer orders. -/
theorem minpoly_natDegree_unbounded_of_strictMono_order
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    (v : Valuation L ℝ≥0)
    (hcoeff : ∀ a : k, a ≠ 0 → ∃ z : ℤ,
      realValuationOrder v (algebraMap k L a) = z)
    (x : ℕ → L) (hx : ∀ n, x n ≠ 0) (halg : ∀ n, IsAlgebraic k (x n))
    (hmono : StrictMono fun n => realValuationOrder v (x n))
    (hbounded : BddAbove (Set.range fun n => realValuationOrder v (x n)))
    (M : ℕ) : ∃ n, M < (minpoly k (x n)).natDegree := by
  by_contra h
  push Not at h
  obtain ⟨n, hn⟩ := exists_not_integer_multiple_of_strictMono_bddAbove
    (fun n => realValuationOrder v (x n)) hmono hbounded M.factorial
    (Nat.factorial_pos M)
  apply hn
  exact polynomial_order_factorial_integral (algebraMap k L) v
    (minpoly k (x n)) (minpoly.ne_zero (halg n).isIntegral) hcoeff M (h n)
    (hx n) (minpoly.aeval k (x n))

section RelativeDegree

variable (k F L : Type*) [Field k] [Field F] [Field L]
  [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L]
  [FiniteDimensional k F]

/-- A base minimal-polynomial degree is bounded by the degree of the actual
simple extension above a fixed finite intermediate field. -/
theorem minpoly_natDegree_le_relative_adjoin (x : L) (hx : IsAlgebraic F x) :
    (minpoly k x).natDegree ≤ Module.finrank k F *
      Module.finrank F (IntermediateField.adjoin F {x}) := by
  let E := IntermediateField.adjoin F {x}
  let : FiniteDimensional F E := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  let : FiniteDimensional k E := Module.Finite.trans F E
  let : IsScalarTower k E L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k F E,
      ← IsScalarTower.algebraMap_apply F E L,
      ← IsScalarTower.algebraMap_apply k F L]
  let y : E := ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩
  have hy : minpoly k y = minpoly k x :=
    (minpoly.algebraMap_eq (IsScalarTower.toAlgHom k E L).injective y).symm
  rw [← hy, Module.finrank_mul_finrank k F E]
  exact minpoly.natDegree_le y

/-- Relative simple-extension degrees are unbounded above every fixed finite
level when the specified nonzero algebraic elements have bounded increasing
orders. No global algebraicity of the ambient field is required. -/
theorem relative_adjoin_finrank_unbounded_of_strictMono_order
    (v : Valuation L ℝ≥0)
    (hcoeff : ∀ a : k, a ≠ 0 → ∃ z : ℤ,
      realValuationOrder v (algebraMap k L a) = z)
    (x : ℕ → L) (hx : ∀ n, x n ≠ 0) (halg : ∀ n, IsAlgebraic k (x n))
    (hmono : StrictMono fun n => realValuationOrder v (x n))
    (hbounded : BddAbove (Set.range fun n => realValuationOrder v (x n)))
    (M : ℕ) : ∃ n, M < Module.finrank F (IntermediateField.adjoin F {x n}) := by
  by_contra h
  push Not at h
  obtain ⟨n, hn⟩ := minpoly_natDegree_unbounded_of_strictMono_order k L v hcoeff
    x hx halg hmono hbounded (Module.finrank k F * M)
  have hle := minpoly_natDegree_le_relative_adjoin k F L (x n) ((halg n).tower_top F)
  exact (not_lt_of_ge (hle.trans (Nat.mul_le_mul_left _ (h n)))) hn

/-- The exact quantitative degree choice needed in Construction B: any
fixed positive first-ratio weight beats any prescribed bound at some block. -/
theorem exists_relative_adjoin_finrank_mul_ge
    (v : Valuation L ℝ≥0)
    (hcoeff : ∀ a : k, a ≠ 0 → ∃ z : ℤ,
      realValuationOrder v (algebraMap k L a) = z)
    (x : ℕ → L) (hx : ∀ n, x n ≠ 0) (halg : ∀ n, IsAlgebraic k (x n))
    (hmono : StrictMono fun n => realValuationOrder v (x n))
    (hbounded : BddAbove (Set.range fun n => realValuationOrder v (x n)))
    {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ n, B ≤ (Module.finrank F (IntermediateField.adjoin F {x n}) : ℝ) * ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (B / ε)
  obtain ⟨n, hn⟩ := relative_adjoin_finrank_unbounded_of_strictMono_order
    k F L v hcoeff x hx halg hmono hbounded m
  have hn' : (m : ℝ) < Module.finrank F (IntermediateField.adjoin F {x n}) := by
    exact_mod_cast hn
  exact ⟨n, ((div_lt_iff₀ hε).mp (hm.trans hn')).le⟩

end RelativeDegree

section SourceBlocks

variable {R : Type*} [CommRing R]

/-- A nonempty block of consecutive source ratios, starting at `a` and
ending at ratio index `a + n`. Its endpoint index is `a + n + 1`. -/
def sourceBlock (t : ℕ → R) (a n : ℕ) : R :=
  ∏ i ∈ Finset.range (n + 1), t (a + i)

@[simp] theorem sourceBlock_zero (t : ℕ → R) (a : ℕ) :
    sourceBlock t a 0 = t a := by simp [sourceBlock]

theorem sourceBlock_succ (t : ℕ → R) (a n : ℕ) :
    sourceBlock t a (n + 1) = sourceBlock t a n * t (a + n + 1) := by
  simp only [sourceBlock, Finset.prod_range_succ]
  simp only [Nat.add_assoc]

variable [IsDomain R]

theorem UniformizerChainData.sourceBlock_ne_zero {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (a n : ℕ) : sourceBlock t a n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact C.ratio_ne_zero (a + i)

omit [IsDomain R] in
/-- The block is an actual source quotient of its endpoint pair. -/
theorem UniformizerChainData.endpoint_eq_mul_sourceBlock {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (a n : ℕ) :
    C.endpoint a = C.endpoint (a + n + 1) * sourceBlock t a n := by
  induction n with
  | zero => simpa only [sourceBlock_zero, Nat.add_zero] using C.step a
  | succ n ih =>
      rw [sourceBlock_succ, ih, C.step (a + n + 1)]
      have heq : a + n + 1 + 1 = a + (n + 1) + 1 := by omega
      rw [heq]
      ring

variable {L : Type*} [Field L]

omit [IsDomain R] in
/-- Evaluating the source block gives the literal quotient of evaluated
endpoints, so no source-membership inference from values is needed. -/
theorem UniformizerChainData.map_sourceBlock_eq_div {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (f : R →+* L) (hf : Function.Injective f)
    (a n : ℕ) :
    f (sourceBlock t a n) = f (C.endpoint a) / f (C.endpoint (a + n + 1)) := by
  apply (eq_div_iff ((map_ne_zero_iff f hf).mpr
    (C.endpoint_ne_zero (a + n + 1)))).mpr
  rw [C.endpoint_eq_mul_sourceBlock a n, map_mul]
  exact mul_comm _ _

/-- Extending a source block increases its order strictly whenever every
ratio has positive order at the chosen dominating valuation. -/
theorem UniformizerChainData.strictMono_sourceBlock_order {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (f : R →+* L) (hf : Function.Injective f)
    (v : Valuation L ℝ≥0) (ht : ∀ n, 0 < realValuationOrder v (f (t n)))
    (a : ℕ) : StrictMono fun n => realValuationOrder v (f (sourceBlock t a n)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [sourceBlock_succ, map_mul, realValuationOrder_mul v
    ((map_ne_zero_iff f hf).mpr (C.sourceBlock_ne_zero a n))
    ((map_ne_zero_iff f hf).mpr (C.ratio_ne_zero (a + n + 1)))]
  linarith [ht (a + n + 1)]

omit [IsDomain R] in
/-- Source block orders have a fixed upper bound because their denominator
endpoint has order at least one; other source elements may have negative order. -/
theorem UniformizerChainData.bddAbove_sourceBlock_order {π : R} {t : ℕ → R}
    (C : UniformizerChainData π t) (f : R →+* L) (hf : Function.Injective f)
    (v : Valuation L ℝ≥0)
    (hfloor : ∀ n, 1 ≤ realValuationOrder v (f (C.endpoint n))) (a : ℕ) :
    BddAbove (Set.range fun n => realValuationOrder v (f (sourceBlock t a n))) := by
  refine ⟨realValuationOrder v (f (C.endpoint a)), ?_⟩
  rintro _ ⟨n, rfl⟩
  dsimp only
  rw [C.map_sourceBlock_eq_div f hf a n,
    realValuationOrder_div v ((map_ne_zero_iff f hf).mpr (C.endpoint_ne_zero a))
      ((map_ne_zero_iff f hf).mpr (C.endpoint_ne_zero (a + n + 1)))]
  have hnonneg := hfloor (a + n + 1)
  linarith

end SourceBlocks

/-- Construction B's degree choice for actual consecutive source-ratio
blocks, above any already chosen finite field level. -/
theorem UniformizerChainData.exists_sourceBlock_degree_mul_ge
    {R : Type*} [CommRing R] [IsDomain R]
    (k F L : Type*) [Field k] [Field F] [Field L]
    [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L]
    [FiniteDimensional k F]
    {π : R} {t : ℕ → R} (C : UniformizerChainData π t)
    (f : R →+* L) (hf : Function.Injective f) (v : Valuation L ℝ≥0)
    (hcoeff : ∀ a : k, a ≠ 0 → ∃ z : ℤ,
      realValuationOrder v (algebraMap k L a) = z)
    (halg : ∀ r : R, IsAlgebraic k (f r))
    (hfloor : ∀ n, 1 ≤ realValuationOrder v (f (C.endpoint n)))
    (ht : ∀ n, 0 < realValuationOrder v (f (t n)))
    (a : ℕ) (B : ℝ) :
    ∃ n, B ≤ (Module.finrank F
      (IntermediateField.adjoin F {f (sourceBlock t a n)}) : ℝ) *
        realValuationOrder v (f (t a)) := by
  exact exists_relative_adjoin_finrank_mul_ge k F L v hcoeff
    (fun n => f (sourceBlock t a n))
    (fun n => (map_ne_zero_iff f hf).mpr (C.sourceBlock_ne_zero a n))
    (fun n => halg (sourceBlock t a n))
    (C.strictMono_sourceBlock_order f hf v ht a)
    (C.bddAbove_sourceBlock_order f hf v hfloor a) (ht a) B

end HereditaryAtomicity.DVRBase
