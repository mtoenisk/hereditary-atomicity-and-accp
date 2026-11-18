import HereditaryAtomicity.DVRBase.IntersectionReturn

/-!
# The witnessed endpoint obstruction in the original source

These results retain the particular nonzero endpoint. They exclude even an
atomic product multiplied by an arbitrary intrinsic unit of the intersection.
-/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators NNReal
variable {K : Type*} [Field K]
namespace SourceBlockData
variable {R : Subring K} (B : SourceBlockData R)

/-- Units of the literal source intersection avoid the junk ideal. -/
theorem intersection_unit_not_mem_junk (D O : Subring K)
    (hO : ∀ a : O, B.valuation (a : K) ≤ 1) (Λ : Set ℕ)
    (x : ↥(B.sourceSubring O Λ ⊓ D)) (hx : IsUnit x) : (x : K) ∉ B.sourceJunk O := by
  intro hj
  exact not_isUnit_of_mapped_order_pos (B.sourceSubring O Λ ⊓ D).subtype B.valuation
    (fun y => B.sourceSubring_bounded O hO Λ ⟨y, y.property.1⟩)
    (B.sourceJunk_order_pos O hO hj (Subtype.coe_ne_coe.mpr hx.ne_zero)) hx

/-- Fresh returned quotients make the actual junk intersection atomless. -/
theorem intersection_irreducible_not_mem_junk
    (D : Subring K) [IsFractionRing D K] (places : Set (MaximalSpectrum D))
    (O : Subring K) (hO : ∀ a : O, B.valuation (a : K) ≤ 1)
    (Λ : Set ℕ) (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hS : ∀ M ∈ places, B.sourceSubring O Λ ≤ sourceMaximalStalk D M)
    (sourceRatio : ℕ → D) (hratio : ∀ n, (sourceRatio n : K) = (B.ratio n : K))
    (hunits : ∀ n (M : MaximalSpectrum D), M ∉ places →
      IsUnit (sourceMaximalMap D M (sourceRatio n)))
    (x : ↥(B.sourceSubring O Λ ⊓ D)) (hx : Irreducible x) :
    (x : K) ∉ B.sourceJunk O := by
  intro hj
  obtain ⟨n, _, _, q, hq, hqD, heq, hy, hypos, hqpos⟩ :=
    B.sourceJunk_fresh_split_in_intersection D places O hO Λ hcofinal hS sourceRatio
      hratio hunits hj x.property.2 (Subtype.coe_ne_coe.mpr hx.ne_zero) 0
  let T := B.sourceSubring O Λ ⊓ D
  let b : T := ⟨sourceRatio n, hy, (sourceRatio n).property⟩
  let c : T := ⟨q, B.sourceJunk_le_sourceSubring O Λ hq, hqD⟩
  have hbnd : ∀ y : T, B.valuation (y : K) ≤ 1 :=
    fun y => B.sourceSubring_bounded O hO Λ ⟨y, y.property.1⟩
  rcases hx.isUnit_or_isUnit (show x = b * c from Subtype.ext heq) with hb | hc
  · exact not_isUnit_of_mapped_order_pos T.subtype B.valuation hbnd (r := b) hypos hb
  · exact not_isUnit_of_mapped_order_pos T.subtype B.valuation hbnd (r := c) hqpos hc

/-- The actual first endpoint is a nonzero nonunit of the original-source
intersection; membership is retained as an explicit source fact. -/
theorem intersection_endpoint_nonzero_nonunit (D O : Subring K)
    (hO : ∀ a : O, B.valuation (a : K) ≤ 1) (Λ : Set ℕ)
    (hzD : (B.endpoint 1 : K) ∈ D) :
    let z : ↥(B.sourceSubring O Λ ⊓ D) :=
      ⟨B.endpoint 1, B.endpoint_mem_sourceSubring O Λ 1, hzD⟩
    z ≠ 0 ∧ ¬ IsUnit z := by
  dsimp only
  refine ⟨fun h => (Subtype.coe_ne_coe.mpr (B.endpoint_ne_zero 1))
    (congrArg (fun z : ↥(B.sourceSubring O Λ ⊓ D) => (z : K)) h), ?_⟩
  apply not_isUnit_of_mapped_order_pos (B.sourceSubring O Λ ⊓ D).subtype B.valuation
    (fun y => B.sourceSubring_bounded O hO Λ ⟨y, y.property.1⟩)
  exact zero_lt_one.trans_le (B.endpoint_order_ge_one 1)

/-- The endpoint has no atomic factorization even up to an arbitrary unit
of the original-source intersection. This is a witnessed obstruction, stronger
than merely asserting that the intersection fails atomicity. -/
theorem intersection_endpoint_no_associated_atomic_product
    (D : Subring K) [IsFractionRing D K] (places : Set (MaximalSpectrum D))
    (O : Subring K) (hO : ∀ a : O, B.valuation (a : K) ≤ 1)
    (Λ : Set ℕ) (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hS : ∀ M ∈ places, B.sourceSubring O Λ ≤ sourceMaximalStalk D M)
    (sourceRatio : ℕ → D) (hratio : ∀ n, (sourceRatio n : K) = (B.ratio n : K))
    (hunits : ∀ n (M : MaximalSpectrum D), M ∉ places →
      IsUnit (sourceMaximalMap D M (sourceRatio n)))
    (hno : B.NoOutsideJunkFactorization O Λ)
    (n : ℕ) (u : (↥(B.sourceSubring O Λ ⊓ D))ˣ)
    (f : Fin n → ↥(B.sourceSubring O Λ ⊓ D)) (hf : ∀ i, Irreducible (f i)) :
    ((u : ↥(B.sourceSubring O Λ ⊓ D)) : K) * ∏ i, (f i : K) ≠ (B.endpoint 1 : K) := by
  let g : Fin (n + 1) → K := Fin.cons ((u : ↥(B.sourceSubring O Λ ⊓ D)) : K)
    (fun i => (f i : K))
  have hmem : ∀ i, g i ∈ B.sourceSubring O Λ := by
    intro i
    exact Fin.cases (u : ↥(B.sourceSubring O Λ ⊓ D)).property.1
      (fun j => (f j).property.1) i
  have hout : ∀ i, g i ∉ B.sourceJunk O := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact B.intersection_unit_not_mem_junk D O hO Λ _ u.isUnit
    · exact B.intersection_irreducible_not_mem_junk D places O hO Λ hcofinal hS
        sourceRatio hratio hunits (f j) (hf j)
  simpa only [g, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using hno (n + 1) g hmem hout


/-- A concrete obstruction retained in the original source intersection. -/
structure IntersectionCertificate (D O : Subring K) (Λ : Set ℕ) : Prop where
  endpoint_mem_source : (B.endpoint 1 : K) ∈ D
  endpoint_ne_zero : (B.endpoint 1 : K) ≠ 0
  endpoint_nonunit : ¬ IsUnit (⟨B.endpoint 1, B.endpoint_mem_sourceSubring O Λ 1,
    endpoint_mem_source⟩ : ↥(B.sourceSubring O Λ ⊓ D))
  junk_atomless : ∀ x : ↥(B.sourceSubring O Λ ⊓ D), Irreducible x →
    (x : K) ∉ B.sourceJunk O
  no_associated_atomic_product : ∀ (n : ℕ) (u : (↥(B.sourceSubring O Λ ⊓ D))ˣ)
    (f : Fin n → ↥(B.sourceSubring O Λ ⊓ D)), (∀ i, Irreducible (f i)) →
    ((u : ↥(B.sourceSubring O Λ ⊓ D)) : K) * ∏ i, (f i : K) ≠ (B.endpoint 1 : K)
  not_atomic : ¬ Factorization.IsAtomicDomain ↥(B.sourceSubring O Λ ⊓ D)

/-- All fields of the witnessed intersection certificate follow from the
actual fresh-return argument and the outside-junk product obstruction. -/
theorem intersectionCertificate_of_no_factorization
    (D : Subring K) [IsFractionRing D K] (places : Set (MaximalSpectrum D))
    (O : Subring K) (hO : ∀ a : O, B.valuation (a : K) ≤ 1)
    (Λ : Set ℕ) (hcofinal : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ Λ)
    (hS : ∀ M ∈ places, B.sourceSubring O Λ ≤ sourceMaximalStalk D M)
    (sourceRatio : ℕ → D) (hratio : ∀ n, (sourceRatio n : K) = (B.ratio n : K))
    (hunits : ∀ n (M : MaximalSpectrum D), M ∉ places →
      IsUnit (sourceMaximalMap D M (sourceRatio n)))
    (hzD : (B.endpoint 1 : K) ∈ D) (hno : B.NoOutsideJunkFactorization O Λ) :
    B.IntersectionCertificate D O Λ where
  endpoint_mem_source := hzD
  endpoint_ne_zero := Subtype.coe_ne_coe.mpr (B.endpoint_ne_zero 1)
  endpoint_nonunit := (B.intersection_endpoint_nonzero_nonunit D O hO Λ hzD).2
  junk_atomless := B.intersection_irreducible_not_mem_junk D places O hO Λ hcofinal hS
    sourceRatio hratio hunits
  no_associated_atomic_product := B.intersection_endpoint_no_associated_atomic_product D
    places O hO Λ hcofinal hS sourceRatio hratio hunits hno
  not_atomic := B.not_isAtomicDomain_intersection_of_no_factorization D places O hO Λ
    hcofinal hS sourceRatio hratio hunits hzD hno

end SourceBlockData
end HereditaryAtomicity.DVRBase
