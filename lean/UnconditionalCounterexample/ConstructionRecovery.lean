import UnconditionalCounterexample.ConstructionWords
import UnconditionalCounterexample.GlobalPlans
import UnconditionalCounterexample.ScheduledRecovery

/-!
# Generic-fibre recovery for the actual common construction

The actual selected DegreePlans supply exact predecessor denominators,
normalized-word identities, infinity bounds and geometric tests. GlobalPlans
transports these to the same common infinite sequence; its nonzero constants
retain the point zero. Thus one actual escaping listed-word sequence in T
recovers Q[T]. Integer clearing then pulls back along the literal injective
inclusion to the original subring, without asserting a uniform conductor.
-/

namespace UnconditionalCounterexample.ConstructionRecovery

open Polynomial Filter RawWords ConstructionWords

/-- Extend the plan's finite predecessor exponents by zero off its prefix. -/
def extendedPowers {n : ℕ} {F : ℕ → ℚ[X]} {E : ℕ → ℕ}
    (plan : DegreePlan n F E) (w : Word n) (j : ℕ) : ℕ :=
  if hj : j < n then plan.powers w ⟨j, hj⟩ else 0

theorem extendedPowers_pos {n : ℕ} {F : ℕ → ℚ[X]} {E : ℕ → ℕ}
    (plan : DegreePlan n F E) (w : Word n) (j : ℕ) (hj : j < n) :
    0 < extendedPowers plan w j := by
  simpa only [extendedPowers, dite_eq_left hj] using plan.powers_pos w ⟨j, hj⟩

theorem oldDenominator_eq_wordDen {n : ℕ} {F : ℕ → ℚ[X]} {E : ℕ → ℕ}
    (plan : DegreePlan n F E) (w : Word n) :
    WordGeometry.oldDenominator F n (extendedPowers plan w) = plan.wordDen w := by
  unfold WordGeometry.oldDenominator DegreePlan.wordDen
  rw [← Fin.prod_univ_eq_prod_range (fun j => F j ^ extendedPowers plan w j) n]
  apply Finset.prod_congr rfl
  intro j _
  simp only [extendedPowers, dite_eq_left j.isLt]

/-- The plan's universal raw expansion is the literal global normalized word
identity once the selected normalization power agrees with the plan. -/
theorem global_word_eq_fraction (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (n : ℕ)
    (plan : DegreePlan n F E) (hE : plan.E = E n) (w : Word n) :
    ScheduledRecovery.generators F E n ^ w.latestExponent *
      (∏ j ∈ Finset.range n, ScheduledRecovery.generators F E j ^ w.oldExponent j) =
      (algebraMap ℚ[X] (RatFunc ℚ) (F n)) ^ w.latestExponent /
        algebraMap ℚ[X] (RatFunc ℚ) (WordGeometry.oldDenominator F n (extendedPowers plan w)) := by
  have he := plan.expand (F n) w
  dsimp only at he
  rw [Fin.prod_univ_eq_prod_range (fun j => F j ^ plan.E) n] at he
  rw [oldDenominator_eq_wordDen]
  simpa only [ScheduledRecovery.generators, normalizedFactor, DegreePlan.wordDen,
    map_prod, map_pow, hE] using he

/-- Coherent choices of the actual construction plans supply every global
polynomial hypothesis of ScheduledRecovery. -/
theorem hull_eq_top_of_coherent_plans
    (F : ℕ → ℚ[X]) (E : ℕ → ℕ) (plan : ∀ n, DegreePlan n F E)
    (hE : ∀ n, (plan n).E = E n)
    (hdegree : ∀ n, (F n).natDegree = (plan n).degree)
    (hF : ∀ n, Irreducible (F n))
    (htests : ∀ n t, t ∈ (plan n).tests →
      t.Holds ((F n).map (algebraMap ℚ (AlgebraicClosure ℚ))))
    (α₀ : AlgebraicClosure ℚ)
    (hα₀ : ∀ j, (F j).eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) α₀ ≠ 0)
    (T : Subring (PoleAlgebra.generated (Set.range F)))
    (y : ℕ → T) (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, Word (stage i))
    (hword : ∀ i, ((y i : PoleAlgebra.generated (Set.range F)) : RatFunc ℚ) =
      ScheduledRecovery.generators F E (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i), ScheduledRecovery.generators F E j ^ (w i).oldExponent j)) :
    RationalHull.hull T = ⊤ := by
  have hinc : StrictMono (fun n => (F n).natDegree) := by
    intro i j hij
    change (F i).natDegree < (F j).natDegree
    rw [hdegree j]
    exact (plan j).increasing i hij
  apply ScheduledRecovery.hull_eq_top_of_listed_sequence (AlgebraicClosure ℚ)
    GeometricReservations.geometricEnumeration GeometricReservations.geometricEnumeration_surjective
    F E hF hinc (fun n => extendedPowers (plan n))
    (fun n => extendedPowers_pos (plan n))
    (fun n => global_word_eq_fraction F E n (plan n) (hE n))
    ?_ ?_ α₀ hα₀ T y stage hstage w hword
  · intro n w
    rw [oldDenominator_eq_wordDen, hdegree n]
    exact (plan n).infinity w
  · intro n t ht
    apply htests n t
    simpa only [DegreePlan.tests, oldDenominator_eq_wordDen] using ht

/-- The common sequence already carries every coherent plan and successful
finite test. Its nonzero constant coefficients make the point zero retained. -/
theorem hull_eq_top_of_sequence {R : StageRecursion.Requirements}
    (s : StageRecursion.Sequence R)
    (T : Subring (PoleAlgebra.generated (Set.range s.chain.raw)))
    (y : ℕ → T) (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, Word (stage i))
    (hword : ∀ i, ((y i : PoleAlgebra.generated (Set.range s.chain.raw)) : RatFunc ℚ) =
      ScheduledRecovery.generators s.chain.raw s.chain.exponent (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i),
          ScheduledRecovery.generators s.chain.raw s.chain.exponent j ^ (w i).oldExponent j)) :
    RationalHull.hull T = ⊤ := by
  apply hull_eq_top_of_coherent_plans s.chain.raw s.chain.exponent (GlobalPlans.globalPlan s)
    (GlobalPlans.globalPlan_E s) (GlobalPlans.globalPlan_degree s) s.chain.raw_irreducible
    (GlobalPlans.global_raw_tests s) 0 ?_ T y stage hstage w hword
  intro j
  simp only [eval₂_at_zero]
  exact (map_ne_zero_iff (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mpr (s.chain.raw_constant_ne_zero j)

/-- Integer clearing in the generic fibre returns to the original subring
along its actual injective ring inclusion. The integer may depend on x. -/
theorem exists_nat_mul_mem_of_mapped_hull_eq_top
    {D B : Type*} [CommRing D] [CommRing B] [Algebra ℚ B]
    (f : D →+* B) (hf : Function.Injective f) (T : Subring D)
    (hT : RationalHull.hull (T.map f) = ⊤) (x : D) :
    ∃ n : ℕ, 0 < n ∧ (n : D) * x ∈ T := by
  obtain ⟨n, hn, hnx⟩ := RationalHull.exists_nat_mul_mem_of_hull_eq_top (T.map f) hT (f x)
  obtain ⟨z, hz, heq⟩ := hnx
  have he : z = (n : D) * x := hf (by simpa only [map_mul, map_natCast] using heq)
  exact ⟨n, hn, he ▸ hz⟩

/-- The actual listed sequence in the image of T clears every original-domain
element by a positive integer, including the coordinate when it belongs to D. -/
theorem exists_nat_mul_mem_of_sequence {R : StageRecursion.Requirements}
    (s : StageRecursion.Sequence R)
    (D : Subring (PoleAlgebra.generated (Set.range s.chain.raw))) (T : Subring D)
    (y : ℕ → T.map D.subtype) (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, Word (stage i))
    (hword : ∀ i, ((y i : PoleAlgebra.generated (Set.range s.chain.raw)) : RatFunc ℚ) =
      ScheduledRecovery.generators s.chain.raw s.chain.exponent (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i),
          ScheduledRecovery.generators s.chain.raw s.chain.exponent j ^ (w i).oldExponent j))
    (x : D) : ∃ n : ℕ, 0 < n ∧ (n : D) * x ∈ T := by
  apply exists_nat_mul_mem_of_mapped_hull_eq_top D.subtype Subtype.val_injective T
    (hull_eq_top_of_sequence s (T.map D.subtype) y stage hstage w hword) x

end UnconditionalCounterexample.ConstructionRecovery
