import UnconditionalCounterexample.Variations.UnivariateSelection

/-!
# Recovery and all-word transfer for prefix-dependent prime roles

The global rational hull, ordinary derivatives and scaled transfer identities
are calculated from the selected polynomial sequence and its permanent sites.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.Univariate

open Polynomial Filter GuardSupport PrimaryChoices CombinedGuardStep ConstructionWords
open RecursivePrefix MixedStageSelection MixedWordTransfer LocalAlgebra

variable (R : Requirements)

/-- Use the same exponents, word denominators and geometric tests after transporting
the finite plan to the actual infinite numerator sequence. -/
def globalPlan (n : ℕ) : DegreePlan n (chain R).raw (chain R).exponent :=
  GlobalPlans.transportPlan (selection R n).plan ((chain R).rawAt_agrees n)
    ((chain R).exponentAt_agrees n)

theorem globalPlan_wordDen (n : ℕ) (w : Word n) :
    (globalPlan R n).wordDen w = (selection R n).plan.wordDen w :=
  GlobalPlans.transportPlan_wordDen _ _ _ w

theorem raw_eq_selection (n : ℕ) : (chain R).raw n = (selection R n).raw :=
  (chain R).raw_eq_selected n

theorem degree_above (n : ℕ) :
    R.degreeFloor ((chain R).approx n) (table R n) < ((chain R).raw n).natDegree := by
  rw [raw_eq_selection, Selection.raw_degree]
  exact (selection R n).degree_above

/-- At a freezing stage, check the prefix and include the degree in the floor.
Increasing raw degrees exclude that polynomial permanently from the poles. -/
theorem retained_after_freezing (n : ℕ) (f : ℚ[X])
    (hprefix : ∀ j : Fin n, ((chain R).approx n).raw j ≠ f)
    (hfloor : f.natDegree ≤ R.degreeFloor ((chain R).approx n) (table R n)) :
    f ∉ Set.range (chain R).raw := by
  rintro ⟨j, he⟩
  by_cases hj : j < n
  · exact hprefix ⟨j, hj⟩ (((chain R).raw_agrees n ⟨j, hj⟩).trans he)
  · have hlt := (hfloor.trans_lt (degree_above R n)).trans_le
      ((chain R).raw_degree_strict.monotone (Nat.le_of_not_gt hj))
    exact (ne_of_lt hlt) (congrArg Polynomial.natDegree he.symm)

theorem hull_eq_top_of_sequence (T : Subring (PoleAlgebra.generated (Set.range (chain R).raw)))
    (y : ℕ → T) (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, Word (stage i))
    (hword : ∀ i, ((y i : PoleAlgebra.generated (Set.range (chain R).raw)) : RatFunc ℚ) =
      ScheduledRecovery.generators (chain R).raw (chain R).exponent (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i),
          ScheduledRecovery.generators (chain R).raw (chain R).exponent j ^ (w i).oldExponent j)) :
    RationalHull.hull T = ⊤ := by
  apply ConstructionRecovery.hull_eq_top_of_coherent_plans (chain R).raw (chain R).exponent
    (globalPlan R) _ _ (chain R).raw_irreducible _ 0 _ T y stage hstage w hword
  · intro n
    exact ((chain R).exponent_eq_selected n).symm
  · intro n
    rw [raw_eq_selection]
    exact (selection R n).raw_degree
  · intro n t ht
    rw [raw_eq_selection]
    exact (selection R n).raw_tests t (by
      rwa [← GlobalPlans.transportPlan_tests (selection R n).plan
        ((chain R).rawAt_agrees n) ((chain R).exponentAt_agrees n)])
  · intro j
    simp only [eval₂_at_zero]
    exact (map_ne_zero_iff (algebraMap ℚ (AlgebraicClosure ℚ))
      (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mpr ((chain R).raw_constant_ne_zero j)

private abbrev assigned (n : ℕ) := ((chain R).approx n).state.assignment.primes

theorem assigned_mono : Monotone (assigned R) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (selection R n).toNext.assigned_subset

theorem table_agrees {m n : ℕ} (hmn : m ≤ n) (p : PrimeIndex)
    (hm : p ∈ assigned R m) (hn : p ∈ assigned R n) :
    table R n p hn = table R m p hm := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n h ih =>
    have hmem := assigned_mono R h hm
    exact (table_persistent R n p hmem hn).trans (ih hmem)

private theorem assigned_at (p : PrimeIndex) : p ∈ assigned R p.val :=
  ((chain R).approx p.val).state.covered ((GuardStages.mem_primesThrough _ _).mpr
    ((chain R).approx p.val).stage_cutoff)

def permanentSite (p : PrimeIndex) : Site p := table R p.val p (assigned_at R p)

theorem table_eq_permanentSite (n : ℕ) (p : PrimeIndex) (h : p ∈ assigned R n) :
    table R n p h = permanentSite R p := by
  rcases le_total n p.val with hle | hle
  · exact (table_agrees R hle p h (assigned_at R p)).symm
  · exact table_agrees R hle p (assigned_at R p) h

abbrev selectionSite (n : ℕ) (j : (selection R n).batch.indices) : Site (primes j.val) :=
  siteAt (selection R n).batch
    (extend R ((chain R).approx n) (table R n) (selection R n).batch) j

theorem selectionSite_eq (n : ℕ) (j : (selection R n).batch.indices) :
    selectionSite R n j = permanentSite R (primes j.val) :=
  table_eq_permanentSite R (n+1) (primes j.val)
    ((selection R n).batch.processed_subset_assigned
      (((selection R n).batch.mem_indices _).mp j.property))

theorem eventually_mem_indices (j : ℕ) : ∀ᶠ n in atTop, j ∈ (selection R n).batch.indices := by
  filter_upwards [eventually_ge_atTop (primes j).val] with n hn
  apply ((selection R n).batch.mem_indices _).mpr
  apply (selection R n).batch.covered
  exact (GuardStages.mem_primesThrough _ _).mpr
    (hn.trans ((Nat.le_succ n).trans (selection R n).toNext.stage_cutoff))

/-- Guard values in the site table are literally those of the underlying prime
batch chain. Thus the logarithmic finite-support theorem applies unchanged. -/
theorem table_guard_eq (n : ℕ) (p : PrimeIndex) (hp : p ∈ assigned R n) :
    (table R n p hp).guard = (((chain R).approx n).state.assignment.guard p hp).value := by
  induction n with
  | zero => exact False.elim ((Finset.notMem_empty p) hp)
  | succ n ih =>
    let sel := selection R n
    by_cases h : p ∈ assigned R n
    · exact (congrArg Site.guard (table_persistent R n p h hp)).trans
        ((ih h).trans (congrArg PaperGuardStages.Guard.value (sel.progress.old_guard p h hp).symm))
    · change (extend R ((chain R).approx n) (table R n) sel.batch p hp).guard =
        (sel.batch.assigned.guard p hp).value
      simp only [extend, h, ↓reduceDIte]

theorem permanent_guard_eq (p : PrimeIndex) :
    (permanentSite R p).guard = (chain R).guardChain.value p := by
  have h := (chain R).guardChain.exhaustive p
  obtain ⟨m, hm⟩ := h
  change p ∈ assigned R (m+1) at hm
  exact ((congrArg Site.guard (table_eq_permanentSite R (m+1) p hm)).symm).trans
    ((table_guard_eq R (m+1) p hm).trans ((chain R).guardChain.value_agrees m p hm))

private theorem raw_map (n : ℕ) (j : (selection R n).batch.indices) :
    ((selection R n).raw).map (algebraMap ℚ ℚ_[(primes j.val).val]) =
    ShiftedEisenstein.monicFamily ((selection R n).plan.degree - 1)
      ((selection R n).constant : ℚ_[(primes j.val).val])
      (fun l => ((selection R n).choice.coeff l : ℚ_[(primes j.val).val])) := by
  have hcast (r : ℚ) : algebraMap ℚ ℚ_[(primes j.val).val] r = (r : ℚ_[(primes j.val).val]) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℚ_[(primes j.val).val]) r
  simp only [Selection.raw, ShiftedEisenstein.monicFamily_map, hcast]

set_option backward.isDefEq.respectTransparency false in
/-- Every late word in the actual stage list has a large derivative at every active
argument and the two-term transfer identity in the scaled polynomial ring. -/
theorem eventually_all_word_estimates (j s : ℕ) :
    ∀ᶠ n in atTop, ∀ w : Word n,
      (∀ b, Active (permanentSite R (primes j)).paired b → (LocalInterpolation.wordDerivative
        (((chain R).raw n).map (algebraMap ℚ ℚ_[(primes j).val]))
        (((globalPlan R n).wordDen w).map (algebraMap ℚ ℚ_[(primes j).val]))
        w.latestExponent ((permanentSite R (primes j)).branch b)).valuation < -((n+1 : ℕ) : ℤ)) ∧
      ∃ U V : padicScaledPolynomialRing (primes j).val s,
        (RatFunc.C ((primes j).val : ℚ_[(primes j).val]) ^ (2*s) *
          vanishing (permanentSite R (primes j)).paired (permanentSite R (primes j)).branch)
          ^ w.latestExponent =
          RatFunc.C ((primes j).val : ℚ_[(primes j).val]) ^ (n+1) *
            ((U : RatFunc ℚ_[(primes j).val]) + (V : RatFunc ℚ_[(primes j).val]) *
              ((((chain R).raw n).map (algebraMap ℚ ℚ_[(primes j).val]) : RatFunc ℚ_[(primes j).val])
                ^ w.latestExponent /
                (((globalPlan R n).wordDen w).map (algebraMap ℚ ℚ_[(primes j).val]) :
                  RatFunc ℚ_[(primes j).val]))) := by
  filter_upwards [eventually_mem_indices R j, eventually_ge_atTop s] with n hj hs
  intro w
  let i : (selection R n).batch.indices := ⟨j, hj⟩
  have heq : selectionSite R n i = permanentSite R (primes j) := selectionSite_eq R n i
  rw [← heq, raw_eq_selection, raw_map R n i, globalPlan_wordDen]
  let sel := selection R n
  have hlocal := sel.choice.witnesses.2.2.2.2.2.1 i
  constructor
  · intro b hb
    exact hlocal.2.2.1 w (Finset.mem_univ w) b hb
  · have hden : sel.plan.wordDen w ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k _
      exact pow_ne_zero _ (((chain R).approx n).rawAt_monic k.val k.isLt).ne_zero
    exact signed_transfer sel.batch.primeAt (fun _ => Fact.out) sel.choice.N
      (primes j).val (selectionSite R n i).paired (sel.plan.degree - 1) (n+1)
      (by have := sel.plan.large_degree; omega)
      (fun l => (sel.choice.coeff l : ℚ_[(primes j).val])) (selectionSite R n i).branch _ _ _
      (fun b hb => ((selectionSite R n i).branch_transcendental b hb).ne_zero)
      (fun b _ => (selectionSite R n i).branch_integral b)
      Finset.univ (fun v => (sel.plan.wordDen v).map (algebraMap ℚ ℚ_[(primes j).val]))
      RawWords.StageWord.latestExponent hlocal.1 hlocal.2 s (by omega) w (Finset.mem_univ w)
      w.latestExponent_bounds.1 ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ_[(primes j).val]).injective).mpr hden)

end UnconditionalCounterexample.Variations.Univariate
