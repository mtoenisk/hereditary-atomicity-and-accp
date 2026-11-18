import UnconditionalCounterexample.StageRecursion

/-!
# The selected finite plans in the actual common infinite sequence

Transport a finite DegreePlan using only equality of predecessor raw polynomials
and predecessor normalization exponents. The chosen power, denominator powers
and degree are copied literally. Applying this to StageRecursion.Sequence keeps
all denominators and geometric test lists equal to the ones actually used by
the selected polynomial, and proves agreement with its global exponent/degree.
No independent infinite family or replacement plan is selected.
-/

namespace UnconditionalCounterexample.GlobalPlans

open Polynomial RawWords ConstructionWords StageRecursion RecursivePrefix

/-- A normalized predecessor uses only raw data and exponents from its prefix. -/
theorem normalizedFactor_congr_prefix {L : Type*} [Field L]
    (P Q : ℕ → L) (E D : ℕ → ℕ) (n : ℕ)
    (hP : ∀ j < n, P j = Q j) (hE : ∀ j < n, E j = D j)
    (j : ℕ) (hj : j < n) : normalizedFactor P E j = normalizedFactor Q D j := by
  unfold normalizedFactor
  rw [hP j hj, hE j hj]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hP i ((Finset.mem_range.mp hi).trans hj)]

/-- Transfer a finite plan along equality of the actual predecessor data.
Its chosen power, denominator exponents and degree are unchanged. -/
noncomputable def transportPlan {n : ℕ} {P Q : ℕ → ℚ[X]} {E D : ℕ → ℕ}
    (plan : DegreePlan n P E) (hP : ∀ j < n, P j = Q j) (hE : ∀ j < n, E j = D j) :
    DegreePlan n Q D := by
  have hden (e : Fin n → ℕ) : (∏ j : Fin n, P j.val ^ e j) =
      ∏ j : Fin n, Q j.val ^ e j := by
    apply Finset.prod_congr rfl
    intro j _
    rw [hP j.val j.isLt]
  refine {
    E := plan.E
    powers := plan.powers
    degree := plan.degree
    E_pos := plan.E_pos
    powers_pos := plan.powers_pos
    large_degree := plan.large_degree
    increasing := ?_
    infinity := ?_
    expand := ?_ }
  · intro j hj
    rw [← hP j hj]
    exact plan.increasing j hj
  · intro w
    rw [← hden (plan.powers w)]
    exact plan.infinity w
  · intro F w
    dsimp only
    have he := plan.expand F w
    dsimp only at he
    have hword : (∏ j ∈ Finset.range n,
        normalizedFactor (fun k => algebraMap ℚ[X] (RatFunc ℚ) (P k)) E j ^ w.oldExponent j) =
      ∏ j ∈ Finset.range n,
        normalizedFactor (fun k => algebraMap ℚ[X] (RatFunc ℚ) (Q k)) D j ^ w.oldExponent j := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [normalizedFactor_congr_prefix _ _ E D n
        (fun k hk => congrArg (algebraMap ℚ[X] (RatFunc ℚ)) (hP k hk)) hE j
        (Finset.mem_range.mp hj)]
    rw [hden (fun _ => plan.E), hden (plan.powers w), hword] at he
    exact he

theorem transportPlan_wordDen {n : ℕ} {P Q : ℕ → ℚ[X]} {E D : ℕ → ℕ}
    (plan : DegreePlan n P E) (hP : ∀ j < n, P j = Q j) (hE : ∀ j < n, E j = D j)
    (w : Word n) : (transportPlan plan hP hE).wordDen w = plan.wordDen w := by
  apply Finset.prod_congr rfl
  intro j _
  change Q j.val ^ plan.powers w j = P j.val ^ plan.powers w j
  rw [hP j.val j.isLt]

theorem transportPlan_rawDen {n : ℕ} {P Q : ℕ → ℚ[X]} {E D : ℕ → ℕ}
    (plan : DegreePlan n P E) (hP : ∀ j < n, P j = Q j) (hE : ∀ j < n, E j = D j) :
    (transportPlan plan hP hE).rawDen = plan.rawDen := by
  apply Finset.prod_congr rfl
  intro j _
  change Q j.val ^ plan.E = P j.val ^ plan.E
  rw [hP j.val j.isLt]

theorem transportPlan_tests {n : ℕ} {P Q : ℕ → ℚ[X]} {E D : ℕ → ℕ}
    (plan : DegreePlan n P E) (hP : ∀ j < n, P j = Q j) (hE : ∀ j < n, E j = D j) :
    (transportPlan plan hP hE).tests = plan.tests := by
  have hres := GeometricReservations.reservedPoints_congr_prefix
    GeometricReservations.geometricEnumeration P Q n hP
  simp only [DegreePlan.tests, transportPlan_wordDen, ← hres]

variable {R : Requirements} (s : Sequence R)

/-- The actual prefix plan interpreted in the same common infinite sequence. -/
noncomputable def globalPlan (n : ℕ) : DegreePlan n s.chain.raw s.chain.exponent :=
  transportPlan (s.selection n).plan (s.chain.rawAt_agrees n) (s.chain.exponentAt_agrees n)

@[simp] theorem globalPlan_wordDen (n : ℕ) (w : Word n) :
    (globalPlan s n).wordDen w = (s.selection n).plan.wordDen w :=
  transportPlan_wordDen _ _ _ w

@[simp] theorem globalPlan_rawDen (n : ℕ) :
    (globalPlan s n).rawDen = (s.selection n).plan.rawDen :=
  transportPlan_rawDen _ _ _

@[simp] theorem globalPlan_tests (n : ℕ) :
    (globalPlan s n).tests = (s.selection n).plan.tests :=
  transportPlan_tests _ _ _

theorem globalRaw_eq_selection (n : ℕ) : s.chain.raw n = (s.selection n).raw := by
  rw [s.chain.raw_eq_selected n, s.consistent n]
  rfl

theorem globalPlan_E (n : ℕ) : (globalPlan s n).E = s.chain.exponent n := by
  rw [s.chain.exponent_eq_selected n, s.consistent n]
  rfl

theorem globalPlan_degree (n : ℕ) : (s.chain.raw n).natDegree = (globalPlan s n).degree := by
  rw [globalRaw_eq_selection]
  exact (s.selection n).raw_degree

theorem global_raw_tests (n : ℕ) : ∀ t ∈ (globalPlan s n).tests,
    t.Holds ((s.chain.raw n).map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
  rw [globalPlan_tests, globalRaw_eq_selection]
  exact (s.selection n).raw_tests

end UnconditionalCounterexample.GlobalPlans
