import UnconditionalCounterexample.Variations.DyadicConcreteRealization
import UnconditionalCounterexample.Variations.DyadicSignRigidity
import UnconditionalCounterexample.Variations.DyadicIntersectionWords

/-! # The integer conductor for intrinsic non-BF subrings of the dyadic example -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated

open Polynomial GuardSupport Univariate DyadicDeviations DiscreteOrders FieldGeneration Filter
open DyadicEscape
variable (a : Policy)

private theorem regular_columns (g : Generator) :
    columnsOfRaw (auxiliaryPrime a) (auxIndex a) (auxPositive a)
      (Finsupp.single (Emission.regularColumn g) 1) = Generator.columns (Finsupp.single g 1) := by
  classical
  cases g with
  | balanced k n =>
    rw [Emission.regularColumn,columnsOfRaw_balanced]
    refine Prod.ext (funext fun l => Finsupp.ext fun j => ?_) (Prod.ext
      (funext fun l => Finsupp.ext fun j => ?_) rfl)
    · change ((Pi.single k (Finsupp.single n (1:ℤ)) : Bool → ℕ →₀ ℤ) l) j = (Finsupp.single
        (.balanced k n) (1:ℤ) : Generator →₀ ℤ) (.balanced l j)
      by_cases h : k = l
      · subst l; simp [Finsupp.single_apply]
      · simp [h]
    · exact (Finsupp.single_eq_of_ne (by simp)).symm
  | adjacent k n =>
    rw [Emission.regularColumn,columnsOfRaw_adjacent]
    refine Prod.ext (funext fun l => Finsupp.ext fun j => ?_) (Prod.ext
      (funext fun l => Finsupp.ext fun j => ?_) rfl)
    · exact (Finsupp.single_eq_of_ne (by simp)).symm
    · change ((Pi.single k (Finsupp.single n (1:ℤ)) : Bool → ℕ →₀ ℤ) l) j = (Finsupp.single
        (.adjacent k n) (1:ℤ) : Generator →₀ ℤ) (.adjacent l j)
      by_cases h : k = l
      · subst l; simp [Finsupp.single_apply]
      · simp [h]

private def HasWords (D : Driver) (A : Subring (RatFunc ℚ)) : Prop :=
  ∀ (T : Subring A) (x : T), x ≠ 0 → ¬ Factorization.HasBoundedFactorizations x →
    ∃ h : ℕ, ∃ y : ℕ → T, ∃ s : ℕ → ℕ, ∃ w : ∀ i, RawWords.StageWord (s i) (s i+1),
      (∀ i, i < s i) ∧ Tendsto s atTop atTop ∧
      (∀ i, (w i).latestExponent ≤ h) ∧ (∀ i j, |(w i).oldExponent j| ≤ h) ∧
      ∀ i, ((y i : A) : RatFunc ℚ) = (generatorUnit D (s i)).val ^ (w i).latestExponent *
        ∏ j ∈ Finset.range (s i), (generatorUnit D j).val ^ (w i).oldExponent j

private theorem domain_hasWords : HasWords (driver a) (domain (driver a).requirements) := by
  rw [domain_eq_intersection]
  intro T x hx h
  apply intersection_bounded_words (valuation a) (signed a) (signed_values a) (auxIndex a)
    (auxSign (auxPositive a)) (signed_mass a) (signed_surjective a) (sign_units a)
    (emission a).rounds.schedule (generatorUnit (driver a)) _ T hx h
  intro g
  let t := (emission a).rounds.regularStage g
  have ht : ((driver a).actualRequest t).column = Emission.regularColumn g := (emission a).regular g
  have he := generator_translates a (signed a) (signed_values a) t 1
  rw [one_mul,ht,regular_columns] at he
  exact he

/-- Re-encode the uniformly bounded escaping words in U's exact finite
word list at their own stages. Removing a finite initial segment ensures
the stage bound exceeds all the signed exponents. -/
theorem listed_of_unbounded (T : Subring (domain (driver a).requirements)) (x : T)
    (hx : x ≠ 0) (hunbounded : ¬ Factorization.HasBoundedFactorizations x) :
    Nonempty (ListedSequence (driver a).requirements T) := by
  let R := (driver a).requirements
  obtain ⟨h,y,s,w,hstage,_,hl,ho,he⟩ := domain_hasWords a T x hx hunbounded
  let t (i : ℕ) := s (i+h)
  have ht (i : ℕ) : h ≤ t i + 1 := by have := hstage (i+h); dsimp [t]; omega
  have lift (i : ℕ) : ∃ v : ConstructionWords.Word (t i),
      (∀ j < t i, v.oldExponent j = (w (i+h)).oldExponent j) ∧
      v.latestExponent = (w (i+h)).latestExponent := by
    apply RawWords.stageWord_covers
    · intro j _
      have hj := abs_le.mp (ho (i+h) j)
      have ht' := ht i
      omega
    · exact ⟨(w (i+h)).latestExponent_bounds.1,(hl _).trans (ht i)⟩
  choose v hv hl' using lift
  refine ⟨{
    element := fun i => ⟨inclusion R ((y (i+h)).val),⟨_,(y (i+h)).property,rfl⟩⟩
    stage := t
    word := v
    bound := h
    bounded := fun i => (hl' i) ▸ hl _
    tends := tendsto_atTop_mono (fun i => Nat.le_of_lt ((Nat.le_add_right i h).trans_lt (hstage _))) tendsto_id
    expansion := ?_ }⟩
  intro i
  rw [hl' i]
  exact (he (i+h)).trans (congrArg (_ * ·) (Finset.prod_congr rfl fun j hj =>
    congrArg (_ ^ ·) (hv i j (Finset.mem_range.mp hj)).symm))

/-- Every intrinsic non-BF subring contains a positive integer multiple
of the whole dyadic domain. -/
theorem integer_conductor (T : Subring (domain (driver a).requirements))
    (hT : ¬ Factorization.IsBFDomain T) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : domain (driver a).requirements, (m : domain (driver a).requirements) * z ∈ T := by
  obtain ⟨x,hx,hu⟩ : ∃ x : T, x ≠ 0 ∧ ¬ Factorization.HasBoundedFactorizations x := by
    simpa only [Factorization.IsBFDomain,not_forall,exists_prop] using hT
  obtain ⟨L⟩ := listed_of_unbounded a T x hx hu
  obtain ⟨⟨m,hm,he⟩,h⟩ := L.integer_conductor
  exact ⟨m,hm,h m he⟩

theorem intersection_index :
    ∀ T : Subring (fullIntersection (valuation a)), ¬ Factorization.IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z : fullIntersection (valuation a), (m : fullIntersection (valuation a)) * z ∈ T := by
  rw [← domain_eq_intersection]
  exact integer_conductor a

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
