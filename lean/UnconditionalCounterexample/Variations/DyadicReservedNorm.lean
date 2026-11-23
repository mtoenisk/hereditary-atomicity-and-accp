import UnconditionalCounterexample.Variations.DyadicGeneratorColumns
import UnconditionalCounterexample.Variations.DyadicSplitInstruction

/-!
# Computing target norms on the previously classified conductor fibres

At a prime dividing the split modulus all its points belong to the same old
channel. Evaluating the signed allocation at that channel computes the norm
of the earlier rational factor before the reserved raw has been selected.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated

open GuardSupport PrimaryChoices Univariate DyadicDeviations DiscreteOrders MixedStageSelection
open DyadicProfiles (Site)

variable (a : Policy)

/-- Lone primes and channel-zero primes are assigned to the left factor. -/
def splitChannel : Option FibreRole → Bool
  | none => false
  | some r => r.channel

private def guardChannel {J : Bool → Type*} {G : Type*} : GuardIndex J G → Bool
  | .inl (k,_) | .inr (.inl (k,_)) | .inr (.inr (.inl ⟨k,_⟩)) => k
  | .inr (.inr (.inr _)) => false

private theorem old_guard (M : ℕ) (g : GuardIndex (Aux a) (Lone a)) :
    OldFibre (H := Horiz a) M (guardChannel g) (guardSite g) := by
  rcases g with ⟨k,j⟩ | ⟨k,j⟩ | ⟨k,j⟩ | g <;> exact .supplementary _ rfl

private theorem ofPrime_channel (p : PrimeIndex) :
    guardChannel (ofPrime a p) = splitChannel ((driver a).permanentRole p) := by
  unfold ofPrime
  split <;> rename_i he <;> exact (congrArg splitChannel he).symm

/-- Identify the actual active argument with its old full-profile coordinate.
Only regular primary arguments require the pre-reservation index bound.
-/
theorem exists_old_coordinate (p : PrimeIndex) (b : Bool) (M : ℕ)
    (hb : Active (permanentSite (driver a).requirements p).paired b)
    (hearly : ∀ c k j, (driver a).permanentRole p = some (.regular c k j) → j < M) :
    ∃ i : Coordinates a, OldFibre M (splitChannel ((driver a).permanentRole p)) i ∧
      ∀ y : (RatFunc ℚ)ˣ, order (valuation a i) y.val =
        ((permanentSite (driver a).requirements p).evaluate b hb y.val).valuation := by
  let D := driver a
  cases b with
  | true =>
    refine ⟨guardSite (ofPrime a p), ofPrime_channel a p ▸ old_guard a M _, ?_⟩
    intro y
    rw [valuation_guard]
    change order (UnivariateExtraction.guardVal D.requirements (toPrime a (ofPrime a p))) y.val = _
    rw [toPrime_ofPrime,evaluation_order,← UnivariateExtraction.eval_permanent_guard]
    rfl
  | false =>
    have hp : (D.permanentRole p).isSome := (D.paired_iff_role p).mp (hb.resolve_left (by decide))
    cases hr : D.permanentRole p with
    | none => simp [hr] at hp
    | some r =>
      cases r with
      | regular c k j =>
        have hi := hearly _ _ _ hr
        have he : regularPrime a (c,k,j) = p := (regular_exists_unique a _).unique (regularPrime_role a _) hr
        cases c
        · refine ⟨.plus k j, ?_, ?_⟩
          · exact .plus hi
          · intro y
            change order (regularVal a (false,k,j)) y.val = _
            subst p
            exact evaluation_order _ _
        · refine ⟨.minus k j, ?_, ?_⟩
          · exact .minus hi
          · intro y
            change order (regularVal a (true,k,j)) y.val = _
            subst p
            exact evaluation_order _ _
      | auxiliary k j f =>
        let t : Aux a k := ⟨p,j,f,hr⟩
        refine ⟨.other (.auxiliary k t),?_,fun y => evaluation_order _ y⟩
        exact .supplementary _ rfl

private theorem balanced_zero_at_old (p : Profile (Aux a) (Lone a) (Horiz a)) (M : ℕ) (k : Bool)
    {i : Coordinates a} (h : OldFibre M k i) :
    rowChange (auxiliaryPrime a) (auxIndex a) (auxPositive a) (auxSign (auxPositive a)) p i
      (Finsupp.single (.balanced true M) 1) = 0 := by
  rw [rowChange_balanced _ _ _ (fun c k i => regularPrime a (c,k,i))]
  cases h with
  | plus hn | minus hn =>
    simp [rawRow,RawColumn.atPrimary,Ne.symm (Nat.ne_of_lt hn)]
  | supplementary i _ => cases i <;> rfl

/-- The computed prefix order agrees with the full signed allocation at any
old point, using only verified orders of earlier raws and the zero formal row
of the reserved balanced column. -/
theorem prefix_order_of_split (signed : (RatFunc ℚ)ˣ → Profile (Aux a) (Lone a) (Horiz a))
    (hval : ∀ y i, (signed y).signedValues i = order (valuation a i) y.val)
    (I : SplitInstruction) (n M : ℕ) (x : (RatFunc ℚ)ˣ) (u v : Profile (Aux a) (Lone a) (Horiz a))
    (split : SplitAt (auxIndex a) (auxSign (auxPositive a)) (signed x) u v M)
    (ht : (signed I.coarse).translate (auxIndex a) (auxSign (auxPositive a))
      (columnsOfRaw (auxiliaryPrime a) (auxIndex a) (auxPositive a) I.coefficients) = u)
    (hs : I.coefficients.support ⊆ (Finset.range (n+1)).image (fun j => ((driver a).actualRequest j).column))
    (hlast : ((driver a).actualRequest n).column = .balanced true M)
    {k : Bool} {i : Coordinates a} (hi : OldFibre M k i) :
    order (valuation a i) (I.prefix ((driver a).state n) ((chain (driver a).requirements).approx n)).val =
      if k = false then order (valuation a i) x.val else 0 := by
  let D := driver a
  rw [D.instruction_prefix_eq]
  rw [← hval x i,← split.old_fibre _ _ hi,← ht]
  apply prefix_order_of_zero_row (auxiliaryPrime a) (auxIndex a) (auxPositive a)
    (auxSign (auxPositive a)) (signed I.coarse) i (valuation a i) _ I.coarse I.coefficients
    (fun j => (D.actualRequest j).column) hs (column_injective a).injOn (hval I.coarse i).symm
  · intro j hj
    rw [(chain D.requirements).generators_agree n j hj]
    have hv := generator_order a j i
    obtain ⟨g,hg⟩ := column_is_basis a j
    have hr := rowChange_eq_rawRow (auxiliaryPrime a) (auxIndex a) (auxPositive a)
      (fun c k j => regularPrime a (c,k,j)) (signed I.coarse) g i
    dsimp only at hr
    rw [hg] at hr
    exact hv.trans hr.symm
  · rw [hlast]
    exact balanced_zero_at_old a _ M k hi

/-- The finite allocation of the whole modulus fibre makes the preselected
factor's norm exactly the target norm on every one of its active branches. -/
theorem prefix_target_norm (signed : (RatFunc ℚ)ˣ → Profile (Aux a) (Lone a) (Horiz a))
    (hval : ∀ y i, (signed y).signedValues i = order (valuation a i) y.val)
    (I : SplitInstruction) (n M : ℕ) (x : (RatFunc ℚ)ˣ) (u v : Profile (Aux a) (Lone a) (Horiz a))
    (split : SplitAt (auxIndex a) (auxSign (auxPositive a)) (signed x) u v M)
    (ht : (signed I.coarse).translate (auxIndex a) (auxSign (auxPositive a))
      (columnsOfRaw (auxiliaryPrime a) (auxIndex a) (auxPositive a) I.coefficients) = u)
    (hs : I.coefficients.support ⊆ (Finset.range (n+1)).image (fun j => ((driver a).actualRequest j).column))
    (hlast : ((driver a).actualRequest n).column = .balanced true M)
    (p : PrimeIndex) (b : Bool) (hb : Active (permanentSite (driver a).requirements p).paired b)
    (hearly : ∀ c k j, (driver a).permanentRole p = some (.regular c k j) → j < M)
    (hfirst : I.first p.val = ((driver a).permanentRole p).elim true (fun q => !q.channel)) :
    let D := driver a; let φ := (permanentSite D.requirements p).evaluate b hb
    ‖φ (I.prefix (D.state n) ((chain D.requirements).approx n)).val‖ =
      if I.first p.val then ‖φ x.val‖ else 1 := by
  let D := driver a
  let φ := (permanentSite D.requirements p).evaluate b hb
  let y := I.prefix (D.state n) ((chain D.requirements).approx n)
  obtain ⟨i,hi,hcoord⟩ := exists_old_coordinate a p b M hb hearly
  have he := prefix_order_of_split a signed hval I n M x u v split ht hs hlast hi
  rw [hcoord y,hcoord x] at he
  have hbool : I.first p.val = !(splitChannel (D.permanentRole p)) := by
    rw [hfirst]
    cases D.permanentRole p <;> rfl
  change ‖φ y.val‖ = if I.first p.val then ‖φ x.val‖ else 1
  rw [hbool,Padic.norm_eq_zpow_neg_valuation ((map_ne_zero φ).mpr y.ne_zero),
    show (φ y.val).valuation = _ from he]
  cases splitChannel (D.permanentRole p)
  · simp [Padic.norm_eq_zpow_neg_valuation ((map_ne_zero φ).mpr x.ne_zero)]
    rfl
  · simp

/-- Classification before allocation of the reserved index forces the
selector to request order zero at every already-classified primary. -/
theorem reserved_primary_zero (n M : ℕ) (hlast : ((driver a).actualRequest n).column = .balanced true M)
    (j : (selection (driver a).requirements n).batch.indices)
    (hearly : ∀ c k i, (driver a).permanentRole (primes j.val) = some (.regular c k i) → i < M) :
    ((driver a).actualRequest n).column.atPrimary (primes j.val) (((driver a).actualRequest n).nextRole (primes j.val)) = 0 := by
  let D := driver a
  have hp : primes j.val ∈ D.assigned (n+1) :=
    (selection D.requirements n).batch.processed_subset_assigned
      (((selection D.requirements n).batch.mem_indices _).mp j.property)
  have he := D.role_eq_permanent (primes j.val) hp
  rw [D.state_succ] at he
  change (D.actualRequest n).nextRole (primes j.val) = D.permanentRole (primes j.val) at he
  rw [hlast,he]
  apply balanced_atPrimary_zero
  intro c hc
  exact (Nat.lt_irrefl M) (hearly c true M hc)

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
