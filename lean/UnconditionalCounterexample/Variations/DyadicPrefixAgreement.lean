import UnconditionalCounterexample.Variations.DyadicPrefixEmbedding
import UnconditionalCounterexample.Variations.DyadicPreparedCoarse

/-!
# Exact comparison of finite split data with the permanent signed profile

The finite table already gives the true order at every assigned argument.
Away from those arguments the frozen field element has its forecast primary
height and zero guard order. Missing retained horizontal coordinates have
order zero as well.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open GuardSupport Univariate DyadicDeviations DiscreteOrders MixedStageSelection

variable (a : Policy) (n : ℕ) (x : (RatFunc ℚ)ˣ)

private abbrev prefixHeight (x : (RatFunc ℚ)ˣ) (c : Bool) :=
  order (HorizontalOrders.valuation (PrefixProfile.centre c)) x.val

private abbrev prefixBranch (b : Bool) := PrefixProfile.branchOrder ((driver a).assigned n)
  (table (driver a).requirements n) x.val b

private abbrev prefixHorizontal := (PrincipalProfiles.exponents x.val x.ne_zero).subtypeDomain
  (fun f => f.val ∈ ((driver a).state n).frozen ∧ ∀ c, f ≠ PrefixProfile.centre c)

theorem assigned_unique_regular : PrefixProfile.UniqueRegular ((driver a).assigned n) ((driver a).state n).role := by
  intro p hp q hq c k j hr hs
  exact (driver a).permanent_regular_unique (((driver a).role_eq_permanent p hp).symm.trans hr)
    (((driver a).role_eq_permanent q hq).symm.trans hs)

private theorem old_guard_order (p : PrimeIndex) (hp : p ∈ (driver a).assigned n) :
    PrefixProfile.branchOrder ((driver a).assigned n) (table (driver a).requirements n) x.val true p =
      order (UnivariateExtraction.guardVal (driver a).requirements p) x.val := by
  rw [PrefixProfile.branchOrder,dite_eq_left hp,table_eq_permanentSite,evaluation_order,
    ← UnivariateExtraction.eval_permanent_guard]
  unfold DyadicSplit.branchValue
  split
  · rfl
  · rename_i hn
    exact False.elim (hn (Or.inl rfl))

private theorem old_primary_order (p : PrimeIndex) (hp : p ∈ (driver a).assigned n) (r : FibreRole)
    (hr : (driver a).permanentRole p = some r) :
    PrefixProfile.branchOrder ((driver a).assigned n) (table (driver a).requirements n) x.val false p =
      order (primaryVal a p (by rw [hr]; rfl)) x.val := by
  have hb : Active (permanentSite (driver a).requirements p).paired false :=
    Or.inr (((driver a).paired_iff_role p).mpr (by simp [hr]))
  rw [PrefixProfile.branchOrder,dite_eq_left hp,table_eq_permanentSite,primaryVal,evaluation_order]
  simp only [DyadicSplit.branchValue,dite_eq_left hb]

private theorem old_regular (ex : Exterior a n x) (c k : Bool) (j : ℕ) :
    PrefixProfile.regularValue (oldSigned a n x) c k j = order (regularVal a (c,k,j)) x.val ∧
      PrefixProfile.regularGuard (oldSigned a n x) c k j =
        order (UnivariateExtraction.guardVal (driver a).requirements (regularPrime a (c,k,j))) x.val := by
  let D := driver a
  let p := regularPrime a (c,k,j)
  have hrole := regularPrime_role a (c,k,j)
  by_cases ha : p ∈ D.assigned n
  · have h := PrefixProfile.actual_regular (D.assigned n) (D.state n).role (prefixHeight x)
      (prefixBranch a n x false) (prefixBranch a n x true) (prefixHorizontal a n x)
      (assigned_unique_regular a n) ha ((D.role_eq_permanent p ha).trans hrole)
    exact ⟨h.1.trans (old_primary_order a n x p ha _ hrole),h.2.trans (old_guard_order a n x p ha)⟩
  · have hm : ∀ q ∈ D.assigned n, (D.state n).role q ≠ some (.regular c k j) := by
      intro q hq he
      have h := D.permanent_regular_unique ((D.role_eq_permanent q hq).symm.trans he) hrole
      exact ha (h ▸ hq : regularPrime a (c,k,j) ∈ D.assigned n)
    have h := PrefixProfile.missing_regular (D.assigned n) (D.state n).role (prefixHeight x)
      (prefixBranch a n x false) (prefixBranch a n x true) (prefixHorizontal a n x) hm
    refine ⟨h.1.trans (ex.primary p ha _ hrole).symm, h.2.trans (ex.guard p ha).symm⟩

private theorem old_auxiliary (k : Bool) (i : oldAux a n k) :
    ((oldSigned a n x).auxiliary k i = order (auxVal a k (includeAux a n k i)) x.val) ∧
      (oldSigned a n x).guards.auxiliary k i =
        order (UnivariateExtraction.guardVal (driver a).requirements i.val) x.val := by
  have h := PrefixProfile.actual_aux ((driver a).assigned n) ((driver a).state n).role (prefixHeight x)
      (prefixBranch a n x false) (prefixBranch a n x true) (prefixHorizontal a n x) k i
  exact ⟨h.1.trans (old_primary_order a n x i.val i.property.1 _ (includeAux a n k i).role_eq),
    h.2.trans (old_guard_order a n x i.val i.property.1)⟩

private theorem old_lone (g : oldLone a n) :
    (oldSigned a n x).guards.lone g = order (UnivariateExtraction.guardVal (driver a).requirements g.val) x.val :=
  (PrefixProfile.actual_lone ((driver a).assigned n) ((driver a).state n).role (prefixHeight x)
      (prefixBranch a n x false) (prefixBranch a n x true) (prefixHorizontal a n x) g).trans
    (old_guard_order a n x g.val g.property.1)

/-- The literal finite table, extended by zero on new supplementary labels,
recovers the entire field profile used to check the installed split. -/
theorem extend_prefix_signed (ex : Exterior a n x) :
    (prefixEmbedding a n).profile (oldSigned a n x) = signed a x := by
  let E := prefixEmbedding a n
  let b := oldSigned a n x
  apply Profile.signedValues_injective
  funext i
  rw [signed_values]
  rcases i with ⟨c⟩ | ⟨k,j⟩ | ⟨k,j⟩ | ⟨i⟩
  · rfl
  · exact (old_regular a n x ex false k j).1
  · exact (old_regular a n x ex true k j).1
  · cases i with
    | plusGuard k j => exact (old_regular a n x ex false k j).2
    | minusGuard k j => exact (old_regular a n x ex true k j).2
    | auxiliary k j | auxiliaryGuard k j =>
      by_cases hp : j.prime ∈ (driver a).assigned n
      · obtain ⟨z,rfl⟩ := includeAux_of_assigned a n k j hp
        first
        | exact (E.supplement_value b (.auxiliary k z)).trans (old_auxiliary a n x k z).1
        | exact (E.supplement_value b (.auxiliaryGuard k z)).trans (old_auxiliary a n x k z).2
      · have hnot : j ∉ Set.range (includeAux a n k) := by
          rintro ⟨w,rfl⟩
          exact hp w.property.1
        first
        | exact (Finsupp.embDomain_of_notMem_range (includeAux a n k) (b.auxiliary k) _ hnot).trans
            (ex.primary j.prime hp _ j.role_eq).symm
        | exact (Finsupp.embDomain_of_notMem_range (includeAux a n k) (b.guards.auxiliary k) _ hnot).trans
            (ex.guard j.prime hp).symm
    | loneGuard g =>
      by_cases hp : g.val ∈ (driver a).assigned n
      · obtain ⟨z,rfl⟩ := includeLone_of_assigned a n g hp
        exact (E.supplement_value b (.loneGuard z)).trans (old_lone a n x z)
      · have hnot : g ∉ Set.range E.lone := by rintro ⟨w,rfl⟩; exact hp w.property.1
        exact (Finsupp.embDomain_of_notMem_range E.lone b.guards.lone _ hnot).trans (ex.guard g.val hp).symm
    | horizontal q =>
      by_cases hq : q.val.val ∈ ((driver a).state n).frozen
      · obtain ⟨z,rfl⟩ := includeHorizontal_of_frozen a n q hq
        exact (E.supplement_value b (.horizontal z)).trans
          (PrefixProfile.horizontal_at ((driver a).assigned n) ((driver a).state n).role
            (table (driver a).requirements n) ((driver a).state n).frozen x (.inr z))
      · have hnot : q ∉ Set.range E.horizontal := by rintro ⟨w,rfl⟩; exact hq w.property.1
        exact (Finsupp.embDomain_of_notMem_range E.horizontal b.horizontal _ hnot).trans (ex.horizontal q hq).symm

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
