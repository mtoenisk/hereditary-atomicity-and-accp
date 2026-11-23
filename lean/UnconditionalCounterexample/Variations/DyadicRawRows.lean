import UnconditionalCounterexample.Variations.DyadicSplitCoefficients
import UnconditionalCounterexample.Variations.DyadicLedgerValues

/-!
# The entries of a dyadic raw in the formal profile and on the prime fibres

The signed columns use positive and negative regular fibres and signed
auxiliary corrections. This calculation identifies each entry with the
actual integer target on the ledger, including the coefficient two on the
successor of an adjacent column.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger
open DyadicDeviations DyadicEscape GuardSupport
open DyadicProfiles (Site)

variable {J : Bool → Type*} {G H : Type*}
    (prime : (Σ k, J k) ↪ PrimeIndex) (index : (k : Bool) → J k → ℕ)
    (positive : (k : Bool) → J k → Bool)

def auxSign (k : Bool) (j : J k) : ℤ := if positive k j then 1 else -1

theorem columnsOfRaw_balanced (k : Bool) (n : ℕ) :
    columnsOfRaw prime index positive (Finsupp.single (.balanced k n) 1) =
      (Pi.single k (Finsupp.single n 1),0,0) := by
  classical
  apply Prod.ext
  · funext l
    ext m
    change (Finsupp.single (.balanced k n) (1 : ℤ) : RawColumn →₀ ℤ) (.balanced l m) = _
    by_cases hk : k = l
    · subst l
      simp [Finsupp.single_apply]
    · simp [hk]
  · apply Prod.ext <;> funext l <;> ext i <;> exact Finsupp.single_eq_of_ne (by simp)

theorem columnsOfRaw_adjacent (k : Bool) (n : ℕ) :
    columnsOfRaw prime index positive (Finsupp.single (.adjacent k n) 1) =
      (0,Pi.single k (Finsupp.single n 1),0) := by
  classical
  apply Prod.ext
  · funext l; ext m; exact Finsupp.single_eq_of_ne (by simp)
  apply Prod.ext
  · funext l
    ext m
    change (Finsupp.single (.adjacent k n) (1 : ℤ) : RawColumn →₀ ℤ) (.adjacent l m) = _
    by_cases hk : k = l
    · subst l
      simp [Finsupp.single_apply]
    · simp [hk]
  · funext l; ext j; exact Finsupp.single_eq_of_ne (by simp)

theorem columnsOfRaw_auxiliary (k : Bool) (j : J k) :
    columnsOfRaw prime index positive
      (Finsupp.single (.auxiliary (prime ⟨k,j⟩) k (index k j) (positive k j)) 1) =
      (0,0,Pi.single k (Finsupp.single j 1)) := by
  classical
  apply Prod.ext
  · funext l; ext n; exact Finsupp.single_eq_of_ne (by simp)
  apply Prod.ext
  · funext l; ext n; exact Finsupp.single_eq_of_ne (by simp)
  funext l
  ext b
  change (Finsupp.single (.auxiliary (prime ⟨k,j⟩) k (index k j) (positive k j)) (1 : ℤ) : RawColumn →₀ ℤ)
    (.auxiliary (prime ⟨l,b⟩) l (index l b) (positive l b)) = _
  by_cases hk : k = l
  · subst l
    by_cases hj : j = b
    · subst b; simp
    · have hn : prime ⟨k,j⟩ ≠ prime ⟨k,b⟩ := fun h => hj (eq_of_heq (Sigma.mk.inj_iff.mp (prime.injective h)).2)
      simp [hn, hj]
  · simp [hk]

/-- The corresponding integer order on actual primary fibres. The raw is
a unit on horizontal, centre, ordinary guard and lone-guard coordinates. -/
def rawRow (regular : Bool → Bool → ℕ → PrimeIndex) (c : RawColumn) :
    Site (Supplement J G H) → ℤ
  | .plus k n => c.atPrimary (regular false k n) (some (.regular false k n))
  | .minus k n => c.atPrimary (regular true k n) (some (.regular true k n))
  | .other (.auxiliary k j) =>
    c.atPrimary (prime ⟨k,j⟩) (some (.auxiliary k (index k j) (positive k j)))
  | _ => 0

private theorem adjacent_single_apply (i n : ℕ) :
    DyadicColumns.adjacent (Finsupp.single i 1) n =
      if n = i then -1 else if n = i+1 then 2 else 0 := by
  classical
  cases n with
  | zero =>
    rw [DyadicColumns.adjacent_zero]
    cases i <;> simp
  | succ n =>
    rw [DyadicColumns.adjacent_succ]
    by_cases h : i = n
    · subst i; simp
    · by_cases hs : i = n+1
      · subst i; simp
      · simp [Ne.symm hs,Ne.symm h]

private theorem transfer_single_apply (k : Bool) (a : J k) (n : ℕ) :
    DyadicColumns.auxiliaryTransfer (index k) (auxSign positive k) (Finsupp.single a 1) n =
      if index k a = n then auxSign positive k a else 0 := by
  simp [DyadicColumns.auxiliaryTransfer,Finsupp.single_apply]

variable (regular : Bool → Bool → ℕ → PrimeIndex) (p : Profile J G H)

theorem rowChange_balanced (k : Bool) (n : ℕ) (i : Site (Supplement J G H)) :
    rowChange prime index positive (auxSign positive) p i (Finsupp.single (.balanced k n) 1) =
      rawRow prime index positive regular (.balanced k n) i := by
  classical
  change (p.translate index _ (columnsOfRaw prime index positive _)).signedValues i - _ = _
  rw [columnsOfRaw_balanced]
  rcases i with ⟨c⟩ | ⟨l,m⟩ | ⟨l,m⟩ | ⟨j⟩
  · simp [Profile.signedValues,Profile.translate,Profile.addColumns,rawRow]
  · cases k <;> cases l <;> simp [Profile.signedValues,Profile.translate,Profile.addColumns,
      Profile.plus,rawRow,RawColumn.atPrimary,Pi.single_apply,Finsupp.single_apply]
  · cases k <;> cases l <;> simp [Profile.signedValues,Profile.translate,Profile.addColumns,
      Profile.minus,rawRow,RawColumn.atPrimary,Pi.single_apply,Finsupp.single_apply]
  · cases j <;> simp [Profile.signedValues,Profile.translate,Profile.addColumns,rawRow,RawColumn.atPrimary]

theorem rowChange_adjacent (k : Bool) (n : ℕ) (i : Site (Supplement J G H)) :
    rowChange prime index positive (auxSign positive) p i (Finsupp.single (.adjacent k n) 1) =
      rawRow prime index positive regular (.adjacent k n) i := by
  classical
  change (p.translate index _ (columnsOfRaw prime index positive _)).signedValues i - _ = _
  rw [columnsOfRaw_adjacent]
  rcases i with ⟨c⟩ | ⟨l,m⟩ | ⟨l,m⟩ | ⟨j⟩
  · simp [Profile.signedValues,Profile.translate,Profile.addColumns,rawRow]
  · cases k <;> cases l <;> simp [Profile.signedValues,Profile.translate,Profile.addColumns,
      Profile.plus,rawRow,RawColumn.atPrimary,Pi.single_apply,adjacent_single_apply]
  · simp [Profile.signedValues,Profile.translate,Profile.addColumns,Profile.minus,rawRow,RawColumn.atPrimary]
  · cases j <;> simp [Profile.signedValues,Profile.translate,Profile.addColumns,rawRow,RawColumn.atPrimary]

theorem rowChange_auxiliary (k : Bool) (a : J k) (i : Site (Supplement J G H)) :
    let c := RawColumn.auxiliary (prime ⟨k,a⟩) k (index k a) (positive k a)
    rowChange prime index positive (auxSign positive) p i (Finsupp.single c 1) =
      rawRow prime index positive regular c i := by
  classical
  change (p.translate index _ (columnsOfRaw prime index positive _)).signedValues i - _ = _
  rw [columnsOfRaw_auxiliary]
  rcases i with ⟨c⟩ | ⟨l,m⟩ | ⟨l,m⟩ | ⟨j⟩
  · simp [Profile.signedValues,Profile.translate,Profile.addColumns,rawRow]
  · by_cases hk : k = l
    · subst l
      simp [Profile.signedValues,Profile.translate,Profile.addColumns,Profile.plus,rawRow,RawColumn.atPrimary,
        transfer_single_apply,auxSign]
      split_ifs <;> simp_all
    · simp [Profile.signedValues,Profile.translate,Profile.addColumns,Profile.plus,rawRow,RawColumn.atPrimary,
        hk]
  · simp [Profile.signedValues,Profile.translate,Profile.addColumns,Profile.minus,rawRow,RawColumn.atPrimary]
  · cases j with
    | auxiliary l b =>
      by_cases hk : k = l
      · subst l
        by_cases hj : a = b
        · subst b; simp [Profile.signedValues,Profile.translate,Profile.addColumns,rawRow,RawColumn.atPrimary]
        · have hn : prime ⟨k,b⟩ ≠ prime ⟨k,a⟩ :=
            fun h => hj (eq_of_heq (Sigma.mk.inj_iff.mp (prime.injective h.symm)).2)
          simp [Profile.signedValues,Profile.translate,Profile.addColumns,rawRow,RawColumn.atPrimary,hn,hj]
      · have hn : prime ⟨l,b⟩ ≠ prime ⟨k,a⟩ := fun h => hk ((Sigma.mk.inj_iff.mp (prime.injective h)).1).symm
        simp [Profile.signedValues,Profile.translate,Profile.addColumns,rawRow,RawColumn.atPrimary,hn,
          Pi.single_eq_of_ne (Ne.symm hk)]
    | _ => simp [Profile.signedValues,Profile.translate,Profile.addColumns,rawRow]

/-- Every valid raw agrees, at every coordinate, with the dyadic row used
by the p-adic selector. -/
theorem rowChange_eq_rawRow (g : Generator ⊕ (Σ k, J k)) (i : Site (Supplement J G H)) :
    let c := basisLabel prime index positive g
    rowChange prime index positive (auxSign positive) p i (Finsupp.single c 1) =
      rawRow prime index positive regular c i := by
  rcases g with (⟨k,n⟩ | ⟨k,n⟩) | ⟨k,a⟩
  · exact rowChange_balanced _ _ _ _ _ _ _ _
  · exact rowChange_adjacent _ _ _ _ _ _ _ _
  · exact rowChange_auxiliary _ _ _ _ _ _ _ _

end UnconditionalCounterexample.Variations.DyadicLedger
