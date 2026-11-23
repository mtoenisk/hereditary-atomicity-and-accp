import UnconditionalCounterexample.Variations.CalibrationForecast

/-!
# Recovering the physical signed mass from a finite prime table

Each regular coordinate has one prime. The auxiliary coordinates in each
channel embed into the primes, carrying their individual index and sign.
Outside a finite set the primary values match the horizontal forecast and
the paired guard values vanish.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.MassReindex
open Calibration DyadicDeviations DyadicColumns

variable {I : Type*} {J : Bool → Type*} {G H : Type*}

structure Indexing (I : Type*) (J : Bool → Type*) where
  role : I → Option FibreRole
  regular : Bool → Bool → ℕ → I
  regular_iff : ∀ p c k n, role p = some (.regular c k n) ↔ p = regular c k n
  auxiliary : (k : Bool) → J k ↪ I
  index : (k : Bool) → J k → ℕ
  positive : (k : Bool) → J k → Bool
  auxiliary_iff : ∀ p k n e, role p = some (.auxiliary k n e) ↔
    ∃ j, auxiliary k j = p ∧ index k j = n ∧ positive k j = e

variable (X : Indexing I J)

def Indexing.sign (k : Bool) (j : J k) : ℤ := if X.positive k j then 1 else -1

theorem Indexing.aux_role (k : Bool) (j : J k) :
    X.role (X.auxiliary k j) = some (.auxiliary k (X.index k j) (X.positive k j)) :=
  (X.auxiliary_iff ..).mpr ⟨j,rfl,rfl,rfl⟩

private theorem regular_entry [DecidableEq I] (p : I) (c k : Bool) (n : ℕ) (z : ℤ) :
    (regularRow (X.role p) c k z) n = (if p = X.regular c k n then z else 0) := by
  classical
  by_cases he : p = X.regular c k n
  · rw [(X.regular_iff ..).mpr he, ite_eq_left he]
    simp [regularRow]
  · have hr := mt (X.regular_iff p c k n).mp he
    cases hrole : X.role p with
    | none => simp [regularRow,he]
    | some r =>
      cases r with
      | auxiliary => simp [regularRow,he]
      | regular a b j =>
        by_cases hab : a = c ∧ b = k
        · obtain ⟨rfl,rfl⟩ := hab
          have hj : j ≠ n := fun h => hr (h ▸ hrole)
          simp [regularRow,he,hj]
        · simp [regularRow,he,hab]

private theorem regular_vector (A : Finset I) (c k : Bool) (v : I → ℤ) (d : ℕ →₀ ℤ)
    (hv : ∀ n, d n = v (X.regular c k n))
    (hz : ∀ n, X.regular c k n ∉ A → d n = 0) :
    ∑ p ∈ A, regularRow (X.role p) c k (v p) = d := by
  classical
  ext n
  rw [Finsupp.finsetSum_apply]
  simp_rw [regular_entry]
  by_cases hm : X.regular c k n ∈ A
  · simp [hm,hv]
  · simp [hm,hz n hm]

private theorem aux_off (p q : I) (hp : p ≠ q) (r : Option FibreRole) (k : Bool) (z : ℤ) :
    (auxiliaryRow r p k z) q = 0 := by
  classical
  cases r with
  | none => rfl
  | some r =>
    cases r with
    | regular => rfl
    | auxiliary l j e =>
      by_cases h : l = k <;> simp [auxiliaryRow,h,hp]

private theorem auxiliary_vector (A : Finset I) (k : Bool) (v : I → ℤ) (d : J k →₀ ℤ)
    (hv : ∀ j, d j = v (X.auxiliary k j))
    (hz : ∀ j, X.auxiliary k j ∉ A → d j = 0) :
    ∑ p ∈ A, auxiliaryRow (X.role p) p k (v p) = Finsupp.embDomain (X.auxiliary k) d := by
  classical
  ext q
  rw [Finsupp.finsetSum_apply]
  by_cases hq : q ∈ Set.range (X.auxiliary k)
  · obtain ⟨j,rfl⟩ := hq
    rw [Finsupp.embDomain_apply_self]
    by_cases hm : X.auxiliary k j ∈ A
    · rw [Finset.sum_eq_single_of_mem _ hm (fun p _ hn => aux_off p _ hn _ _ _)]
      simp [X.aux_role,auxiliaryRow,hv]
    · rw [hz j hm]
      exact Finset.sum_eq_zero fun p hp =>
        aux_off p (X.auxiliary k j) (fun e => hm (e ▸ hp)) _ _ _
  · rw [Finsupp.embDomain_of_notMem_range _ _ _ hq]
    apply Finset.sum_eq_zero
    intro p _
    by_cases he : p = q
    · subst p
      cases h : X.role q with
      | none => rfl
      | some r =>
        cases r with
        | regular => rfl
        | auxiliary l j e =>
          by_cases hl : l = k
          · subst l
            obtain ⟨w, hw, _, _⟩ := (X.auxiliary_iff q k j e).mp h
            exact (hq ⟨w,hw⟩).elim
          · simp [auxiliaryRow,hl]
    · exact aux_off p q he _ _ _

private theorem transfer_embDomain (k : Bool) (d : J k →₀ ℤ) :
    auxiliaryTransfer (auxWeight X.role k) (auxSign X.role k) (Finsupp.embDomain (X.auxiliary k) d) =
      auxiliaryTransfer (X.index k) (X.sign k) d := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [Finsupp.embDomain_add,hu,hv]
  | single j z =>
    cases h : X.positive k j <;>
      simp [Finsupp.embDomain_single,auxiliaryTransfer,auxWeight,auxSign,X.aux_role,
        FibreRole.sign,FibreRole.index,Indexing.sign,h]

/-- The profile entries at all paired fibres are their genuine observed
branch orders. The lone guards and horizontal entries carry no channel weight. -/
structure Reads (X : Indexing I J) (P : Profile J G H) (primary guard : I → ℤ) : Prop where
  regular_primary : ∀ c k n, primary (X.regular c k n) = if c then P.minus k n else P.plus k n
  regular_guard : ∀ c k n, guard (X.regular c k n) =
    if c then P.guards.minus k n else P.guards.plus k n
  aux_primary : ∀ k j, primary (X.auxiliary k j) = P.auxiliary k j
  aux_guard : ∀ k j, guard (X.auxiliary k j) = P.guards.auxiliary k j

/-- The physical mass is the same finite prime sum that the adaptive
calibration computed. The proof reindexes the auxiliary weights without
identifying distinct auxiliary primes that share an index. -/
theorem signedMass_eq_sum (A : Finset I) (P : Profile J G H) (primary guard : I → ℤ)
    (read : Reads X P primary guard)
    (forecast : ∀ p ∉ A, ∀ r, X.role p = some r →
      primary p = forecastOrder P.height (some r) ∧ guard p = 0) (k : Bool) :
    P.signedMass X.index X.sign k = (P.height false : ℚ) - P.height true +
      ∑ p ∈ A, discrepancy (X.role p) P.height k (primary p) (guard p) := by
  let Q := provisionalProfile A X.role P.height primary guard (0 : Unit →₀ ℤ)
  have dev (c : Bool) :
      ∑ p ∈ A, regularRow (X.role p) c k (primary p - P.height c) =
        (if c then P.minusDeviation k else P.plusDeviation k) := by
    apply regular_vector
    · intro n
      rw [read.regular_primary]
      cases c <;> simp [Profile.plus,Profile.minus]
    · intro n hn
      have h := (forecast _ hn _ ((X.regular_iff ..).mpr rfl)).1
      rw [read.regular_primary] at h
      cases c <;> simpa [forecastOrder,Profile.plus,Profile.minus] using h
  have gdev (c : Bool) :
      ∑ p ∈ A, regularRow (X.role p) c k (guard p) =
        (if c then P.guards.minus k else P.guards.plus k) := by
    apply regular_vector
    · intro n
      rw [read.regular_guard]
      cases c <;> rfl
    · intro n hn
      have h := (forecast _ hn _ ((X.regular_iff ..).mpr rfl)).2
      rw [read.regular_guard] at h
      cases c <;> exact h
  have aux : Q.auxiliary k = Finsupp.embDomain (X.auxiliary k) (P.auxiliary k) :=
    auxiliary_vector X A k primary _ (fun j => (read.aux_primary k j).symm) (fun j hj =>
      (read.aux_primary k j).symm.trans (forecast _ hj _ (X.aux_role k j)).1)
  have ag : Q.guards.auxiliary k = Finsupp.embDomain (X.auxiliary k) (P.guards.auxiliary k) :=
    auxiliary_vector X A k guard _ (fun j => (read.aux_guard k j).symm) (fun j hj =>
      (read.aux_guard k j).symm.trans (forecast _ hj _ (X.aux_role k j)).2)
  have hplus : Q.plusDeviation k = P.plusDeviation k := dev false
  have hminus : Q.minusDeviation k = P.minusDeviation k := dev true
  have hgplus : Q.guards.plus k = P.guards.plus k := gdev false
  have hgminus : Q.guards.minus k = P.guards.minus k := gdev true
  change P.signedMass X.index X.sign k = _
  rw [← provisional_signedMass A X.role P.height primary guard (0 : Unit →₀ ℤ) k]
  change _ = Q.signedMass (auxWeight X.role) (auxSign X.role) k
  simp only [Profile.signedMass,Profile.regularMass,hplus,hminus,hgplus,hgminus,aux,ag,map_sub,
    transfer_embDomain]
  rfl

end UnconditionalCounterexample.Variations.DyadicLedger.MassReindex
