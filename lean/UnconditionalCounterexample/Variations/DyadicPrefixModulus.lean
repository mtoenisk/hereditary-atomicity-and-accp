import UnconditionalCounterexample.Variations.DyadicDispatchEmission
import UnconditionalCounterexample.Variations.DyadicPermanentRoles

/-!
# Prepared modulus fibres for the next opening's split

At round r+1 every rational prime of the modulus named at round r is
already in the finite table. Its channel assignment is permanent, and a
single finite bound places the reserved coordinate beyond all such labels
and the indices of the auxiliary columns that have just been requested.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger
open GuardSupport Univariate RecursivePrefix

/-- The manuscript assigns lone guards and channel zero to the first factor. -/
def splitFirst (role : PrimeIndex → Option FibreRole) (p : ℕ) : Bool :=
  if hp : Nat.Prime p then (role ⟨p,hp⟩).elim true fun r => !r.channel else true

theorem splitFirst_prime (role : PrimeIndex → Option FibreRole) (p : PrimeIndex) :
    splitFirst role p.val = (role p).elim true fun r => !r.channel := by simp [splitFirst,p.property]

def columnIndex : RawColumn → ℕ
  | .balanced _ i | .adjacent _ i | .auxiliary _ _ i _ => i

/-- Also admit a caller-supplied bound, for example the stable-tail cutoff of
the split element's preview. -/
def reserveIndex (m : Ledger) (A : Finset PrimeIndex) (aux : List RawColumn) (extra : ℕ) :=
  max (max m.regularBound extra) (max (A.sup fun p => (m.role p).elim 0 FibreRole.index)
    (aux.toFinset.sup columnIndex)) + 1

theorem reserve_gt_raw (m : Ledger) (A : Finset PrimeIndex) (aux : List RawColumn) (extra : ℕ) :
    m.regularBound < reserveIndex m A aux extra ∧ extra < reserveIndex m A aux extra := by
  unfold reserveIndex
  omega

theorem reserve_gt_role (m : Ledger) (A : Finset PrimeIndex) (aux : List RawColumn) (extra : ℕ)
    (p : PrimeIndex) (hp : p ∈ A) (r : FibreRole) (hr : m.role p = some r) :
    r.index < reserveIndex m A aux extra := by
  have h := Finset.le_sup (f := fun p => (m.role p).elim 0 FibreRole.index) hp
  simp only [hr,Option.elim_some] at h
  unfold reserveIndex
  omega

theorem reserve_gt_aux (m : Ledger) (A : Finset PrimeIndex) (aux : List RawColumn) (extra : ℕ)
    (c : RawColumn) (h : c ∈ aux) : columnIndex c < reserveIndex m A aux extra := by
  have h' := Finset.le_sup (f := columnIndex) (List.mem_toFinset.mpr h)
  unfold reserveIndex
  omega

/-- The full fibre for the previously named modulus is present before this
round's width, reservation, and unit targets are chosen. -/
theorem previous_modulus_assigned (choose : Planner) (r : ℕ) (p : PrimeIndex)
    (hp : p.val ∣ (taskAt r).modulus) :
    p ∈ (dispatcher choose).assigned ((dispatcher choose).opening (r+1)) := by
  let D := dispatcher choose
  let n := D.opening r
  let m := D.state n
  let P := (chain D.requirements).approx n
  let T := table D.requirements n
  let o := choose m P T
  have he : (D.actualRequest n).toFreshFibres = o.fibres.coverPrimes
      (FreshFibres.modulusPrimes (taskAt m.rounds).modulus) :=
    dispatch_open_fibres choose m P T (D.opening_empty r)
  have hm : m.rounds = r := D.opening_rounds r
  have cov := o.fibres.modulus_covered (taskAt m.rounds).positive p (hm ▸ hp)
  rw [← he] at cov
  rcases Finset.mem_union.mp cov with old | new
  · exact assigned_mono D.requirements (D.opening_strict (Nat.lt_succ_self r)).le old
  · have mem := (selection D.requirements n).batch.processed_subset_assigned
      (D.schedule.requested_processed n new)
    exact assigned_mono D.requirements (D.opening_strict (Nat.lt_succ_self r)) mem

/-- On every modulus prime the prefix's choice of whole channel agrees with
the final ring, and every regular coordinate there precedes the reserve. -/
theorem previous_modulus_data (choose : Planner) (r : ℕ) (aux : List RawColumn) (extra : ℕ)
    (p : PrimeIndex) (hp : p.val ∣ (taskAt r).modulus) :
    let D := dispatcher choose; let n := D.opening (r+1); let m := D.state n
    splitFirst m.role p.val = (D.permanentRole p).elim true (fun q => !q.channel) ∧
      ∀ c k i, D.permanentRole p = some (.regular c k i) → i < reserveIndex m (D.assigned n) aux extra := by
  let D := dispatcher choose
  let n := D.opening (r+1)
  have mem : p ∈ D.assigned n := previous_modulus_assigned choose r p hp
  have he := D.role_eq_permanent p mem
  refine ⟨(splitFirst_prime (D.state n).role p).trans (congrArg (fun q => Option.elim q true fun a => !FibreRole.channel a) he), ?_⟩
  exact fun c k i hr => reserve_gt_role (D.state n) _ aux extra p mem (.regular c k i) (he.trans hr)

end UnconditionalCounterexample.Variations.DyadicLedger
