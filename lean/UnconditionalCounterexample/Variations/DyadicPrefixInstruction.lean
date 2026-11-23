import UnconditionalCounterexample.Variations.DyadicPrefixCoarse
import UnconditionalCounterexample.Variations.DyadicPrefixModulus
import UnconditionalCounterexample.Variations.DyadicCalibratedDriver

/-!
# Choosing a split instruction from its finite prefix

Compute the channel split on the snapshot, place its reserved balanced raw
past the frozen exceptions, and choose the block width after finite signed
elimination. The policy reads only the memory, table, and new auxiliary
column list supplied at the opening of this round.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.PrefixInstruction
open GuardSupport RecursivePrefix Univariate DyadicDeviations DyadicEscape DyadicSplit PrefixProfile

variable {n : ℕ} (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes)
    (aux : List RawColumn) (x : (RatFunc ℚ)ˣ)

abbrev A := P.state.assignment.primes
abbrev source := signed (A P) m.role T m.frozen x

def M := reserveIndex m (A P) aux (source m P T x).natRegular.cutoff

/-- Finite signed elimination of a split with one distinguished last raw. -/
structure Prepared where
  left : Profile (Aux (A P) m.role) (Lone (A P) m.role) (Known m.frozen)
  right : Profile (Aux (A P) m.role) (Lone (A P) m.role) (Known m.frozen)
  split : SplitAt (index (A P) m.role) (sign (A P) m.role) (source m P T x) left right (M m P T aux x)
  exponents : RawColumn →₀ ℤ
  basis : ∀ c ∈ exponents.support,
    c ∈ Set.range (basisLabel (prime (A P) m.role) (index (A P) m.role) (positive (A P) m.role))
  one : exponents (.balanced true (M m P T aux x)) = 1
  word : (signed (A P) m.role T m.frozen (coarse (A P) m.role T m.frozen left)).translate
    (index (A P) m.role) (sign (A P) m.role)
    (columnsOfRaw (prime (A P) m.role) (index (A P) m.role) (positive (A P) m.role) exponents) = left

/-- The finite split and its raw exponents exist once the source and its
explicit horizontal/scalar coarse factor satisfy the calibrated equations. -/
theorem exists_prepared (hr : UniqueRegular (A P) m.role)
    (hm : (source m P T x).MassEquations (index (A P) m.role) (sign (A P) m.role))
    (heff : ∀ i, 0 ≤ (source m P T x).signedValues i)
    (h₀ : 0 < (source m P T x).height false) (h₁ : 0 < (source m P T x).height true)
    (hbase : ∀ u, (signed (A P) m.role T m.frozen (coarse (A P) m.role T m.frozen u)).MassEquations
      (index (A P) m.role) (sign (A P) m.role)) : Nonempty (Prepared m P T aux x) := by
  let p := source m P T x
  let j := M m P T aux x
  let index' := index (A P) m.role
  let sign' := sign (A P) m.role
  let prime' := prime (A P) m.role
  let pos := positive (A P) m.role
  have hcut : p.natRegular.cutoff ≤ j := (reserve_gt_raw m (A P) aux p.natRegular.cutoff).2.le
  obtain ⟨u,v,hs⟩ := exists_split_signed index' sign' p hm heff h₀ h₁ j hcut
  let b := signed (A P) m.role T m.frozen (coarse (A P) m.role T m.frozen u)
  have hh := coarse_horizontal (A P) m.role T m.frozen u
  have hheight : b.height = u.height := funext fun c => DFunLike.congr_fun hh (.inl c)
  have hhor : b.horizontal = u.horizontal := Finsupp.ext fun i => DFunLike.congr_fun hh (.inr i)
  have hg := coarse_guards (A P) m.role T m.frozen u hr
    (split_supported (A P) m.role m.frozen hs (signed_supported (A P) m.role T m.frozen x))
  have miss (q : PrimeIndex) (hq : q ∈ A P) : m.role q ≠ some (.regular true true j) := by
    intro he
    have hj := reserve_gt_role m (A P) aux p.natRegular.cutoff q hq (.regular true true j) he
    exact (lt_irrefl j) hj
  have hmj : b.minus true j = 0 := by
    have h := (missing_regular (A P) m.role b.height (branchOrder (A P) T (coarse (A P) m.role T m.frozen u) false)
      (branchOrder (A P) T (coarse (A P) m.role T m.frozen u) true) b.horizontal miss).1
    change b.minus true j = b.height true at h
    exact h.trans ((congrFun hheight true).trans hs.heights.2.1)
  obtain ⟨he,q,hq⟩ := hs.reserved_coefficient index' sign' b (hbase u) hheight hg hhor hmj
  let cols : Columns (Aux (A P) m.role) := (fun k => u.minusDeviation k - b.minusDeviation k,q,
    fun k => u.auxiliary k - b.auxiliary k)
  let e := rawCoefficients prime' index' pos cols
  refine ⟨⟨u,v,hs,e,?_,(rawCoefficients_balanced _ _ _ _ _ _).trans he,?_⟩⟩
  · intro c hc
    by_contra hn
    exact Finsupp.mem_support_iff.mp hc (Finsupp.embDomain_of_notMem_range _ _ _ hn)
  · change b.translate index' sign' (columnsOfRaw prime' index' pos (rawCoefficients prime' index' pos cols)) = u
    rw [columnsOfRaw_rawCoefficients]
    exact hq

namespace Prepared
variable {m P T aux x} (w : Prepared m P T aux x)

def width := max (M m P T aux x - m.regularBound) (w.exponents.support.sup columnIndex - m.regularBound) + 1

theorem index_lt (w : Prepared m P T aux x) : M m P T aux x-m.regularBound < w.width := by
  unfold width
  omega

def block : Block :=
  { start := m.regularBound
    width := w.width
    positive := Nat.succ_pos _
    reserved := ⟨DyadicBlocks.Rounds.code true (M m P T aux x-m.regularBound), by
      have h := w.index_lt
      simp only [DyadicBlocks.Rounds.code,ite_true]
      omega⟩
    auxiliary := aux }

theorem reserved : w.block.localColumn true w.block.reserved.val = .balanced true (M m P T aux x) := by
  change w.block.localColumn true (DyadicBlocks.Rounds.code true (M m P T aux x-m.regularBound)) = _
  rw [Block.localColumn_code]
  have hl := (reserve_gt_raw m (A P) aux (source m P T x).natRegular.cutoff).1.le
  simp [block,M,Nat.add_sub_of_le hl]

theorem support_below (c : RawColumn) (hc : c ∈ w.exponents.support) :
    columnIndex c < m.regularBound + w.block.width := by
  have h := Finset.le_sup (f := columnIndex) hc
  change columnIndex c < m.regularBound + (max _ _ + 1)
  omega

def instruction (task : SplitTask) : SplitInstruction :=
  { task := task, coarse := coarse (A P) m.role T m.frozen w.left,
    coefficients := w.exponents, first := splitFirst m.role, channel := true,
    index := M m P T aux x, exponent_one := w.one }

def layout (task : SplitTask) : Calibrated.Layout m aux :=
  { block := w.block, start_eq := rfl, auxiliary_eq := rfl, instruction := some (w.instruction task),
    reserved_eq := fun _ h => Option.some.inj h ▸ w.reserved }

end Prepared

/-- The previous round's task has already been frozen before this decision.
At an ineligible task the calibrated recursion still processes its next round. -/
def policy : Calibrated.Policy := fun m P T aux => by
  classical
  let task := taskAt (m.rounds-1)
  by_cases hr : m.rounds = 0
  · exact Calibrated.unitWidth m P T aux
  by_cases hx : task.element = 0
  · exact Calibrated.unitWidth m P T aux
  let x := Units.mk0 task.element hx
  by_cases hp : Nonempty (Prepared m P T aux x)
  · exact (Classical.choice hp).layout task
  · exact Calibrated.unitWidth m P T aux

theorem policy_selects {m : Ledger} (P : Prefix n) (T : Table P.state.assignment.primes) (aux : List RawColumn)
    (hr : m.rounds ≠ 0) (hx : (taskAt (m.rounds-1)).element ≠ 0)
    (hp : Nonempty (Prepared m P T aux (Units.mk0 _ hx))) :
    ∃ w : Prepared m P T aux (Units.mk0 _ hx), policy m P T aux = w.layout (taskAt (m.rounds-1)) := by
  classical
  exact ⟨Classical.choice hp, by simp [policy,hr,hx,hp]⟩

end UnconditionalCounterexample.Variations.DyadicLedger.PrefixInstruction
