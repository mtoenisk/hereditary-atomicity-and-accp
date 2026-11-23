import UnconditionalCounterexample.Hierarchy.WeightedProfiles
import Mathlib.Topology.ClopenBox
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.Piecewise
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Separation.Profinite

/-!
# Countable requests on the perfect marked fibers

Each fiber has the same Cantor parameter space. Its two constant streams
mark the chosen points. The requests are locally constant integer functions
with finite support in the *fiber index*, not in the individual points.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open TopologicalSpace

abbrev Fiber := ℕ → Bool

def mark (b : Bool) : Fiber := fun _ => b

abbrev Profile := ℕ →₀ LocallyConstant Fiber ℤ

/-- The finite list of marked differences at which weights are measured. -/
def markedDifference : Profile →+ (ℕ →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom
    ((LocallyConstant.evalRingHom (Y := ℤ) (mark false)).toAddMonoidHom -
      (LocallyConstant.evalRingHom (Y := ℤ) (mark true)).toAddMonoidHom)

@[simp] theorem markedDifference_apply (g : Profile) (n : ℕ) :
    markedDifference g n = g n (mark false) - g n (mark true) := rfl

def profileWeight : Profile →+ ℚ := totalWeight.comp markedDifference

/-- Constant height on a clopen patch and zero everywhere else. -/
def patch (C : Clopens Fiber) (s : ℤ) : LocallyConstant Fiber ℤ := by
  classical
  exact ⟨fun x => if x ∈ C then s else 0,
    (IsLocallyConstant.iff_continuous _).mpr
      (continuous_piecewise (fun x hx => False.elim (by simp [C.isClopen.frontier_eq] at hx)) continuousOn_const continuousOn_const)⟩

open Classical in
@[simp] theorem patch_apply (C : Clopens Fiber) (s : ℤ) (x : Fiber) :
    patch C s x = (if x ∈ C then s else 0) := by classical rfl

theorem profileWeight_single_patch (n : ℕ) (C : Clopens Fiber) (s : ℤ) :
    profileWeight (Finsupp.single n (patch C s)) =
      ((patch C s (mark false) - patch C s (mark true) : ℤ) : ℚ) * weight n := by
  change totalWeight (Finsupp.mapRange _ (map_zero _) (Finsupp.single _ _)) = _
  rw [Finsupp.mapRange_single, totalWeight_single]
  rfl

/-- A clopen patch in the given level set avoids both marked points and the
specified point itself, which can therefore witness positivity in the cofactor. -/
theorem exists_unmarked_patch (f : LocallyConstant Fiber ℤ) (x : Fiber) :
    ∃ C : Clopens Fiber, (C : Set Fiber).Nonempty ∧ x ∉ C ∧
      mark false ∉ C ∧ mark true ∉ C ∧ ∀ y ∈ C, f y = f x := by
  classical
  let U := {y : Fiber | f y = f x}
  have ho : IsOpen U := f.isLocallyConstant.isOpen_fiber _
  obtain ⟨I, t, ht, hU⟩ := isOpen_pi_iff.mp ho x rfl
  let N := I.sup id + 1
  let z : Fiber := fun i => if i = N then !x i else if i = N+1 then true
    else if i = N+2 then false else x i
  have hzU : z ∈ U := hU (by
    intro i hi
    have h : i < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    simpa [z, show i ≠ N by omega, show i ≠ N+1 by omega, show i ≠ N+2 by omega] using (ht i hi).2)
  have hzx : z ≠ x := by
    intro he
    have h := congrFun he N
    cases hx : x N <;> simp [z, hx] at h
  have hza : z ≠ mark false := by
    intro he
    simpa [z, mark] using congrFun he (N+1)
  have hzb : z ≠ mark true := by
    intro he
    simpa [z, mark, show N+2 ≠ N+1 by omega] using congrFun he (N+2)
  let D : Set Fiber := {x, mark false, mark true}
  have hD : D.Finite := by simp [D]
  have hz : z ∈ U \ D := ⟨hzU, by simpa [D] using And.intro hzx (And.intro hza hzb)⟩
  obtain ⟨C, hc, hzc, hCU⟩ := compact_exists_isClopen_in_isOpen (ho.sdiff hD.isClosed) hz
  refine ⟨⟨C, hc⟩, ⟨z, hzc⟩, ?_, ?_, ?_, fun y hy => (hCU hy).1⟩
  all_goals exact fun hy => (hCU hy).2 (by simp [D])

/-- Clopen subsets of the Cantor fiber form a countable Boolean algebra.
A locally constant function is encoded by its finite table of nonempty fibers. -/
instance countableRequests : Countable Profile := by
  classical
  let : Countable (Clopens Fiber) := Clopens.countable_iff_secondCountable.mpr inferInstance
  let table (f : LocallyConstant Fiber ℤ) : Finset (ℤ × Clopens Fiber) :=
    f.range_finite.toFinset.image fun z => (z, ⟨{x | f x = z}, f.isLocallyConstant.isClopen_fiber z⟩)
  have htable : Function.Injective table := by
    intro f g he
    ext x
    let C : Clopens Fiber := ⟨{y | f y = f x}, f.isLocallyConstant.isClopen_fiber _⟩
    have hin : (f x, C) ∈ table f := Finset.mem_image.mpr
      ⟨f x, f.range_finite.mem_toFinset.mpr (Set.mem_range_self x), rfl⟩
    rw [he] at hin
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hin
    have he₁ := congrArg Prod.fst hz
    have he₂ := congrArg (fun p : ℤ × Clopens Fiber => (p.2 : Set Fiber)) hz
    change z = f x at he₁
    have hm : x ∈ C := rfl
    change {y | g y = z} = (C : Set Fiber) at he₂
    change x ∈ (C : Set Fiber) at hm
    rw [← he₂] at hm
    exact he₁.symm.trans (show g x = z from hm).symm
  let : Countable (LocallyConstant Fiber ℤ) := htable.countable
  infer_instance

end UnconditionalCounterexample.Hierarchy.Weighted
