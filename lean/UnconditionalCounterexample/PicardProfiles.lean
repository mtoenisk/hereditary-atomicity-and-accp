import UnconditionalCounterexample.ValuationProfiles
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Range
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic

noncomputable section
namespace UnconditionalCounterexample.PicardProfiles

/-- A restricted integer profile: its E entry, finitely supported primary
deviation from E, and finitely supported outside entries. -/
abbrev Profile (O : Type*) := ℤ × (ℕ →₀ ℤ) × (O →₀ ℤ)

/-- The actual coordinate function represented by the three pieces. -/
def coordinate {O : Type*} : Profile O →+ (ProfilePlace O → ℤ) where
  toFun x
    | .limit => x.1
    | .primary j => x.1 + x.2.1 j
    | .outside o => x.2.2 o
  map_zero' := by funext p; cases p <;> simp
  map_add' x y := by funext p; cases p <;> simp [add_assoc, add_left_comm, add_comm]

@[simp] theorem coordinate_limit {O : Type*} (x : Profile O) : coordinate x .limit = x.1 := rfl
@[simp] theorem coordinate_primary {O : Type*} (x : Profile O) (j : ℕ) :
    coordinate x (.primary j) = x.1 + x.2.1 j := rfl
@[simp] theorem coordinate_outside {O : Type*} (x : Profile O) (o : O) :
    coordinate x (.outside o) = x.2.2 o := rfl

theorem coordinate_injective {O : Type*} : Function.Injective (coordinate (O := O)) := by
  intro x y h
  have hE : x.1 = y.1 := congrFun h .limit
  apply Prod.ext hE
  apply Prod.ext
  · apply Finsupp.ext
    intro j
    have hj := congrFun h (.primary j)
    change x.1 + x.2.1 j = y.1 + y.2.1 j at hj
    omega
  · apply Finsupp.ext
    intro o
    exact congrFun h (.outside o)

/-- Exactly the restrictions asserted for invertible fractional ideal profiles. -/
def Restricted {O : Type*} (f : ProfilePlace O → ℤ) : Prop :=
  (∃ N : ℕ, ∀ j, N ≤ j → f (.primary j) = f .limit) ∧
    {o : O | f (.outside o) ≠ 0}.Finite

theorem coordinate_restricted {O : Type*} (x : Profile O) : Restricted (coordinate x) := by
  obtain ⟨N, hN⟩ := x.2.1.support.exists_nat_subset_range
  refine ⟨⟨N, fun j hj => ?_⟩, ?_⟩
  · have hz : x.2.1 j = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro h
      have := Finset.mem_range.mp (hN h)
      omega
    simp [hz]
  · change (Function.support x.2.2).Finite
    exact x.2.2.hasFiniteSupport

theorem exists_coordinate {O : Type*} (f : ProfilePlace O → ℤ) (hf : Restricted f) :
    ∃ x : Profile O, coordinate x = f := by
  obtain ⟨⟨N, hN⟩, ho⟩ := hf
  have hp : (Function.support (fun j => f (.primary j) - f .limit)).Finite := by
    apply (Finset.range N).finite_toSet.subset
    intro j hj
    change j ∈ Finset.range N
    apply Finset.mem_range.mpr
    by_contra h
    exact hj (sub_eq_zero.mpr (hN j (by omega)))
  let x : Profile O := (f .limit, Finsupp.ofSupportFinite _ hp, Finsupp.ofSupportFinite _ ho)
  refine ⟨x, ?_⟩
  funext p
  cases p with
  | limit => rfl
  | primary j =>
    change f .limit + (f (.primary j) - f .limit) = f (.primary j)
    omega
  | outside o => rfl

/-- Construct the finite representation of an actual restricted tuple. -/
def ofCoordinates {O : Type*} (f : ProfilePlace O → ℤ) (hf : Restricted f) : Profile O :=
  (exists_coordinate f hf).choose

@[simp] theorem coordinate_ofCoordinates {O : Type*} (f : ProfilePlace O → ℤ) (hf : Restricted f) :
    coordinate (ofCoordinates f hf) = f := (exists_coordinate f hf).choose_spec

/-- Finite primary tuples embedded with E and every outside coordinate zero. -/
def primary {O : Type*} : (ℕ →₀ ℤ) →+ Profile O where
  toFun a := (0, a, 0)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coordinate_primary_embed {O : Type*} (a : ℕ →₀ ℤ) (j : ℕ) :
    coordinate (primary (O := O) a) (.primary j) = a j := by
  change 0 + a j = a j
  exact zero_add _

/-- The tail profile lambda, equal to one at E and every primary. -/
def tail {O : Type*} : Profile O := (1, 0, 0)

/-- The actual profile of t: lambda plus one extra unit at the first primary. -/
def tProfile {O : Type*} : Profile O := (1, Finsupp.single 0 1, 0)

end UnconditionalCounterexample.PicardProfiles
