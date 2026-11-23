import UnconditionalCounterexample.Variations.DyadicFreshFibres
import UnconditionalCounterexample.Variations.DyadicRounds
import UnconditionalCounterexample.Variations.FreezingCalendar
import UnconditionalCounterexample.Variations.RegularForecast
import UnconditionalCounterexample.Variations.DyadicBlocks

/-!
# Finite work of a dyadic round on its actual prefix

The reserve is exchanged with the final balanced column. Every regular coordinate
used by the resulting word can be allocated before the first raw is selected.
Every retained horizontal and the factors of every split task occur at a finite
opening of the changing prefix.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger
open GuardSupport RecursivePrefix Univariate Polynomial

/-- All regular coordinates at which this raw's additive order can be nonzero. -/
def RawColumn.regularSupport : RawColumn → Finset RegularLabel
  | .balanced k i => {(false,k,i), (true,k,i)}
  | .adjacent k i => {(false,k,i), (false,k,i+1)}
  | .auxiliary _ k i _ => {(false,k,i)}

theorem RawColumn.supports_nonzero (c : RawColumn) (p : PrimeIndex) (l : RegularLabel)
    (h : c.atPrimary p (some l.role) ≠ 0) : l ∈ c.regularSupport := by
  rcases l with ⟨a,b,j⟩
  cases c <;> cases a <;> simp_all [RawColumn.atPrimary,RegularLabel.role,RawColumn.regularSupport]
  all_goals split_ifs at h <;> simp_all

/-- A block starts at the first unconsumed regular index and gives the finite
auxiliary columns first, followed by all adjacent and all balanced columns. -/
structure Block where
  start : ℕ
  width : ℕ
  positive : 0 < width
  reserved : Fin (2*width)
  auxiliary : List RawColumn

namespace Block
variable (s : Block)

def channel (code : ℕ) : Bool := decide (code % 2 = 1)

def localColumn (balanced : Bool) (code : ℕ) : RawColumn :=
  if balanced then .balanced (channel code) (s.start + code / 2)
  else .adjacent (channel code) (s.start + code / 2)

def perm : ℕ ≃ ℕ := Equiv.swap s.reserved.val (2*s.width-1)

def columns : List RawColumn := s.auxiliary ++
  (List.range (2*s.width)).map (s.localColumn false) ++
  (List.range (2*s.width)).map (fun i => s.localColumn true (s.perm i))

theorem length_columns : s.columns.length = s.auxiliary.length + 4*s.width := by
  simp only [columns, List.length_append, List.length_map, List.length_range]
  omega

theorem nonempty : s.columns ≠ [] := by
  intro h
  have := s.length_columns
  rw [h, List.length_nil] at this
  have := s.positive
  omega

theorem columns_last : s.columns.getLast? = some (s.localColumn true s.reserved.val) := by
  have he : 2*s.width = (2*s.width-1)+1 := by have := s.positive; omega
  unfold columns
  rw [show List.range (2*s.width) = List.range (2*s.width-1) ++ [2*s.width-1] by
    conv_lhs => rw [he, List.range_succ]]
  simp only [List.map_append,List.map_singleton,← List.append_assoc,List.getLast?_concat,
    perm,Equiv.swap_apply_right]

theorem localColumn_code (reserved : Bool) (k : Bool) (i : ℕ) :
    s.localColumn reserved (DyadicBlocks.Rounds.code k i) =
      (if reserved then RawColumn.balanced k (s.start+i) else .adjacent k (s.start+i)) := by
  cases k <;> cases reserved <;> simp [localColumn,channel,DyadicBlocks.Rounds.code,
    Nat.mul_comm 2 i,Nat.add_mod] <;> omega

/-- Include the successor of the final adjacent index plus the regular
compensation indices of the actual auxiliary columns. -/
def required : Finset RegularLabel := s.columns.toFinset.biUnion RawColumn.regularSupport

theorem required_of_nonzero {c : RawColumn} (hc : c ∈ s.columns) (p : PrimeIndex) (l : RegularLabel)
    (h : c.atPrimary p (some l.role) ≠ 0) : l ∈ s.required :=
  Finset.mem_biUnion.mpr ⟨c,List.mem_toFinset.mpr hc,c.supports_nonzero p l h⟩

end Block

/-- Missing labels are tested against the complete persistent prime-role map. -/
def Ledger.missing (m : Ledger) (need : Finset RegularLabel) : Finset RegularLabel := by
  classical
  exact need.filter fun l => ∀ p, m.role p ≠ some l.role

def RegularLabel.centre (l : RegularLabel) : ℕ := if l.1 then 1 else 0

theorem RegularLabel.centre_case (l : RegularLabel) : l.centre = 0 ∨ l.centre = 1 := by
  cases h : l.1 <;> simp [RegularLabel.centre,h]

/-- All missing labels can be installed at this very stage while the regular
tail formula holds for the complete frozen set, including both centres. -/
theorem Block.reserve_regular {n : ℕ} (s : Block) (m : Ledger) (P : Prefix n)
    (frozen : Finset ℚ[X]) (hf : ∀ f ∈ frozen, f.Monic ∧ Irreducible f)
    (avoid : Finset PrimeIndex) (cutoff : ℕ) :
    ∃ a : FreshFibres m P, Disjoint a.births.primes avoid ∧
      (∀ p hp, ∃ l ∈ m.missing s.required, a.role p hp = some l.role ∧ cutoff < p.val ∧
        ∀ f ∈ frozen, (aeval ((a.births.site p hp).branch false) f).valuation =
          (if f = RegularForecast.centreFactor l.centre then 1 else 0) ∧
          (aeval ((a.births.site p hp).branch true) f).valuation = 0) ∧
      (∀ l ∈ s.required, (∃ p, m.role p = some l.role) ∨
        ∃ p, ∃ hp : p ∈ a.births.primes, cutoff < p.val ∧ a.role p hp = some l.role ∧
          ∀ f ∈ frozen,
            (aeval ((a.births.site p hp).branch false) f).valuation =
              (if f = RegularForecast.centreFactor l.centre then 1 else 0) ∧
            (aeval ((a.births.site p hp).branch true) f).valuation = 0) := by
  classical
  let labels := m.missing s.required
  have hfresh : ∀ l ∈ labels, ∀ p, m.role p ≠ some l.role :=
    fun _ h => (Finset.mem_filter.mp h).2
  obtain ⟨e,hinj,hnew⟩ := RegularForecast.exists_family P labels RegularLabel.centre
    RegularLabel.centre_case frozen hf avoid cutoff
  let a := FreshFibres.regular (labels := labels) (centre := RegularLabel.centre)
    (frozen := fun l => frozen.erase (RegularForecast.centreFactor l.centre)) e hinj hfresh
  have cover (l) (hl : l ∈ labels) :
      ∃ p, ∃ hp : p ∈ a.births.primes, cutoff < p.val ∧ a.role p hp = some l.role ∧
        ∀ f ∈ frozen, (aeval ((a.births.site p hp).branch false) f).valuation =
          (if f = RegularForecast.centreFactor l.centre then 1 else 0) ∧
          (aeval ((a.births.site p hp).branch true) f).valuation = 0 := by
    let i : labels := ⟨l,hl⟩
    have hp : (e i).prime ∈ a.births.primes := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    refine ⟨(e i).prime,hp,(hnew i).1,FreshFibres.regular_role (labels := labels) (centre := RegularLabel.centre)
      (frozen := fun l => frozen.erase (RegularForecast.centreFactor l.centre)) e hinj hfresh i hp,?_⟩
    intro f h
    simp only [a,FreshFibres.regular,RegularReservations.Entry.births_site]
    exact RegularForecast.entry_orders (e i) l.centre_case h
  refine ⟨a,Finset.disjoint_left.mpr ?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact (hnew i).2
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨i.val,i.property,FreshFibres.regular_role (labels := labels) (centre := RegularLabel.centre)
      (frozen := fun l => frozen.erase (RegularForecast.centreFactor l.centre)) e hinj hfresh i _,(hnew i).1,?_⟩
    intro f h
    simp only [a,FreshFibres.regular,RegularReservations.Entry.births_site]
    exact RegularForecast.entry_orders (e i) i.val.centre_case h
  · intro l hl
    by_cases existsOld : ∃ p, m.role p = some l.role
    · exact Or.inl existsOld
    · exact Or.inr (cover l (Finset.mem_filter.mpr ⟨hl,fun p h => existsOld ⟨p,h⟩⟩))

end UnconditionalCounterexample.Variations.DyadicLedger
