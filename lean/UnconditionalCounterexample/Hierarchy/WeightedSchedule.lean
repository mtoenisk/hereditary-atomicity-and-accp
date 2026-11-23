import UnconditionalCounterexample.Hierarchy.WeightedFiber
import UnconditionalCounterexample.PrincipalProfiles
import Mathlib.Data.Rat.Encodable
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Data.Nat.Pairing
import Mathlib.Algebra.BigOperators.Fin

/-!
# Simultaneous schedule for marked fibers and polynomial poles

At each step the next ordinary monic irreducible is processed before one
profile request is filled. Previously seen polynomials remain units on the
new fiber. Requests are enumerated infinitely often, so every finite support
lies in the assigned prefix by some occurrence of that request.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open Polynomial
open scoped BigOperators
open Classical

/-- Even-valued finite requests on the Cantor fibers with integral weight. -/
def Admissible (g : Profile) : Prop :=
  (∀ n x, Even (g n x)) ∧ ∃ z : ℤ, profileWeight g = z

private theorem zero_admissible : Admissible 0 := by
  constructor
  · intro n x
    exact ⟨0,rfl⟩
  · exact ⟨0, by simp⟩

private abbrev Request := {g : Profile // Admissible g}

private instance : Nonempty Request := ⟨0, zero_admissible⟩

private def enumerateRequest : ℕ → Request := (exists_surjective_nat Request).choose

/-- At stage n, postpone requests on fibers beyond the assigned prefix. -/
private def request (n : ℕ) : Profile :=
  let g := (enumerateRequest n.unpair.1).val
  if g.support ⊆ Finset.range (n+1) then g else 0

private theorem request_admissible (n : ℕ) : Admissible (request n) := by
  dsimp only [request]
  split <;> first | exact (enumerateRequest _).property | exact zero_admissible

private theorem request_support (n : ℕ) : (request n).support ⊆ Finset.range (n+1) := by
  dsimp only [request]
  split <;> simp_all

private theorem request_surjective (g : Profile) (hg : Admissible g) :
    ∃ n, request n = g := by
  obtain ⟨m, hm⟩ := (exists_surjective_nat Request).choose_spec ⟨g,hg⟩
  let n := Nat.pair m (g.support.sup id)
  have hmax : g.support.sup id ≤ n := Nat.right_le_pair ..
  refine ⟨n, ?_⟩
  have hrequest : enumerateRequest n.unpair.1 = ⟨g,hg⟩ := by
    simpa [enumerateRequest, n] using hm
  have hs : g.support ⊆ Finset.range (n+1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.le_sup (f := id) hi).trans hmax))
  simp [request, hrequest, hs]

abbrev Ordinary := PrincipalProfiles.MonicIrreducible ℚ
private instance : Countable Ordinary := by
  have : Countable ℚ[X] := (Polynomial.toFinsuppIso ℚ).injective.countable
  infer_instance

private instance : Nonempty Ordinary := ⟨X, monic_X, irreducible_X⟩
private def ordinary : ℕ → Ordinary := (exists_surjective_nat Ordinary).choose

/-- Data proved by the fresh-prime and the compact approximation lemmas. -/
structure StageChoices (P : Type*) where
  prime : P → ℕ
  order : P → ℚ[X] → Fiber → ℤ
  safe : ∀ (frozen : Finset Ordinary) (N : ℕ), ∃ A, N < prime A ∧
    ∀ f ∈ frozen, ∀ x, order A f.val x = 0
  correct : ∀ (frozen : Finset Ordinary) (f : Ordinary), f ∉ frozen → ∀ k : ℤ, ∀ N : ℕ,
    ∃ A, N < prime A ∧ (∀ g ∈ frozen, ∀ x, order A g.val x = 0) ∧
      order A f.val (mark false) - order A f.val (mark true) = k
  approximate : ∀ {n : ℕ} (A : Fin n → P), Function.Injective (prime ∘ A) →
    ∀ g : Profile, ∀ m : ℕ, ∃ f : Ordinary, m ≤ f.val.natDegree ∧
      ∀ i x, order (A i) f.val x = g i.val x

private def columns {P : Type*} (D : StageChoices P) {n : ℕ} (A : Fin n → P) (f : Ordinary) :
    ℕ →₀ ℤ :=
  ∑ i, Finsupp.single i.val (D.order (A i) f.val (mark false) - D.order (A i) f.val (mark true))

private theorem columns_snoc {P : Type*} (D : StageChoices P) {n : ℕ} (A : Fin n → P)
    (next : P) (f : Ordinary) :
    columns D (Fin.snoc A next) f = columns D A f + Finsupp.single n
      (D.order next f.val (mark false) - D.order next f.val (mark true)) := by
  unfold columns
  rw [Fin.sum_univ_castSucc]
  simp

private theorem columns_apply {P : Type*} (D : StageChoices P) {n : ℕ} (A : Fin n → P)
    (f : Ordinary) (j : ℕ) :
    columns D A f j = if h : j < n then D.order (A ⟨j,h⟩) f.val (mark false) -
      D.order (A ⟨j,h⟩) f.val (mark true) else 0 := by
  classical
  unfold columns
  rw [Finsupp.finsetSum_apply]
  by_cases h : j < n
  · simp only [h, dite_true]
    rw [Finset.sum_eq_single (⟨j,h⟩ : Fin n)]
    · simp
    · intro b _ hb
      exact Finsupp.single_eq_of_ne (fun he => hb (Fin.ext he.symm))
    · simp
  · simp only [h, dite_false]
    exact Finset.sum_eq_zero fun b _ => Finsupp.single_eq_of_ne (fun he => h (he ▸ b.isLt))

private theorem columns_support {P : Type*} (D : StageChoices P) {n : ℕ} (A : Fin n → P)
    (f : Ordinary) : (columns D A f).support ⊆ Finset.range n := by
  intro i hi
  by_contra h
  rw [Finset.mem_range] at h
  exact (Finsupp.mem_support_iff.mp hi) (by simp [columns_apply, h])

private def seen {n : ℕ} (raw : Fin n → Ordinary) : Finset Ordinary :=
  Finset.univ.image raw ∪ (Finset.range n).image ordinary

private theorem seen_snoc {n : ℕ} (raw : Fin n → Ordinary) (f : Ordinary) :
    seen (Fin.snoc raw f) = insert f (insert (ordinary n) (seen raw)) := by
  ext h
  simp only [seen, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.range_add_one, Finset.image_insert, Finset.mem_insert]
  constructor
  · rintro (⟨i, hi⟩ | hi)
    · induction i using Fin.lastCases with
      | last => exact Or.inl (by simpa using hi.symm)
      | cast i => exact Or.inr (Or.inr (Or.inl ⟨i,by simpa using hi⟩))
    · tauto
  · rintro (rfl | rfl | ⟨i, hi⟩ | h)
    · exact Or.inl ⟨Fin.last _, Fin.snoc_last ..⟩
    · tauto
    · exact Or.inl ⟨i.castSucc, by simpa using hi⟩
    · tauto

private structure History {P : Type*} (D : StageChoices P) (n : ℕ) where
  places : Fin n → P
  raw : Fin n → Ordinary
  increasing : StrictMono (D.prime ∘ places)
  integral : ∀ f ∈ seen raw, ∃ z : ℤ, totalWeight (columns D places f) = z

private structure Extension {P : Type*} {n : ℕ} (D : StageChoices P) (h : History D n) where
  place : P
  polynomial : Ordinary
  prime_gt : ∀ i, D.prime (h.places i) < D.prime place
  degree_gt : ∀ i, (h.raw i).val.natDegree < polynomial.val.natDegree
  old_unit : ∀ f ∈ seen h.raw, ∀ x, D.order place f.val x = 0
  new_weight : ∃ z : ℤ, totalWeight (columns D (Fin.snoc h.places place) (ordinary n)) = z
  realizes : ∀ i : Fin (n+1), ∀ x, D.order ((Fin.snoc h.places place : Fin (n+1) → P) i) polynomial.val x =
    request n i.val x

private theorem strict_snoc {α β : Type*} [Preorder β] {n : ℕ} (f : α → β) (a : Fin n → α)
    (b : α) (h : StrictMono (f ∘ a)) (hb : ∀ i, f (a i) < f b) :
    StrictMono (f ∘ Fin.snoc a b) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact (lt_irrefl _ hij).elim
    | cast i => simpa using hb i
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact ((not_lt_of_ge (Fin.le_last j.castSucc)) hij).elim
    | cast i => simpa using h (show i < j from hij)

private def extend {P : Type*} {n : ℕ} (D : StageChoices P) (h : History D n) :
    Extension D h := by
  let frozen := seen h.raw
  let N := Finset.univ.sup (D.prime ∘ h.places)
  let f := ordinary n
  have hs (i : Fin n) : D.prime (h.places i) ≤ N := Finset.le_sup (f := D.prime ∘ h.places) (Finset.mem_univ i)
  have pick : ∃ A, N < D.prime A ∧ (∀ g ∈ frozen, ∀ x, D.order A g.val x = 0) ∧
      ∃ z : ℤ, totalWeight (columns D (Fin.snoc h.places A) f) = z := by
    by_cases hf : f ∈ frozen
    · obtain ⟨A, ha, hu⟩ := D.safe frozen N
      obtain ⟨z, hz⟩ := h.integral f hf
      exact ⟨A, ha, hu, z, by simpa [columns_snoc, hu f hf] using hz⟩
    · obtain ⟨k, hk⟩ := exists_correcting_difference _ n (columns_support D h.places f)
      obtain ⟨A, ha, hu, hc⟩ := D.correct frozen f hf k N
      exact ⟨A, ha, hu, 0, by simpa [columns_snoc, hc] using hk⟩
  let A := pick.choose
  have hp (i : Fin n) : D.prime (h.places i) < D.prime A := (hs i).trans_lt pick.choose_spec.1
  let L := Finset.univ.sup (fun i : Fin n => (h.raw i).val.natDegree) + 1
  have select := D.approximate (Fin.snoc h.places A)
    (strict_snoc _ _ _ h.increasing hp).injective (request n) L
  exact ⟨A, select.choose, hp, fun i => (Nat.lt_succ_of_le
    (Finset.le_sup (f := fun i : Fin n => (h.raw i).val.natDegree) (Finset.mem_univ i))).trans_le
      select.choose_spec.1, pick.choose_spec.2.1, pick.choose_spec.2.2, select.choose_spec.2⟩

private theorem columns_of_request {P : Type*} (D : StageChoices P) {n : ℕ} (A : Fin n → P)
    (f : Ordinary) (g : Profile) (hg : g.support ⊆ Finset.range n)
    (hv : ∀ i x, D.order (A i) f.val x = g i.val x) :
    columns D A f = markedDifference g := by
  ext j
  by_cases hj : j < n
  · simp [columns_apply, hj, hv]
  · have hzero : g j = 0 := Finsupp.notMem_support_iff.mp
      (fun hj' => hj (Finset.mem_range.mp (hg hj')))
    simp [columns_apply, hj, hzero]

private def start {P : Type*} (D : StageChoices P) : History D 0 where
  places := Fin.elim0
  raw := Fin.elim0
  increasing := fun i => Fin.elim0 i
  integral := by simp [seen]

private def advance {P : Type*} (D : StageChoices P) {n : ℕ} (h : History D n) : History D (n+1) where
  places := Fin.snoc h.places (extend D h).place
  raw := Fin.snoc h.raw (extend D h).polynomial
  increasing := strict_snoc _ _ _ h.increasing (extend D h).prime_gt
  integral := by
    intro f hf
    rw [seen_snoc] at hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rw [columns_of_request _ _ _ _ (request_support n) (extend D h).realizes]
      exact (request_admissible n).2
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact (extend D h).new_weight
    · obtain ⟨z, hz⟩ := h.integral f hf
      exact ⟨z, by simpa [columns_snoc, (extend D h).old_unit f hf] using hz⟩

private def history {P : Type*} (D : StageChoices P) : (n : ℕ) → History D n
  | 0 => start D
  | n+1 => advance D (history D n)

namespace StageChoices

variable {P : Type*} (D : StageChoices P)

/-- The actual sequence chosen by the fair schedule. -/
def places (n : ℕ) : P := (extend D (history D n)).place

/-- The pole polynomial selected at stage n is monic and irreducible. -/
def raw (n : ℕ) : Ordinary := (extend D (history D n)).polynomial

private theorem prefix_places (n : ℕ) (i : Fin n) : (history D n).places i = D.places i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => simp [history, advance, places]
    | cast i => simpa [history, advance] using ih i

private theorem prefix_raw (n : ℕ) (i : Fin n) : (history D n).raw i = D.raw i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => simp [history, advance, raw]
    | cast i => simpa [history, advance] using ih i

theorem primes_strict : StrictMono (D.prime ∘ D.places) := by
  intro i j hij
  simpa [prefix_places, places] using (extend D (history D j)).prime_gt (⟨i,hij⟩ : Fin j)

theorem degrees_strict : StrictMono (fun n => (D.raw n).val.natDegree) := by
  intro i j hij
  simpa [prefix_raw, raw] using (extend D (history D j)).degree_gt (⟨i,hij⟩ : Fin j)

private theorem raw_orders (j n : ℕ) (x : Fiber) :
    D.order (D.places n) (D.raw j).val x = request j n x := by
  by_cases hn : n < j+1
  · let i := (⟨n,hn⟩ : Fin (j+1))
    have hh := (extend D (history D j)).realizes i x
    change D.order ((history D (j+1)).places i) (D.raw j).val x = _ at hh
    rw [prefix_places] at hh
    exact hh
  · have hj : j < n := by omega
    have hf : D.raw j ∈ seen (history D n).raw :=
      Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨⟨j,hj⟩, Finset.mem_univ _, prefix_raw D n _⟩)
    have hu := (extend D (history D n)).old_unit (D.raw j) hf x
    have hz : request j n = 0 := Finsupp.notMem_support_iff.mp
      (fun h => hn (Finset.mem_range.mp (request_support j h)))
    simpa only [hz, LocallyConstant.zero_apply, places] using hu

/-- The realized profile of every pole has even pointwise orders and integral weight. -/
theorem raw_profile (j : ℕ) :
    ∃ g : Profile, Admissible g ∧ ∀ n x, D.order (D.places n) (D.raw j).val x = g n x :=
  ⟨request j, request_admissible j, raw_orders D j⟩

/-- Each admissible request is met exactly on every fiber, including later fibers. -/
theorem realizes_profile (g : Profile) (hg : Admissible g) :
    ∃ j, ∀ n x, D.order (D.places n) (D.raw j).val x = g n x := by
  obtain ⟨j, hj⟩ := request_surjective g hg
  exact ⟨j, fun n x => (raw_orders D j n x).trans (hj ▸ rfl)⟩

/-- Every rational monic irreducible is a unit along all sufficiently late
fibers and has integral marked weight, whether it entered as a request or
as an ordinary irreducible. -/
theorem ordinary_profile (f : Ordinary) :
    ∃ (N : ℕ) (d : ℕ →₀ ℤ), (∀ n ≥ N, ∀ x, D.order (D.places n) f.val x = 0) ∧
      (∀ n, d n = D.order (D.places n) f.val (mark false) -
        D.order (D.places n) f.val (mark true)) ∧ ∃ z : ℤ, totalWeight d = z := by
  obtain ⟨j, hj⟩ := (exists_surjective_nat Ordinary).choose_spec f
  change ordinary j = f at hj
  have hmem (n : ℕ) (hn : j < n) : f ∈ seen (history D n).raw :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hn, hj⟩)
  have hu (n : ℕ) (hn : j+1 ≤ n) (x : Fiber) : D.order (D.places n) f.val x = 0 :=
    (extend D (history D n)).old_unit f (hmem n hn) x
  let h := history D (j+1)
  refine ⟨j+1, columns D h.places f, hu, ?_, h.integral f (hmem _ (Nat.lt_succ_self j))⟩
  intro n
  by_cases hn : n < j+1
  · simp [columns_apply, hn, h, prefix_places]
  · simp [columns_apply, hn, hu n (Nat.le_of_not_gt hn)]

end StageChoices
end UnconditionalCounterexample.Hierarchy.Weighted
