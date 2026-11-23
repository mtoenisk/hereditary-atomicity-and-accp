import UnconditionalCounterexample.Variations.FrozenSites

/-!
# Reserving finite lists of dyadic regular sites on demand

Every newly required regular index gets its own fresh odd prime, screened against
the actual raw prefix and the finite frozen polynomials that do not vanish at
its centre. All of these pairs enter one batch and are disjoint from any
previously reserved set of auxiliary primes.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.RegularReservations

open Polynomial GuardSupport PaperGuardStages RecursivePrefix Univariate

/-- A fresh regular coordinate with all its screening certificates. -/
structure Entry {n : ℕ} (P : Prefix n) (c : ℕ) (frozen : Finset ℚ[X]) where
  prime : PrimeIndex
  fresh : prime ∉ P.state.assignment.primes
  guard : Guard prime
  birth : guard.birth = n
  guard_residue_ne_one : PadicInt.toZMod guard.value ≠ 1
  primary : Primary prime guard.value
  odd : 2 < prime.val
  residue : PadicInt.toZMod primary.val = c
  order : (primary.val.val - c).valuation = 1
  old_units : ∀ j : Fin n, ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[prime.val]) primary.val.val‖ = 1 ∧
    ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[prime.val]) guard.value.val‖ = 1
  frozen_units : ∀ f ∈ frozen, ‖f.eval₂ (algebraMap ℚ ℚ_[prime.val]) primary.val.val‖ = 1 ∧
    ‖f.eval₂ (algebraMap ℚ ℚ_[prime.val]) guard.value.val‖ = 1

theorem exists_entry {n : ℕ} (P : Prefix n) (c : ℕ) (hc : c = 0 ∨ c = 1)
    (frozen : Finset ℚ[X]) (hmonic : ∀ f ∈ frozen, f.Monic)
    (haway : ∀ f ∈ frozen, f.eval (c : ℚ) ≠ 0) (avoid : Finset PrimeIndex) (cutoff : ℕ) :
    ∃ e : Entry P c frozen, cutoff < e.prime.val ∧ e.prime ∉ avoid := by
  obtain ⟨p,g,α,hf,ha,hb,hodd,hbirth,hguard,hr,ho,hu,hfreeze⟩ :=
    exists_regular_site_avoiding P frozen hmonic c hc haway avoid cutoff
  exact ⟨⟨p,hf,g,hbirth,hguard,α,hodd,hr,ho,hu,hfreeze⟩,hb,ha⟩

/-- Realize an arbitrary finite set of on-demand requests, at distinct fresh
primes. Different requests may have different centres and frozen lists. -/
theorem exists_family {I : Type*} {n : ℕ} (P : Prefix n) (labels : Finset I)
    (centre : I → ℕ) (hc : ∀ i, centre i = 0 ∨ centre i = 1)
    (frozen : I → Finset ℚ[X]) (hmonic : ∀ i f, f ∈ frozen i → f.Monic)
    (haway : ∀ i f, f ∈ frozen i → f.eval (centre i : ℚ) ≠ 0)
    (avoid : Finset PrimeIndex) (cutoff : ℕ) :
    ∃ e : (i : labels) → Entry P (centre i.val) (frozen i.val),
      Function.Injective (fun i => (e i).prime) ∧ ∀ i, cutoff < (e i).prime.val ∧ (e i).prime ∉ avoid := by
  classical
  induction labels using Finset.induction_on with
  | empty =>
    let e (i : (∅ : Finset I)) : Entry P (centre i.val) (frozen i.val) := isEmptyElim i
    exact ⟨e, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  | @insert a L ha ih =>
    obtain ⟨e, hInj, hgood⟩ := ih
    let oldPrimes := (Finset.univ : Finset ↥L).image (fun i => (e i).prime)
    obtain ⟨ea, hb, hav⟩ := exists_entry P (centre a) (hc a) (frozen a)
      (hmonic a) (haway a) (avoid ∪ oldPrimes) cutoff
    have fresh (i : L) : ea.prime ≠ (e i).prime := by
      intro h
      exact hav (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩))
    let add (i : ↥(insert a L)) : Entry P (centre i.val) (frozen i.val) :=
      if h : i.val = a then h.symm ▸ ea
      else e ⟨i.val, (Finset.mem_insert.mp i.property).resolve_left h⟩
    have atA (i : ↥(insert a L)) (h : i.val = a) : (add i).prime = ea.prime := by
      rcases i with ⟨v, hv⟩
      change v = a at h
      subst v
      simp [add]
    have atL (i : ↥(insert a L)) (h : i.val ≠ a) :
        (add i).prime = (e ⟨i.val, (Finset.mem_insert.mp i.property).resolve_left h⟩).prime := by
      simp [add, h]
    refine ⟨add, ?_, ?_⟩
    · intro i j hij
      change (add i).prime = (add j).prime at hij
      by_cases hi : i.val = a <;> by_cases hj : j.val = a
      · exact Subtype.ext (hi.trans hj.symm)
      · rw [atA i hi, atL j hj] at hij
        exact False.elim (fresh _ hij)
      · rw [atL i hi, atA j hj] at hij
        exact False.elim (fresh _ hij.symm)
      · rw [atL i hi, atL j hj] at hij
        exact Subtype.ext (congrArg (fun z : L => z.val) (hInj hij))
    · intro i
      by_cases h : i.val = a
      · rw [atA i h]
        exact ⟨hb, fun hi => hav (Finset.mem_union_left _ hi)⟩
      · rw [atL i h]
        exact hgood _

namespace Entry
variable {I : Type*} [Fintype I] {n : ℕ} {P : Prefix n} {c : I → ℕ} {frozen : I → Finset ℚ[X]}
    (e : (i : I) → Entry P (c i) (frozen i)) (hinj : Function.Injective (fun i => (e i).prime))

def primeSet : Finset PrimeIndex := Finset.univ.image (fun i => (e i).prime)

private def label (p : PrimeIndex) (hp : p ∈ primeSet e) : I := (Finset.mem_image.mp hp).choose

private theorem prime_label (p : PrimeIndex) (hp : p ∈ primeSet e) : (e (label e p hp)).prime = p :=
  (Finset.mem_image.mp hp).choose_spec.2

def entrySite (i : I) : Site (e i).prime :=
  ⟨(e i).guard.value, (e i).guard.transcendental, some (e i).primary⟩

private def dataAt (p : PrimeIndex) (hp : p ∈ primeSet e) :
    Σ g : Guard p, Option (Primary p g.value) :=
  prime_label e p hp ▸ ⟨(e (label e p hp)).guard, some (e (label e p hp)).primary⟩

include hinj in
private theorem dataAt_eq (i : I) (hp : (e i).prime ∈ primeSet e) :
    dataAt e (e i).prime hp = ⟨(e i).guard, some (e i).primary⟩ := by
  have he : label e (e i).prime hp = i := hinj (prime_label e _ hp)
  generalize hx : label e (e i).prime hp = j at he
  unfold dataAt
  generalize_proofs heq
  revert heq
  rw [hx, he]
  intro _
  rfl

/-- Turn the whole finite regular reservation into a single ordinary batch
request, with its actual guards and primaries. -/
def births : Births P where
  primes := primeSet e
  fresh p hp := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (e i).fresh
  guard p hp := (dataAt e p hp).1
  primary p hp := (dataAt e p hp).2
  birth_eq p hp := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    rw [dataAt_eq e hinj i]
    exact (e i).birth
  old_units p hp j := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    rw [dataAt_eq e hinj i]
    exact ((e i).old_units j).2

theorem births_site (i : I) :
    let hp : (e i).prime ∈ (births e hinj).primes := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    (births e hinj).site (e i).prime hp = entrySite e i := by
  intro hp
  exact congrArg (fun d : Σ g : Guard (e i).prime, Option (Primary (e i).prime g.value) =>
    (⟨d.1.value, d.1.transcendental, d.2⟩ : Site (e i).prime)) (dataAt_eq e hinj i hp)

end Entry

end UnconditionalCounterexample.Variations.RegularReservations
