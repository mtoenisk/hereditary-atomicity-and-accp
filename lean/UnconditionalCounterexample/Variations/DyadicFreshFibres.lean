import UnconditionalCounterexample.Variations.DyadicLedger
import UnconditionalCounterexample.Variations.RegularReservations

/-!
# Labelling and combining the finite births of a dyadic stage

An on-demand list of regular labels receives distinct fresh primes. Each
primary and guard preserves the old raw units. Fresh auxiliary and regular
families can be glued without changing either family's roles or site data.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open GuardSupport RecursivePrefix Univariate Polynomial

/-- Centre, channel and regular index. -/
abbrev RegularLabel := Bool × Bool × ℕ

def RegularLabel.role (l : RegularLabel) : FibreRole := .regular l.1 l.2.1 l.2.2

private theorem regularRole_injective : Function.Injective RegularLabel.role := by
  rintro ⟨a,b,c⟩ ⟨d,e,f⟩ h
  cases h
  rfl

namespace FreshFibres
variable {n : ℕ} {m : Ledger} {P : Prefix n}

section Regular
variable {labels : Finset RegularLabel} {centre : RegularLabel → ℕ}
    {frozen : RegularLabel → Finset ℚ[X]}
    (entries : (i : labels) → RegularReservations.Entry P (centre i.val) (frozen i.val))
    (inj : Function.Injective fun i => (entries i).prime)

private def labelAt (p : PrimeIndex) (hp : p ∈ (RegularReservations.Entry.births entries inj).primes) :
    labels := (Finset.mem_image.mp hp).choose

private theorem prime_labelAt (p : PrimeIndex) (hp : p ∈ (RegularReservations.Entry.births entries inj).primes) :
    (entries (labelAt entries inj p hp)).prime = p := (Finset.mem_image.mp hp).choose_spec.2

/-- Convert a finite regular reservation into the labelled birth required by
the dyadic ledger. -/
def regular (hfresh : ∀ l ∈ labels, ∀ p, m.role p ≠ some l.role) : FreshFibres m P where
  births := RegularReservations.Entry.births entries inj
  role p hp := some (labelAt entries inj p hp).val.role
  paired p hp := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    rw [RegularReservations.Entry.births_site]
    rfl
  primary_before p hp _ j := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    rw [RegularReservations.Entry.births_site]
    exact ((entries i).old_units j).1
  new_regular p hp c k i he q := by
    rw [← Option.some.inj he]
    exact hfresh _ (labelAt entries inj p hp).property q
  distinct_regular p hp q hq _ _ _ he he' := by
    have h : labelAt entries inj p hp = labelAt entries inj q hq :=
      Subtype.ext (regularRole_injective (Option.some.inj (he.trans he'.symm)))
    exact (prime_labelAt entries inj p hp).symm.trans
      ((congrArg (fun i => (entries i).prime) h).trans (prime_labelAt entries inj q hq))

theorem regular_role (hfresh : ∀ l ∈ labels, ∀ p, m.role p ≠ some l.role) (i : labels)
    (hi : (entries i).prime ∈ (regular entries inj hfresh).births.primes) :
    (regular entries inj hfresh).role _ hi = some i.val.role := by
  have he := inj (prime_labelAt entries inj (entries i).prime hi)
  change some (labelAt entries inj (entries i).prime hi).val.role = _
  rw [he]

end Regular

/-- A finite family whose labels have been screened against the supplied frozen
polynomials and whose primes avoid an arbitrary finite list. -/
theorem exists_regular (m : Ledger) (P : Prefix n) (labels : Finset RegularLabel)
    (hfresh : ∀ l ∈ labels, ∀ p, m.role p ≠ some l.role)
    (frozen : RegularLabel → Finset ℚ[X]) (hmonic : ∀ l f, f ∈ frozen l → f.Monic)
    (haway : ∀ l f, f ∈ frozen l → f.eval (if l.1 then (1:ℚ) else 0) ≠ 0)
    (avoid : Finset PrimeIndex) (cutoff : ℕ) :
    ∃ a : FreshFibres m P, Disjoint a.births.primes avoid ∧
      (∀ p hp, ∃ l ∈ labels, a.role p hp = some l.role) ∧
      ∀ l ∈ labels, ∃ p, ∃ hp : p ∈ a.births.primes, cutoff < p.val ∧
        a.role p hp = some l.role ∧ ∀ f ∈ frozen l,
          ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) ((a.births.site p hp).branch false)‖ = 1 ∧
          ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) ((a.births.site p hp).branch true)‖ = 1 := by
  let c (l : RegularLabel) : ℕ := if l.1 then 1 else 0
  have hc (l : RegularLabel) : c l = 0 ∨ c l = 1 := by cases h : l.1 <;> simp [c,h]
  have hav (l : RegularLabel) (f : ℚ[X]) (hf : f ∈ frozen l) : f.eval (c l : ℚ) ≠ 0 := by
    cases h : l.1 <;> simpa [c,h] using haway l f hf
  obtain ⟨e, hinj, hnew⟩ := RegularReservations.exists_family P labels c hc frozen hmonic hav avoid cutoff
  let a := regular e hinj hfresh
  refine ⟨a, Finset.disjoint_left.mpr ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (hnew i).2
  · intro p hp
    exact ⟨(labelAt e hinj p hp).val, (labelAt e hinj p hp).property, rfl⟩
  · intro l hl
    let i : labels := ⟨l,hl⟩
    have hp : (e i).prime ∈ a.births.primes := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    refine ⟨(e i).prime, hp, (hnew i).1, regular_role e hinj hfresh i hp, ?_⟩
    intro f hf
    simp only [a, regular]
    rw [RegularReservations.Entry.births_site]
    exact (e i).frozen_units f hf

section Union
variable (a b : FreshFibres m P) (hd : Disjoint a.births.primes b.births.primes)

private def unionRole (p : PrimeIndex) (hp : p ∈ (a.births.union b.births hd).primes) : Option FibreRole :=
  if h : p ∈ a.births.primes then a.role p h else b.role p ((Finset.mem_union.mp hp).resolve_left h)

/-- Combine arbitrary regular requests with an auxiliary-only calibration batch. -/
def unionAux (haux : ∀ p hp c k i, b.role p hp ≠ some (.regular c k i)) : FreshFibres m P where
  births := a.births.union b.births hd
  role := unionRole a b hd
  paired p hp := by
    by_cases h : p ∈ a.births.primes
    · rw [a.births.union_site_left b.births hd p h, unionRole, dite_eq_left h]
      exact a.paired _ h
    · let hb := (Finset.mem_union.mp hp).resolve_left h
      rw [a.births.union_site_right b.births hd p hb, unionRole, dite_eq_right h]
      exact b.paired _ hb
  primary_before p hp h j := by
    by_cases ha : p ∈ a.births.primes
    · rw [a.births.union_site_left b.births hd p ha] at h ⊢
      exact a.primary_before p ha h j
    · let hb := (Finset.mem_union.mp hp).resolve_left ha
      rw [a.births.union_site_right b.births hd p hb] at h ⊢
      exact b.primary_before p hb h j
  new_regular p _ c k i he := by
    by_cases ha : p ∈ a.births.primes
    · exact a.new_regular p ha c k i (by simpa [unionRole,ha] using he)
    · exact False.elim (haux p _ c k i (by simpa [unionRole,ha] using he))
  distinct_regular p _ q _ c k i h₁ h₂ := by
    by_cases hp : p ∈ a.births.primes
    · by_cases hq : q ∈ a.births.primes
      · exact a.distinct_regular p hp q hq c k i (by simpa [unionRole,hp] using h₁)
          (by simpa [unionRole,hq] using h₂)
      · exact False.elim (haux q _ c k i (by simpa [unionRole,hq] using h₂))
    · exact False.elim (haux p _ c k i (by simpa [unionRole,hp] using h₁))

theorem unionAux_role_left (haux : ∀ p hp c k i, b.role p hp ≠ some (.regular c k i))
    (p : PrimeIndex) (hp : p ∈ a.births.primes) :
    (a.unionAux b hd haux).role p (Finset.mem_union_left _ hp) = a.role p hp := by
  simp [unionAux, unionRole, hp]

theorem unionAux_role_right (haux : ∀ p hp c k i, b.role p hp ≠ some (.regular c k i))
    (p : PrimeIndex) (hp : p ∈ b.births.primes) :
    (a.unionAux b hd haux).role p (Finset.mem_union_right _ hp) = b.role p hp := by
  have h : p ∉ a.births.primes := fun hm => Finset.disjoint_left.mp hd hm hp
  simp [unionAux, unionRole, h]

end Union
end FreshFibres
end UnconditionalCounterexample.Variations.DyadicLedger
