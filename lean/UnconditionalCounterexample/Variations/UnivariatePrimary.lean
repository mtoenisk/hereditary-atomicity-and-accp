import UnconditionalCounterexample.Variations.UnivariateBirths
import UnconditionalCounterexample.Variations.UnivariateGuards

/-!
# Allocating a labelled primary prime after a finite polynomial prefix

A single primary can be requested at any stage, in either residue class and
with any positive order of displacement. Both members of its fibre are
units on the full preceding polynomial prefix.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.UnivariatePrimary

open Polynomial RecursivePrefix GuardSupport PaperGuardStages Univariate

/-- A primary chosen for colour `c` and order `k` carries its guard and the
old evaluation certificates required to insert it in the permanent schedule. -/
structure At {n : ℕ} (P : Prefix n) (c : Bool) (k : ℕ) where
  prime : PrimeIndex
  odd : 2 < prime.val
  fresh : prime ∉ P.state.assignment.primes
  guard : Guard prime
  birth_eq : guard.birth = n
  guard_good : UnivariateGuards.Good guard
  primary : Primary prime guard.value
  hr : PadicInt.toZMod primary.val = if c then 1 else 0
  hv : (primary.val.val - (if c then 1 else 0)).valuation = k
  old_primary_units : ∀ j : Fin n,
    ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[prime.val]) primary.val.val‖ = 1
  old_guard_units : ∀ j : Fin n,
    ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[prime.val]) guard.value.val‖ = 1

theorem exists_at {n : ℕ} (P : Prefix n) (c : Bool) (k : ℕ) (hk : 0 < k)
    (avoid : Finset PrimeIndex) (bound : ℕ) :
    ∃ a : At P c k, bound < a.prime.val ∧ a.prime ∉ avoid := by
  let t : ℕ := if c then 1 else 0
  have ht : t = 0 ∨ t = 1 := by cases c <;> simp [t]
  have hval (j : Fin n) : (P.raw j).eval (t : ℚ) ≠ 0 :=
    (P.irreducible j).not_isRoot_of_natDegree_ne_one (by have := P.degree_five j; omega)
  obtain ⟨p, hb, hodd, hf, hav, α, g, hα, hr, hv, hbirth, hguard, hu, hold⟩ :=
    UnivariateCentres.exists_fresh_pair P.state.assignment avoid P.raw P.monic
      P.current_support t k n bound ht hk hval
  have hdiff := (padicInt_isUnit_iff_toZMod_ne_zero _).mp hu
  rw [map_sub, sub_ne_zero] at hdiff
  exact ⟨⟨p, hodd, hf, g, hbirth, ⟨fun h => (by omega), fun _ => hguard⟩,
    ⟨α, hα, hdiff.symm⟩, by cases c <;> simpa [t] using hr,
    by cases c <;> simpa [t] using hv,
    fun j => (hold j).1, fun j => (hold j).2⟩, hb, hav⟩

/-- The requested primary can always be chosen beyond the current cutoff. -/
def choose {n : ℕ} (P : Prefix n) (c : Bool) (k : ℕ) (hk : 0 < k) : At P c k :=
  (exists_at P c k hk ∅ P.state.cutoff).choose

namespace At

variable {n : ℕ} {P : Prefix n} {c : Bool} {k : ℕ} (a : At P c k)

def births : Births P :=
  Births.singleton P a.prime a.fresh a.guard a.birth_eq a.old_guard_units (some a.primary)

theorem site_eq (hp : a.prime ∈ a.births.primes) :
    a.births.site a.prime hp = ⟨a.guard.value, a.guard.transcendental, some a.primary⟩ := rfl

theorem requested_good (p : PrimeIndex) (hp : p ∈ a.births.primes) :
    UnivariateGuards.Good (a.births.guard p hp) := by
  have h : p = a.prime := Finset.mem_singleton.mp hp
  subst p
  exact a.guard_good

end At

end UnconditionalCounterexample.Variations.UnivariatePrimary
