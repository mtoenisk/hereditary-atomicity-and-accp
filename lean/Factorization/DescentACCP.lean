import Factorization.Descent
import Factorization.PrincipalIdeals

/-!
# ACCP descent with bounded ambient-unit factors

An infinite source chain maps to an eventually stationary target principal-ideal
chain. Every sufficiently late ratio is then a target unit. Those source
nonunits would give arbitrarily many ambient-unit factors of one fixed source
element, contradicting its budget.
-/

namespace Factorization

universe u v

section Monoids

variable {R : Type u} {S : Type v} [CommMonoid R] [CommMonoid S]

private theorem exists_factorization_large_ambientUnitCount
    (f : R →* S) (x a : ℕ → R) (ha : ∀ n, ¬ IsUnit (a n))
    (hfa : ∀ n, IsUnit (f (a n))) (hxa : ∀ n, x n = x (n + 1) * a n)
    (n m : ℕ) : ∃ t : Multiset R,
      (∀ b ∈ t, ¬ IsUnit b) ∧ Associated t.prod (x m) ∧
        n ≤ ambientUnitFactorCount f t := by
  classical
  induction n generalizing m with
  | zero =>
    refine ⟨{x m}, ?_, by simp, Nat.zero_le _⟩
    have hx : ¬ IsUnit (x m) := by
      rw [hxa m]
      exact fun hu => ha m (isUnit_of_mul_isUnit_right hu)
    simpa using hx
  | succ n ih =>
    obtain ⟨t, ht, htx, hcount⟩ := ih (m + 1)
    refine ⟨a m ::ₘ t, ?_, ?_, ?_⟩
    · intro b hb
      rcases Multiset.mem_cons.mp hb with rfl | hb
      · exact ha m
      · exact ht b hb
    · simpa only [Multiset.prod_cons, hxa m, mul_comm (a m)] using htx.mul_left (a m)
    · simpa [ambientUnitFactorCount, hfa m] using Nat.succ_le_succ hcount

end Monoids

section Domains

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S]

omit [IsDomain R] in
/-- ACCP descends along an injective domain map if every nonzero source element
has a bound on source-nonunit factors whose images are target units. -/
theorem wfDvdMonoid_of_boundedAmbientUnitFactors
    (f : R →+* S) (hf : Function.Injective f)
    (hbudget : ∀ x : R, x ≠ 0 → HasBoundedAmbientUnitFactors f.toMonoidHom x)
    (hS : WfDvdMonoid S) : WfDvdMonoid R := by
  classical
  by_contra hR
  obtain ⟨x, a, hx, ha, hxa⟩ := not_wfDvdMonoid_iff_exists_nonunit_chain.mp hR
  have hfx : ∀ n, f (x n) ≠ 0 := by
    intro n hzero
    exact hx n (hf (hzero.trans f.map_zero.symm))
  have hfxa : ∀ n, f (x n) = f (x (n + 1)) * f (a n) := by
    intro n
    rw [hxa n, map_mul]
  obtain ⟨N, hN⟩ := eventually_isUnit_ratios_of_wfDvdMonoid hS
    (fun n => f (x n)) (fun n => f (a n)) hfx hfxa
  obtain ⟨B, hB⟩ := hbudget (x N) (hx N)
  obtain ⟨t, ht, htx, hcount⟩ := exists_factorization_large_ambientUnitCount
    f.toMonoidHom (fun n => x (N + n)) (fun n => a (N + n))
    (fun n => ha (N + n)) (fun n => hN (N + n) (by omega))
    (fun n => by simpa only [Nat.add_assoc] using hxa (N + n)) (B + 1) 0
  have hbound := hB t ht (by simpa only [Nat.add_zero] using htx)
  omega

/-- Ambient ACCP and ambient-unit budgets for every actual subring imply
hereditary ACCP. The budgets remain explicit hypotheses. -/
theorem isHereditarilyACCP_of_boundedAmbientUnitFactors (hR : WfDvdMonoid R)
    (hbudget : ∀ A : Subring R, ∀ x : A, x ≠ 0 →
      HasBoundedAmbientUnitFactors A.subtype.toMonoidHom x) : IsHereditarilyACCP R := by
  intro A
  exact wfDvdMonoid_of_boundedAmbientUnitFactors A.subtype Subtype.val_injective
    (hbudget A) hR

end Domains

end Factorization
