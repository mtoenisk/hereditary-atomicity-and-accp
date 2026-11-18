import Factorization.Hierarchy
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.Order.OrderIsoNat

/-!
# ACCP and actual principal ideal chains

These statements identify mathlib's strict-divisibility ACCP with reverse
well-founded inclusion on principal ideals, eventual stabilization of increasing
principal-ideal chains, and the absence of strictly increasing such chains.
-/

namespace Factorization

universe u

variable {R : Type u} [CommSemiring R] [IsDomain R]

/-- ACCP is well-founded reverse inclusion on the actual principal ideals. -/
theorem wfDvdMonoid_iff_principalIdeals_wellFounded :
    WfDvdMonoid R ↔ {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·) := by
  constructor
  · intro hR
    let : WfDvdMonoid R := hR
    exact Ideal.setOfPred_isPrincipal_wellFoundedOn_gt
  · exact WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt

/-- ACCP holds exactly when every increasing sequence of principal ideals
eventually stabilizes. -/
theorem wfDvdMonoid_iff_principalIdealChains_stabilize :
    WfDvdMonoid R ↔ ∀ I : ℕ → Ideal R,
      (∀ n, (I n).IsPrincipal) → Monotone I →
        ∃ N, ∀ n, N ≤ n → I N = I n := by
  constructor
  · intro hR I hI hmono
    let : WellFoundedGT {J : Ideal R // J.IsPrincipal} :=
      wfDvdMonoid_iff_principalIdeals_wellFounded.mp hR
    let a : ℕ →o {J : Ideal R // J.IsPrincipal} :=
      ⟨fun n => ⟨I n, hI n⟩, hmono⟩
    obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition a
    exact ⟨N, fun n hn => congrArg Subtype.val (hN n hn)⟩
  · intro h
    apply wfDvdMonoid_iff_principalIdeals_wellFounded.mpr
    change WellFoundedGT {J : Ideal R // J.IsPrincipal}
    apply wellFoundedGT_iff_monotone_chain_condition.mpr
    intro a
    obtain ⟨N, hN⟩ := h (fun n => (a n).val) (fun n => (a n).property) a.monotone
    exact ⟨N, fun n hn => Subtype.ext (hN n hn)⟩

/-- An explicit ACCP hypothesis stabilizes any increasing principal-ideal chain. -/
theorem principalIdealChains_stabilize (hR : WfDvdMonoid R)
    (I : ℕ → Ideal R) (hI : ∀ n, (I n).IsPrincipal) (hmono : Monotone I) :
    ∃ N, ∀ n, N ≤ n → I N = I n :=
  wfDvdMonoid_iff_principalIdealChains_stabilize.mp hR I hI hmono

/-- In a nonzero divisibility chain in an ACCP domain, all sufficiently late
ratios are units. The original chain is not assumed to be strict. -/
theorem eventually_isUnit_ratios_of_wfDvdMonoid (hR : WfDvdMonoid R)
    (x a : ℕ → R) (hx : ∀ n, x n ≠ 0)
    (hxa : ∀ n, x n = x (n + 1) * a n) :
    ∃ N, ∀ n, N ≤ n → IsUnit (a n) := by
  let I : ℕ → Ideal R := fun n => Ideal.span {x n}
  have hI : ∀ n, (I n).IsPrincipal := fun n => ⟨x n, rfl⟩
  have hmono : Monotone I := by
    apply monotone_nat_of_le_succ
    intro n
    exact Ideal.span_singleton_le_span_singleton.mpr ⟨a n, hxa n⟩
  obtain ⟨N, hN⟩ := principalIdealChains_stabilize hR I hI hmono
  refine ⟨N, ?_⟩
  intro n hn
  have heq : I n = I (n + 1) :=
    (hN n hn).symm.trans (hN (n + 1) (hn.trans (Nat.le_succ n)))
  have hback : x n ∣ x (n + 1) :=
    Ideal.span_singleton_le_span_singleton.mp heq.ge
  obtain ⟨b, hb⟩ := hback
  have hab : a n * b = 1 := by
    apply mul_left_cancel₀ (hx (n + 1))
    calc
      x (n + 1) * (a n * b) = x n * b := by rw [← mul_assoc, ← hxa n]
      _ = x (n + 1) := hb.symm
      _ = x (n + 1) * 1 := (mul_one _).symm
  exact isUnit_iff_dvd_one.mpr ⟨b, hab.symm⟩

/-- Failure of ACCP is equivalent to a strictly increasing sequence of actual
principal ideals. -/
theorem not_wfDvdMonoid_iff_exists_strictMono_principalIdealChain :
    ¬ WfDvdMonoid R ↔ ∃ I : ℕ → Ideal R,
      (∀ n, (I n).IsPrincipal) ∧ StrictMono I := by
  constructor
  · intro hR
    obtain ⟨x, a, hx, ha, hxa⟩ := not_wfDvdMonoid_iff_exists_nonunit_chain.mp hR
    refine ⟨fun n => Ideal.span {x n}, fun n => ⟨x n, rfl⟩, ?_⟩
    apply strictMono_nat_of_lt_succ
    intro n
    exact Ideal.span_singleton_lt_span_singleton.mpr ⟨hx (n + 1), a n, ha n, hxa n⟩
  · rintro ⟨I, hI, hmono⟩ hR
    obtain ⟨N, hN⟩ := principalIdealChains_stabilize hR I hI hmono.monotone
    exact (hmono (Nat.lt_succ_self N)).ne (hN (N + 1) (Nat.le_succ N))

end Factorization
