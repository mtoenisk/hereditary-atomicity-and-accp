import UnconditionalCounterexample.Hierarchy.WeightedFiber
import UnconditionalCounterexample.GuardSupport
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Transcendental Cantor fibers in the p-adic integers -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open Polynomial GuardSupport

structure FiberPlace where
  prime : PrimeIndex
  emb : Fiber → ℤ_[prime.val]
  continuous : Continuous emb
  injective : Function.Injective emb
  transcendental : ∀ x, Transcendental ℚ (emb x).val

namespace FiberPlace

def polynomialOrder (P : FiberPlace) (f : ℚ[X]) (x : Fiber) : ℤ :=
  (aeval (P.emb x).val f).valuation

def homeomorph (P : FiberPlace) : Fiber ≃ₜ Set.range P.emb :=
  (P.continuous.isClosedEmbedding P.injective).isEmbedding.toHomeomorph

@[simp] theorem homeomorph_val (P : FiberPlace) (x : Fiber) :
    (P.homeomorph x).val = P.emb x := rfl

theorem order_of_norm {p : ℕ} [Fact p.Prime] {z : ℚ_[p]} {k : ℤ}
    (h : ‖z‖ = ‖(p : ℚ_[p]) ^ k‖) : z.valuation = k := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ha : (p : ℚ_[p]) ^ k ≠ 0 := zpow_ne_zero _ hq
  have hz : z ≠ 0 := norm_ne_zero_iff.mp (h.trans_ne (norm_ne_zero_iff.mpr ha))
  rw [Padic.norm_eq_zpow_neg_valuation hz, Padic.norm_eq_zpow_neg_valuation ha,
    Padic.valuation_zpow, Padic.valuation_p, mul_one] at h
  exact neg_inj.mp ((zpow_right_inj₀ (zero_lt_one.trans hp) hp.ne').mp h)

theorem order_of_norm_one {p : ℕ} [Fact p.Prime] {z : ℚ_[p]} (h : ‖z‖ = 1) :
    z.valuation = 0 := order_of_norm (by simpa using h)

end FiberPlace
end UnconditionalCounterexample.Hierarchy.Weighted
