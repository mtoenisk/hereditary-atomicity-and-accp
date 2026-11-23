import UnconditionalCounterexample.Hierarchy.WeightedPlace
import UnconditionalCounterexample.Hierarchy.WeightedPrimeStage
import UnconditionalCounterexample.Hierarchy.PrescribedFiber

/-! # Fresh weighted fibers preserving all previously selected polynomials -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open Polynomial GuardSupport

namespace CorrectionBalls

private theorem exists_embedding {f : ℚ[X]} {frozen : Finset ℚ[X]} {k : ℤ}
    (s : CorrectionBalls f frozen k) :
    ∃ e : Fiber → ℤ_[s.prime.val], Continuous e ∧ Function.Injective e ∧
      ∀ x, e x ∈ Metric.ball (s.center (x 0)) (s.radius (x 0)) ∧ Transcendental ℚ (e x).val := by
  choose u hu hi hab using fun b ↦ Prescribed.exists_cantor_in_ball s.prime.val
    (s.center b) (s.radius b) (s.radius_pos b)
  let e (x : Fiber) := if x 0 = true then u true x else u false x
  have hsel (x : Fiber) : e x = u (x 0) x := by cases h : x 0 <;> simp [e, h]
  have hc : IsClopen {x : Fiber | x 0 = true} :=
    (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply 0)
  refine ⟨e, continuous_if (fun x hx ↦ False.elim (by simp [hc.frontier_eq] at hx))
    (hu true).continuousOn (hu false).continuousOn, ?_, fun x ↦ by rw [hsel]; exact hab (x 0) x⟩
  intro x y h
  rw [hsel, hsel] at h
  have hhead : x 0 = y 0 := by
    by_contra hn
    have hx := (hab (x 0) x).1
    have hy := (hab (y 0) y).1
    rw [← h] at hy
    rcases hx0 : x 0 <;> rcases hy0 : y 0 <;> simp_all [Set.disjoint_left.mp s.disjoint]
  rw [hhead] at h
  exact hi _ h

/-- Choose a transcendental compact Cantor fiber in the two certified balls. -/
def place {f : ℚ[X]} {frozen : Finset ℚ[X]} {k : ℤ} (s : CorrectionBalls f frozen k) : FiberPlace where
  prime := s.prime
  emb := s.exists_embedding.choose
  continuous := s.exists_embedding.choose_spec.1
  injective := s.exists_embedding.choose_spec.2.1
  transcendental := fun x ↦ (s.exists_embedding.choose_spec.2.2 x).2

theorem order {f : ℚ[X]} {frozen : Finset ℚ[X]} {k : ℤ} (s : CorrectionBalls f frozen k) (x : Fiber) :
    s.place.polynomialOrder f x = correctionOrder k (x 0) :=
  (s.on_ball _ _ (s.exists_embedding.choose_spec.2.2 x).1).2.1

theorem frozen_order {f g : ℚ[X]} {frozen : Finset ℚ[X]} {k : ℤ} (s : CorrectionBalls f frozen k)
    (hg : g ∈ frozen) (x : Fiber) : s.place.polynomialOrder g x = 0 :=
  FiberPlace.order_of_norm_one ((s.on_ball _ _ (s.exists_embedding.choose_spec.2.2 x).1).2.2 g hg)

end CorrectionBalls

theorem exists_correcting_place (f : ℚ[X]) (hirr : Irreducible f) (frozen : Finset ℚ[X])
    (hn : ∀ g ∈ frozen, g ≠ 0) (hcop : ∀ g ∈ frozen, IsCoprime f g) (k : ℤ) (cutoff : ℕ) :
    ∃ P : FiberPlace, cutoff < P.prime.val ∧
      (∀ b, P.polynomialOrder f (mark b) = correctionOrder k b) ∧
      ∀ g ∈ frozen, ∀ x, P.polynomialOrder g x = 0 := by
  obtain ⟨s, hs⟩ := exists_correctionBalls f hirr frozen hn hcop k cutoff
  exact ⟨s.place, hs, fun b ↦ s.order (mark b), fun _ hg ↦ s.frozen_order hg⟩

theorem exists_safe_place (frozen : Finset ℚ[X]) (h : ∀ g ∈ frozen, g ≠ 0) (N : ℕ) :
    ∃ E : FiberPlace, N < E.prime.val ∧ ∀ g ∈ frozen, ∀ x, E.polynomialOrder g x = 0 := by
  obtain ⟨s, hs⟩ := exists_unitBalls 1 one_ne_zero frozen h N
  exact ⟨s.place, hs, fun _ hg ↦ s.frozen_order hg⟩

end UnconditionalCounterexample.Hierarchy.Weighted
