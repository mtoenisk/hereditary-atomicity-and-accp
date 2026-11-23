import Factorization.Hierarchy
import Mathlib.Order.Preorder.Finite

/-! # Maximal common divisors of finite families -/

namespace Factorization

variable {R : Type*}

/-- A common divisor is maximal if multiplying it by a further common factor
of the residual family always multiplies it by a unit. -/
def IsMaximalCommonDivisor [Monoid R] (s : Finset R) (d : R) : Prop :=
  (∀ x ∈ s, d ∣ x) ∧ ∀ u : R, (∀ x ∈ s, d * u ∣ x) → IsUnit u

variable [CommMonoidWithZero R] [IsCancelMulZero R]

/-- For a pair this tests relative primality of the two actual residual elements. -/
theorem isMaximalCommonDivisor_pair_iff [DecidableEq R] {d a b : R} (hd : d ≠ 0) :
    IsMaximalCommonDivisor {d * a, d * b} d ↔ IsRelPrime a b := by
  constructor
  · intro h u hau hbu
    apply h.2 u
    simpa using And.intro (mul_dvd_mul_left d hau) (mul_dvd_mul_left d hbu)
  · intro h
    refine ⟨?_, ?_⟩
    · simp
    · intro u hu
      have hab : d * u ∣ d * a ∧ d * u ∣ d * b := by simpa using hu
      exact h ((mul_dvd_mul_iff_left hd).mp hab.1) ((mul_dvd_mul_iff_left hd).mp hab.2)

/-- One accessible residual suffices to finish a common divisor to a maximal
one. The other entries need no chain condition. -/
theorem exists_maximalCommonDivisor_of_acc_residual {s : Finset R} {x d q : R}
    (hx : x ∈ s) (hx0 : x ≠ 0) (hd : ∀ y ∈ s, d ∣ y)
    (heq : x = d * q) (hq : Acc DvdNotUnit q) :
    ∃ m : R, d ∣ m ∧ IsMaximalCommonDivisor s m := by
  classical
  induction hq generalizing d with
  | intro q _ ih =>
    by_cases hm : IsMaximalCommonDivisor s d
    · exact ⟨d, dvd_rfl, hm⟩
    · have hf : ¬ ∀ u : R, (∀ y ∈ s, d * u ∣ y) → IsUnit u :=
        fun h => hm ⟨hd, h⟩
      push Not at hf
      obtain ⟨u, hu, hnu⟩ := hf
      obtain ⟨z, hz⟩ := hu x hx
      have hd0 : d ≠ 0 := left_ne_zero_of_mul (heq ▸ hx0)
      have hz0 : z ≠ 0 := right_ne_zero_of_mul (hz ▸ hx0)
      have hqz : q = u * z := mul_left_cancel₀ hd0 (by
        calc d * q = x := heq.symm
             _ = d * (u * z) := hz.trans (mul_assoc _ _ _))
      obtain ⟨m, hdm, hm⟩ := ih z ⟨hz0, u, hnu, hqz.trans (mul_comm _ _)⟩ hu hz
      exact ⟨m, (dvd_mul_right d u).trans hdm, hm⟩

/-- A finite set of common-divisor classes has a maximal representative,
provided that at least one of the entries is nonzero. -/
theorem exists_maximalCommonDivisor_of_finite_classes (s : Finset R)
    (hne : ∃ x ∈ s, x ≠ 0)
    (hfin : (Associates.mk '' {d : R | ∀ x ∈ s, d ∣ x}).Finite) :
    ∃ d : R, IsMaximalCommonDivisor s d := by
  let C : Set R := {d | ∀ x ∈ s, d ∣ x}
  have hone : (1 : R) ∈ C := fun x _ => one_dvd x
  obtain ⟨d, hd, hmax⟩ :=
    Set.Finite.exists_maximalFor' Associates.mk C hfin ⟨1, hone⟩
  obtain ⟨x, hx, hx0⟩ := hne
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hx0 (zero_dvd_iff.mp (hd x hx))
  refine ⟨d, hd, fun u hu => (mul_dvd_left_iff_isUnit hd0).mp ?_⟩
  exact Associates.mk_le_mk_iff_dvd.mp
    (hmax hu (Associates.mk_le_mk_of_dvd (dvd_mul_right d u)))

/-- For a nonzero divisor, maximality is equivalent to association with
every common divisor above it in the divisibility order. -/
theorem isMaximalCommonDivisor_iff_associated {s : Finset R} {d : R} (hd : d ≠ 0) :
    IsMaximalCommonDivisor s d ↔
      (∀ x ∈ s, d ∣ x) ∧ ∀ m : R, d ∣ m → (∀ x ∈ s, m ∣ x) → Associated d m := by
  constructor
  · rintro ⟨hdiv, hmax⟩
    refine ⟨hdiv, ?_⟩
    rintro _ ⟨u, rfl⟩ hu
    exact (associated_mul_unit_left d u (hmax u hu)).symm
  · rintro ⟨hdiv, hmax⟩
    refine ⟨hdiv, fun u hu => (mul_dvd_left_iff_isUnit hd).mp ?_⟩
    exact (hmax (d * u) (dvd_mul_right d u) hu).symm.dvd

/-- Multiplying every entry by a nonzero factor lifts a maximal common divisor
of the residual family to one of the original family. -/
theorem IsMaximalCommonDivisor.mul_left [DecidableEq R] {s : Finset R} {d c : R}
    (hm : IsMaximalCommonDivisor s d) (hc : c ≠ 0) :
    IsMaximalCommonDivisor (s.image (c * ·)) (c * d) := by
  constructor
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact mul_dvd_mul_left c (hm.1 x hx)
  · intro u hu
    apply hm.2 u
    intro x hx
    apply (mul_dvd_mul_iff_left hc).mp
    simpa only [mul_assoc] using hu (c * x) (Finset.mem_image_of_mem _ hx)

/-- Pairwise specialization of lifting a maximal common divisor. -/
theorem IsMaximalCommonDivisor.mul_left_pair [DecidableEq R] {a b c d : R}
    (hm : IsMaximalCommonDivisor {a, b} d) (hc : c ≠ 0) :
    IsMaximalCommonDivisor {c * a, c * b} (c * d) := by
  simpa using hm.mul_left hc

end Factorization
