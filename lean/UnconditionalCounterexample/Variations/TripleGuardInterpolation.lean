import UnconditionalCounterexample.Variations.GuardInterpolation
import UnconditionalCounterexample.GuardSupport

/-! # Integral interpolation at a Witt guard and two rational branches -/

noncomputable section
namespace UnconditionalCounterexample.Variations.GuardUnramified
open Polynomial

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [Algebra (ZMod p) k]

/-- The two rational residues must differ. Their difference is then invertible
in the p-adic integers. Correct the second branch by a polynomial vanishing
both at the Witt guard and at the first rational branch. -/
theorem guard_two_primary_values (x : WittVector p k)
    (hgen : Algebra.adjoin ℤ_[p] ({x} : Set (WittVector p k)) = ⊤)
    (hout : x.coeff 0 ∉ Set.range (algebraMap (ZMod p) k))
    (a b : ℤ_[p]) (hab : PadicInt.toZMod a ≠ PadicInt.toZMod b)
    (u : WittVector p k) (v w : ℤ_[p]) :
    ∃ P : Polynomial ℤ_[p], aeval x P = u ∧ P.eval a = v ∧ P.eval b = w := by
  obtain ⟨P,hx,ha⟩ := guard_primary_values p k x hgen hout a u v
  have hunit : IsUnit (b - a) := (GuardSupport.padicInt_isUnit_iff_toZMod_ne_zero _).mpr
    (by rw [map_sub,sub_ne_zero]; exact hab.symm)
  obtain ⟨d,hd⟩ := hunit
  obtain ⟨Q,h0,hb⟩ := guard_primary_values p k x hgen hout b 0 ((d⁻¹ : ℤ_[p]ˣ) * (w - P.eval b))
  refine ⟨P + (X - C a) * Q,by simp [hx,h0],by simp [ha],?_⟩
  simp only [eval_add,eval_mul,eval_sub,eval_X,eval_C,hb,← hd,← mul_assoc,Units.mul_inv,one_mul]
  abel

end UnconditionalCounterexample.Variations.GuardUnramified
