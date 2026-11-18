import UnconditionalCounterexample.LocalizedPolynomialJets
import UnconditionalCounterexample.RationalFunctionJets
import UnconditionalCounterexample.ScalarExtension

/-!
# Actual first jets of the pole algebra

The canonical localization first jet has the ordinary rational-function value
and quotient-rule derivative as its two coordinates. The formulas work for
any surviving polynomial denominator, even if that denominator is not itself
in the selected monoid. They are unchanged by polynomial cancellation.

Under the actual coefficient-extension equivalence, a pure tensor c tensor b
has jet coordinates c times the original rational-function value and ordinary
derivative. These are algebraic maps on the pole localization inside RatFunc;
no equality with the whole rational-function field is asserted.
-/

noncomputable section
namespace UnconditionalCounterexample.PoleJets

open Polynomial LocalizedPolynomialJets TensorProduct

universe u
variable {K : Type u} [Field K]

theorem closure_eval_ne_zero (S : Set K[X]) (a : K)
    (ha : ∀ f ∈ S, f.eval a ≠ 0) :
    ∀ m : Submonoid.closure S, (m : K[X]).eval a ≠ 0 := by
  rintro ⟨m, hm⟩
  change m.eval a ≠ 0
  induction hm using Submonoid.closure_induction with
  | mem f hf => exact ha f hf
  | one => simp
  | mul f g _ _ hf hg => simpa only [eval_mul] using mul_ne_zero hf hg

def jet (S : Set K[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval a ≠ 0) :
    PoleAlgebra.generated S →+* DualNumber K := by
  letI := PoleAlgebra.isLocalization_generated S hS
  exact localizedFirstJet (Submonoid.closure S) _ a (closure_eval_ne_zero S a ha)

@[simp] theorem jet_polynomial (S : Set K[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval a ≠ 0) (P : K[X]) :
    jet S hS a ha (algebraMap K[X] (PoleAlgebra.generated S) P) = firstJet a P := by
  let := PoleAlgebra.isLocalization_generated S hS
  exact localizedFirstJet_algebraMap (Submonoid.closure S) _ a _ P

@[simp] theorem jet_scalar (S : Set K[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval a ≠ 0) (c : K) :
    jet S hS a ha (algebraMap K (PoleAlgebra.generated S) c) =
      algebraMap K (DualNumber K) c := by
  let := PoleAlgebra.isLocalization_generated S hS
  exact localizedFirstJet_scalar (Submonoid.closure S) _ a _ c

theorem fraction_relation (S : Set K[X]) (z : PoleAlgebra.generated S)
    (P Q : K[X]) (hQ : Q ≠ 0)
    (hz : (z : RatFunc K) = algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) :
    z * algebraMap K[X] (PoleAlgebra.generated S) Q =
      algebraMap K[X] (PoleAlgebra.generated S) P := by
  apply Subtype.ext
  exact (eq_div_iff (RatFunc.algebraMap_ne_zero hQ)).mp hz

theorem jet_fst_fraction (S : Set K[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval a ≠ 0) (z : PoleAlgebra.generated S)
    (P Q : K[X]) (hQ : Q.eval a ≠ 0)
    (hz : (z : RatFunc K) = algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) :
    (jet S hS a ha z).fst = P.eval a / Q.eval a := by
  have hQ0 : Q ≠ 0 := by intro h; simp [h] at hQ
  have h := congrArg (fun z => (jet S hS a ha z).fst)
    (fraction_relation S z P Q hQ0 hz)
  simp only [map_mul, jet_polynomial, TrivSqZeroExt.fst_mul, firstJet_fst] at h
  exact (eq_div_iff hQ).mpr h

theorem jet_snd_fraction (S : Set K[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval a ≠ 0) (z : PoleAlgebra.generated S)
    (P Q : K[X]) (hQ : Q.eval a ≠ 0)
    (hz : (z : RatFunc K) = algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) :
    (jet S hS a ha z).snd =
      (P.derivative.eval a * Q.eval a - P.eval a * Q.derivative.eval a) /
        Q.eval a ^ 2 := by
  have hQ0 : Q ≠ 0 := by intro h; simp [h] at hQ
  have h := congrArg (fun z => (jet S hS a ha z).snd)
    (fraction_relation S z P Q hQ0 hz)
  simp only [map_mul, jet_polynomial, DualNumber.snd_mul, firstJet_fst, firstJet_snd] at h
  rw [jet_fst_fraction S hS a ha z P Q hQ hz] at h
  field_simp at h ⊢
  linear_combination h

theorem jet_fst (S : Set K[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval a ≠ 0) (z : PoleAlgebra.generated S) :
    (jet S hS a ha z).fst = RatFunc.eval (algebraMap K K) a z := by
  obtain ⟨P, Q, hQ, hz⟩ := (PoleAlgebra.mem_generated_iff S hS z).mp z.property
  have hQa := closure_eval_ne_zero S a ha ⟨Q, hQ⟩
  rw [jet_fst_fraction S hS a ha z P Q hQa hz, hz]
  simpa only [Algebra.algebraMap_self, eval₂_id] using
    (RationalFunctionJets.eval_fraction P Q a (by simpa using hQa)).symm

theorem jet_snd (S : Set K[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval a ≠ 0) (z : PoleAlgebra.generated S) :
    (jet S hS a ha z).snd = CurveRecovery.geometricDerivativeAt K (z : RatFunc K) a := by
  obtain ⟨P, Q, hQ, hz⟩ := (PoleAlgebra.mem_generated_iff S hS z).mp z.property
  have hQa := closure_eval_ne_zero S a ha ⟨Q, hQ⟩
  rw [jet_snd_fraction S hS a ha z P Q hQa hz, hz]
  simpa only [Algebra.algebraMap_self, eval₂_id] using
    (RationalFunctionJets.derivative_fraction P Q a (by simpa using hQa)).symm

section ScalarExtension

variable {k : Type u} [Field k] [Algebra k K]

theorem extended_retained (S : Set k[X]) (a : K)
    (ha : ∀ f ∈ S, f.eval₂ (algebraMap k K) a ≠ 0) :
    ∀ f ∈ ScalarExtension.extendedSet k K S, f.eval a ≠ 0 := by
  rintro f ⟨g, hg, rfl⟩
  simpa only [eval_map] using ha g hg

def extendedJet (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval₂ (algebraMap k K) a ≠ 0) :
    PoleAlgebra.generated (ScalarExtension.extendedSet k K S) →+* DualNumber K :=
  jet _ (ScalarExtension.extendedSet_nonzero k K S hS) a (extended_retained S a ha)

@[simp] theorem extendedJet_scalar (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval₂ (algebraMap k K) a ≠ 0) (c : K) :
    extendedJet S hS a ha
      (algebraMap K (PoleAlgebra.generated (ScalarExtension.extendedSet k K S)) c) =
        algebraMap K (DualNumber K) c := jet_scalar _ _ _ _ _

theorem extendedJet_one_tmul_fst (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval₂ (algebraMap k K) a ≠ 0)
    (b : PoleAlgebra.generated S) :
    (extendedJet S hS a ha (ScalarExtension.tensorEquiv k K S hS (1 ⊗ₜ[k] b))).fst =
      RatFunc.eval (algebraMap k K) a (b : RatFunc k) := by
  have hden := CurveRecovery.geometric_denom_ne_zero S K hS b a ha
  have h := jet_fst_fraction (ScalarExtension.extendedSet k K S)
    (ScalarExtension.extendedSet_nonzero k K S hS) a (extended_retained S a ha)
    (ScalarExtension.tensorEquiv k K S hS (1 ⊗ₜ[k] b))
    ((b : RatFunc k).num.map (algebraMap k K))
    ((b : RatFunc k).denom.map (algebraMap k K)) (by simpa only [eval_map] using hden)
    (ScalarExtension.embedding_one_tmul_fraction k K S hS b _ _
      (b : RatFunc k).denom_ne_zero (RatFunc.num_div_denom (b : RatFunc k)).symm)
  simpa only [extendedJet, eval_map, RatFunc.eval] using h

theorem extendedJet_one_tmul_snd (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval₂ (algebraMap k K) a ≠ 0)
    (b : PoleAlgebra.generated S) :
    (extendedJet S hS a ha (ScalarExtension.tensorEquiv k K S hS (1 ⊗ₜ[k] b))).snd =
      CurveRecovery.geometricDerivativeAt K (b : RatFunc k) a := by
  have hden := CurveRecovery.geometric_denom_ne_zero S K hS b a ha
  have h := jet_snd_fraction (ScalarExtension.extendedSet k K S)
    (ScalarExtension.extendedSet_nonzero k K S hS) a (extended_retained S a ha)
    (ScalarExtension.tensorEquiv k K S hS (1 ⊗ₜ[k] b))
    ((b : RatFunc k).num.map (algebraMap k K))
    ((b : RatFunc k).denom.map (algebraMap k K)) (by simpa only [eval_map] using hden)
    (ScalarExtension.embedding_one_tmul_fraction k K S hS b _ _
      (b : RatFunc k).denom_ne_zero (RatFunc.num_div_denom (b : RatFunc k)).symm)
  simpa only [extendedJet, derivative_map, eval_map, CurveRecovery.geometricDerivativeAt] using h

theorem extendedJet_tmul (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval₂ (algebraMap k K) a ≠ 0)
    (c : K) (b : PoleAlgebra.generated S) :
    extendedJet S hS a ha (ScalarExtension.tensorEquiv k K S hS (c ⊗ₜ[k] b)) =
      algebraMap K (DualNumber K) c *
        extendedJet S hS a ha (ScalarExtension.tensorEquiv k K S hS (1 ⊗ₜ[k] b)) := by
  have heq : c ⊗ₜ[k] b =
      algebraMap K (K ⊗[k] PoleAlgebra.generated S) c * (1 ⊗ₜ[k] b) := by
    change c ⊗ₜ[k] b = (c ⊗ₜ[k] (1 : PoleAlgebra.generated S)) * (1 ⊗ₜ[k] b)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [heq, map_mul, AlgEquiv.commutes, map_mul, extendedJet_scalar]

theorem extendedJet_tmul_fst (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval₂ (algebraMap k K) a ≠ 0)
    (c : K) (b : PoleAlgebra.generated S) :
    (extendedJet S hS a ha (ScalarExtension.tensorEquiv k K S hS (c ⊗ₜ[k] b))).fst =
      c * RatFunc.eval (algebraMap k K) a (b : RatFunc k) := by
  rw [extendedJet_tmul, TrivSqZeroExt.fst_mul, extendedJet_one_tmul_fst]
  rfl

theorem extendedJet_tmul_snd (S : Set k[X]) (hS : ∀ f ∈ S, f ≠ 0)
    (a : K) (ha : ∀ f ∈ S, f.eval₂ (algebraMap k K) a ≠ 0)
    (c : K) (b : PoleAlgebra.generated S) :
    (extendedJet S hS a ha (ScalarExtension.tensorEquiv k K S hS (c ⊗ₜ[k] b))).snd =
      c * CurveRecovery.geometricDerivativeAt K (b : RatFunc k) a := by
  rw [extendedJet_tmul, DualNumber.snd_mul, extendedJet_one_tmul_snd]
  change c * _ + 0 * _ = c * _
  simp only [zero_mul, add_zero]

end ScalarExtension

end UnconditionalCounterexample.PoleJets
