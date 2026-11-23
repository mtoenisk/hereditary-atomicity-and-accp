import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.StdBasis

/-!
# The unramified integer ring at a multivariate guard

The Witt ring of a finite residue field is a discrete valuation ring with
uniformizer p. Lifts of a full set of residues span over the p-adic integers,
by completeness of the finite product of coefficient modules.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.GuardUnramified

open scoped Pointwise

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [Algebra (ZMod p) k]

/-- The scalar embedding via Witt vectors over the prime field. -/
def scalar : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (algebraMap (ZMod p) k)).comp (WittVector.equiv p).symm.toRingHom

instance : Algebra ℤ_[p] (WittVector p k) := (scalar p k).toAlgebra

omit [CharP k p] in
theorem scalar_injective : Function.Injective (scalar p k) :=
  (WittVector.map_injective _ (algebraMap (ZMod p) k).injective).comp (WittVector.equiv p).symm.injective

private theorem pow_smod {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (n : ℕ) (x y : M) :
    (x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule R M)]) ↔
    ∃ z : M, a ^ n • z = x - y := by
  simp [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]

private theorem precomplete_pi {R ι : Type*} [CommRing R] (a : R)
    [h : IsPrecomplete (Ideal.span {a}) R] : IsPrecomplete (Ideal.span {a}) (ι → R) := by
  constructor
  intro f hf
  have hi (i : ι) : ∀ {m n : ℕ}, m ≤ n → f m i ≡ f n i [SMOD (Ideal.span {a} ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    obtain ⟨z, hz⟩ := (pow_smod a m _ _).mp (hf hmn)
    exact (pow_smod a m _ _).mpr ⟨z i, congrFun hz i⟩
  choose L hL using fun i => h.prec (hi i)
  refine ⟨L, fun n => (pow_smod a n _ _).mpr ?_⟩
  choose z hz using fun i => (pow_smod a n _ _).mp (hL i n)
  exact ⟨z, funext hz⟩

/-- A set of lifts of all residue elements gives a surjective linear map
from a finite product of copies of the p-adic integers. -/
theorem span_lifts [Fintype k] (lift : k → WittVector p k) (hlift : ∀ c, (lift c).coeff 0 = c) :
    ∀ y : WittVector p k, ∃ a : k → ℤ_[p], ∑ i, a i • lift i = y := by
  classical
  let I : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p])}
  let J : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  have hm : I.map (algebraMap ℤ_[p] (WittVector p k)) = J := by simp [I, J, Ideal.map_span]
  let : IsPrecomplete I ℤ_[p] := by
    dsimp [I]
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  let : IsPrecomplete I (k → ℤ_[p]) := precomplete_pi _
  let : IsHausdorff I (WittVector p k) := IsHausdorff.of_map hm.le
  let f := Fintype.linearCombination ℤ_[p] lift
  have hs : Function.Surjective ((I • (⊤ : Submodule ℤ_[p] (WittVector p k))).mkQ ∘ₗ f) := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ y
    use Pi.single (w.coeff 0) 1
    simp only [LinearMap.comp_apply, f, Fintype.linearCombination_apply_single, one_smul,
      Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    rw [Ideal.smul_top_eq_map, hm]
    change lift (w.coeff 0) - w ∈ J
    apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
    change WittVector.constantCoeff (lift (w.coeff 0) - w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hlift _)
  exact surjective_of_mkQ_comp_surjective (I := I) (f := f) hs

/-- The Witt integer ring is finite over the p-adic integers. -/
instance [Finite k] : Module.Finite ℤ_[p] (WittVector p k) := by
  let := Fintype.ofFinite k
  let lift := WittVector.teichmuller p (R := k)
  exact Module.Finite.of_surjective (Fintype.linearCombination ℤ_[p] lift)
    (span_lifts p k lift (WittVector.teichmuller_coeff_zero p))

/-- Every lift of a residue-field generator generates the full integer ring.
This gives integral polynomial interpolation on a single guard fibre. -/
theorem adjoin_lift_eq_top [Finite k] (x : WittVector p k)
    (hx : Algebra.adjoin (ZMod p) ({x.coeff 0} : Set k) = ⊤) :
    Algebra.adjoin ℤ_[p] ({x} : Set (WittVector p k)) = ⊤ := by
  classical
  let := Fintype.ofFinite k
  let A := Algebra.adjoin ℤ_[p] ({x} : Set (WittVector p k))
  let red : WittVector p k →+* k := WittVector.constantCoeff
  have hlifts (c : k) : ∃ z ∈ A, red z = c := by
    have hc : c ∈ Algebra.adjoin (ZMod p) ({x.coeff 0} : Set k) := hx ▸ Algebra.mem_top
    induction hc using Algebra.adjoin_induction with
    | mem y hy =>
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact ⟨x, Algebra.subset_adjoin (Set.mem_singleton _), rfl⟩
    | algebraMap b =>
      refine ⟨(b.val : WittVector p k), natCast_mem A _, ?_⟩
      rw [map_natCast, ← ZMod.natCast_zmod_val b, map_natCast]
      simp
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨_, A.add_mem ha hb, map_add red a b⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨_, A.mul_mem ha hb, map_mul red a b⟩
  choose lift hA hred using hlifts
  apply top_unique
  intro y _
  obtain ⟨a, rfl⟩ := span_lifts p k lift hred y
  exact A.toSubmodule.sum_mem fun i _ => A.toSubmodule.smul_mem (a i) (hA i)

/-- The actual guard field is the fraction field of its Witt integer ring. -/
abbrev LocalField := FractionRing (WittVector p k)

instance : FaithfulSMul ℤ_[p] (WittVector p k) :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr (scalar_injective p k)

private def embedPadic : ℚ_[p] →+* LocalField p k :=
  IsFractionRing.lift (K := ℚ_[p]) (FaithfulSMul.algebraMap_injective ℤ_[p] (LocalField p k))

instance : Algebra ℚ_[p] (LocalField p k) := (embedPadic p k).toAlgebra

instance : IsScalarTower ℤ_[p] ℚ_[p] (LocalField p k) :=
  IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := ℚ_[p])
      (FaithfulSMul.algebraMap_injective ℤ_[p] (LocalField p k)) a).symm

instance [Finite k] : FiniteDimensional ℚ_[p] (LocalField p k) :=
  Module.Finite.of_isLocalization ℤ_[p] (WittVector p k) (nonZeroDivisors ℤ_[p])

open scoped WithZero

/-- Normalized discrete valuation of this local field. -/
def valuation [Finite k] : Valuation (LocalField p k) ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal (WittVector p k)).valuation _

omit [Algebra (ZMod p) k] in
theorem valuation_prime [Finite k] : valuation p k (p : LocalField p k) = WithZero.exp (-1) := by
  let P := IsDiscreteValuationRing.maximalIdeal (WittVector p k)
  rw [← map_natCast (algebraMap (WittVector p k) (LocalField p k)) p]
  change P.valuation _ _ = _
  rw [P.valuation_of_algebraMap]
  exact P.intValuation_singleton (WittVector.p_nonzero p k)
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (WittVector.irreducible p))

omit [Algebra (ZMod p) k] in
theorem integral_iff [Finite k] (y : LocalField p k) :
    valuation p k y ≤ 1 ↔ ∃ w : WittVector p k, algebraMap _ _ w = y := by
  constructor
  · exact IsDiscreteValuationRing.exists_lift_of_le_one
  · rintro ⟨w, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal _).valuation_le_one _

end UnconditionalCounterexample.Variations.GuardUnramified
