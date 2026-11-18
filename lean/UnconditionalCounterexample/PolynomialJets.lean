import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.Div

/-!
# Exact polynomial jet quotients

Taylor translation identifies the ordinary quotient by `(X - a)^e` with the
ordinary truncated polynomial ring. For two distinct rational points, the
Chinese remainder map gives the product of their truncated rings and sends
the polynomial variable to `(a + X, b + X)`.

These algebraic identities hold in every characteristic. Hasse derivatives
record jet coefficients without division by factorials. The identities also
hold for exponent zero, when the corresponding quotient is the zero ring;
the intended vertical-jet applications use positive exponents.
-/

noncomputable section

namespace UnconditionalCounterexample.PolynomialJets

open Polynomial

variable {K : Type*} [Field K]

/-- The actual ideal defining jets of order less than `e` at `a`. -/
def pointIdeal (a : K) (e : ℕ) : Ideal K[X] :=
  Ideal.span { (X - C a) ^ e }

/-- The actual truncation ideal, with no completed power-series construction. -/
def truncIdeal (K : Type*) [Field K] (e : ℕ) : Ideal K[X] :=
  Ideal.span { X ^ e }

abbrev PointJet (a : K) (e : ℕ) := K[X] ⧸ pointIdeal a e
abbrev TruncJet (K : Type*) [Field K] (e : ℕ) := K[X] ⧸ truncIdeal K e

theorem map_pointIdeal_taylor (a : K) (e : ℕ) :
    (pointIdeal a e).map (taylorEquiv a).toRingHom = truncIdeal K e := by
  have h : (taylorEquiv a) ((X - C a) ^ e) = X ^ e := by
    change taylor a ((X - C a) ^ e) = X ^ e
    simp
  rw [pointIdeal, Ideal.map_span, Set.image_singleton]
  change Ideal.span {(taylorEquiv a) ((X - C a) ^ e)} = _
  rw [h]
  rfl

/-- Translation sends the class of `X` at `a` to the class of `a + X`. -/
def shiftEquiv (a : K) (e : ℕ) : PointJet a e ≃ₐ[K] TruncJet K e :=
  Ideal.quotientEquivAlg (pointIdeal a e) (truncIdeal K e) (taylorEquiv a)
    (map_pointIdeal_taylor a e).symm

@[simp] theorem shiftEquiv_mk (a : K) (e : ℕ) (f : K[X]) :
    shiftEquiv a e (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (taylor a f) := rfl

@[simp] theorem shiftEquiv_X (a : K) (e : ℕ) :
    shiftEquiv a e (Ideal.Quotient.mk _ X) =
      Ideal.Quotient.mk _ (C a + X) := by
  simp [add_comm]

/-- The exact ordinary polynomial jet map, formed by translation and quotient. -/
def jetMap (a : K) (e : ℕ) : K[X] →ₐ[K] TruncJet K e :=
  (Ideal.Quotient.mkₐ K (truncIdeal K e)).comp (taylorAlgHom a)

@[simp] theorem jetMap_apply (a : K) (e : ℕ) (f : K[X]) :
    jetMap a e f = Ideal.Quotient.mk _ (taylor a f) := rfl

theorem jetMap_eq_shift (a : K) (e : ℕ) (f : K[X]) :
    jetMap a e f = shiftEquiv a e (Ideal.Quotient.mk _ f) := rfl

theorem jetMap_surjective (a : K) (e : ℕ) : Function.Surjective (jetMap a e) :=
  Ideal.Quotient.mk_surjective.comp (taylorEquiv a).surjective

theorem jetMap_eq_zero_iff (a : K) (e : ℕ) (f : K[X]) :
    jetMap a e f = 0 ↔ f ∈ pointIdeal a e := by
  rw [jetMap_eq_shift, map_eq_zero_iff (shiftEquiv a e) (shiftEquiv a e).injective]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem ker_jetMap (a : K) (e : ℕ) :
    RingHom.ker (jetMap a e).toRingHom = pointIdeal a e := by
  ext f
  exact jetMap_eq_zero_iff a e f

/-- Jet vanishing is exactly vanishing of the first `e` Hasse derivatives. -/
theorem jetMap_eq_zero_iff_hasseDeriv (a : K) (e : ℕ) (f : K[X]) :
    jetMap a e f = 0 ↔ ∀ i < e, (hasseDeriv i f).eval a = 0 := by
  rw [jetMap_apply, Ideal.Quotient.eq_zero_iff_mem, truncIdeal,
    Ideal.mem_span_singleton, X_pow_dvd_iff]
  simp only [taylor_coeff]

theorem pointIdeals_isCoprime {a b : K} (hab : a ≠ b) (e d : ℕ) :
    IsCoprime (pointIdeal a e) (pointIdeal b d) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
  exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).pow

def twoPointEquiv (a b : K) (hab : a ≠ b) (e d : ℕ) :
    (K[X] ⧸ (pointIdeal a e ⊓ pointIdeal b d)) ≃+*
      TruncJet K e × TruncJet K d :=
  (Ideal.quotientInfEquivQuotientProd _ _ (pointIdeals_isCoprime hab e d)).trans
    (RingEquiv.prodCongr (shiftEquiv a e).toRingEquiv (shiftEquiv b d).toRingEquiv)

@[simp] theorem twoPointEquiv_mk (a b : K) (hab : a ≠ b) (e d : ℕ) (f : K[X]) :
    twoPointEquiv a b hab e d (Ideal.Quotient.mk _ f) =
      (jetMap a e f, jetMap b d f) := by
  apply Prod.ext <;> simp [twoPointEquiv]

def twoPointAlgEquiv (a b : K) (hab : a ≠ b) (e d : ℕ) :
    (K[X] ⧸ (pointIdeal a e ⊓ pointIdeal b d)) ≃ₐ[K]
      TruncJet K e × TruncJet K d :=
  { twoPointEquiv a b hab e d with
    commutes' r := by
      change twoPointEquiv a b hab e d (Ideal.Quotient.mk _ (C r)) = _
      rw [twoPointEquiv_mk]
      exact Prod.ext ((jetMap a e).commutes r) ((jetMap b d).commutes r) }

@[simp] theorem twoPointAlgEquiv_mk (a b : K) (hab : a ≠ b) (e d : ℕ) (f : K[X]) :
    twoPointAlgEquiv a b hab e d (Ideal.Quotient.mk _ f) =
      (jetMap a e f, jetMap b d f) := twoPointEquiv_mk a b hab e d f

theorem pointIdeals_inf_eq_span {a b : K} (hab : a ≠ b) (e d : ℕ) :
    pointIdeal a e ⊓ pointIdeal b d =
      Ideal.span { (X - C a) ^ e * (X - C b) ^ d } := by
  rw [← Ideal.mul_eq_inf_of_isCoprime (pointIdeals_isCoprime hab e d)]
  exact Ideal.span_singleton_mul_span_singleton _ _

/-- The exact two-point CRT isomorphism, allowing different positive jet orders. -/
def twoPointProductEquiv (a b : K) (hab : a ≠ b) (e d : ℕ) :
    (K[X] ⧸ Ideal.span { (X - C a) ^ e * (X - C b) ^ d }) ≃ₐ[K]
      TruncJet K e × TruncJet K d :=
  (Ideal.quotientEquivAlgOfEq K (pointIdeals_inf_eq_span hab e d).symm).trans
    (twoPointAlgEquiv a b hab e d)

@[simp] theorem twoPointProductEquiv_mk
    (a b : K) (hab : a ≠ b) (e d : ℕ) (f : K[X]) :
    twoPointProductEquiv a b hab e d (Ideal.Quotient.mk _ f) =
      (jetMap a e f, jetMap b d f) := by
  simp [twoPointProductEquiv]

/-- Simultaneous jets at two points; distinctness is needed for surjectivity. -/
def twoJetMap (a b : K) (e d : ℕ) : K[X] →ₐ[K] TruncJet K e × TruncJet K d :=
  (jetMap a e).prod (jetMap b d)

@[simp] theorem twoJetMap_apply (a b : K) (e d : ℕ) (f : K[X]) :
    twoJetMap a b e d f = (jetMap a e f, jetMap b d f) := rfl

theorem twoJetMap_surjective (a b : K) (hab : a ≠ b) (e d : ℕ) :
    Function.Surjective (twoJetMap a b e d) := by
  intro z
  obtain ⟨q, hq⟩ := (twoPointProductEquiv a b hab e d).surjective z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨f, (twoPointProductEquiv_mk a b hab e d f).symm.trans hq⟩

theorem twoJetMap_eq_zero_iff (a b : K) (hab : a ≠ b) (e d : ℕ) (f : K[X]) :
    twoJetMap a b e d f = 0 ↔
      f ∈ Ideal.span { (X - C a) ^ e * (X - C b) ^ d } := by
  rw [twoJetMap_apply, ← twoPointProductEquiv_mk a b hab e d f,
    map_eq_zero_iff (twoPointProductEquiv a b hab e d)
      (twoPointProductEquiv a b hab e d).injective]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem ker_twoJetMap (a b : K) (hab : a ≠ b) (e d : ℕ) :
    RingHom.ker (twoJetMap a b e d).toRingHom =
      Ideal.span { (X - C a) ^ e * (X - C b) ^ d } := by
  ext f
  exact twoJetMap_eq_zero_iff a b hab e d f

/-- The quotient by the `e`th power of the two-point vanishing polynomial. -/
def pairPowerEquiv (a b : K) (hab : a ≠ b) (e : ℕ) :
    (K[X] ⧸ Ideal.span { ((X - C a) * (X - C b)) ^ e }) ≃ₐ[K]
      TruncJet K e × TruncJet K e :=
  (Ideal.quotientEquivAlgOfEq K (by rw [mul_pow])).trans
    (twoPointProductEquiv a b hab e e)

@[simp] theorem pairPowerEquiv_mk
    (a b : K) (hab : a ≠ b) (e : ℕ) (f : K[X]) :
    pairPowerEquiv a b hab e (Ideal.Quotient.mk _ f) =
      (jetMap a e f, jetMap b e f) := by
  simp [pairPowerEquiv]

@[simp] theorem pairPowerEquiv_X (a b : K) (hab : a ≠ b) (e : ℕ) :
    pairPowerEquiv a b hab e (Ideal.Quotient.mk _ X) =
      (Ideal.Quotient.mk _ (C a + X), Ideal.Quotient.mk _ (C b + X)) := by
  simp [add_comm]

end UnconditionalCounterexample.PolynomialJets
