import UnconditionalCounterexample.PaperPolynomialDivisors
import UnconditionalCounterexample.PaperAtomicity
import UnconditionalCounterexample.FiniteDivisorBounds
import Factorization.StrictHierarchy

/-!
# Hereditary finite factorization of the polynomial part

Divisibility and irreducibility are taken in the chosen subring of the
polynomial part. A multiset of associate classes records a factorization
up to permutation and association of its factors.
-/

namespace UnconditionalCounterexample.PaperConstruction

open FiniteDivisorBounds

/-- Factorizations of `x` as multisets of intrinsic atom classes. -/
abbrev atomicFactorizationClasses {R : Type*} [CommMonoid R] (x : R) :=
  Factorization.atomicFactorizationClasses x

private theorem classes_of_finite_divisors {R : Type*} [CommRing R] [IsDomain R] (x : R)
    (hx : x ≠ 0) (hf : {a : R | a ∣ x}.Finite) :
    (atomicFactorizationClasses x).Nonempty ∧ (atomicFactorizationClasses x).Finite := by
  have hatom := (hasBoundedFactorizations_of_finite_divisor_classes hx
    (finite_classes_of_finite_divisors hf)).hasAtomicFactorization
  refine ⟨(Factorization.atomicFactorizationClasses_nonempty_iff x).mpr hatom, ?_⟩
  change (Factorization.atomicFactorizationClasses x).Finite
  rw [Factorization.atomicFactorizationClasses_eq_image]
  exact (finite_atomic_factorizations hx hf).image _

/-- Actual divisors in an arbitrary subring form a finite set. -/
theorem polynomialPart_subring_finite_divisors (T : Subring polynomialPart) (x : T) (hx : x ≠ 0) :
    {a : T | a ∣ x}.Finite :=
  finite_divisors_subring T x (polynomialPart_finite_divisors x (fun h => hx (Subtype.ext h)))

/-- An intrinsic factorization exists and even the multisets of actual atom
representatives with product associated to `x` form a finite set. -/
theorem polynomialPart_subring_factorizations (T : Subring polynomialPart) (x : T) (hx : x ≠ 0) :
    Factorization.HasAtomicFactorization x ∧
    {s : Multiset T | (∀ a ∈ s, Irreducible a) ∧ Associated s.prod x}.Finite := by
  have hf := polynomialPart_subring_finite_divisors T x hx
  exact ⟨(hasBoundedFactorizations_of_finite_divisor_classes hx
    (finite_classes_of_finite_divisors hf)).hasAtomicFactorization,finite_atomic_factorizations hx hf⟩

/-- Hereditary finite factorization up to order and associates in §7. -/
theorem polynomialPart_subring_factorization_classes (T : Subring polynomialPart) (x : T) (hx : x ≠ 0) :
    (atomicFactorizationClasses x).Nonempty ∧ (atomicFactorizationClasses x).Finite :=
  classes_of_finite_divisors x hx (polynomialPart_subring_finite_divisors T x hx)

/-- Every unital subring of the polynomial part is a finite factorization domain. -/
theorem polynomialPart_subring_isFFDomain (T : Subring polynomialPart) :
    Factorization.IsFFDomain T :=
  polynomialPart_subring_factorization_classes T

/-- The original parameter as an element of the polynomial part. -/
noncomputable def polynomialParameter : polynomialPart := ⟨parameter,parameter_mem_polynomialPart⟩

theorem polynomialParameter_irreducible : Irreducible polynomialParameter := by
  refine ⟨fun h => parameter_irreducible.not_isUnit (h.map polynomialPart.subtype),?_⟩
  intro a b he
  have h : parameter = (a : domain) * (b : domain) := congrArg polynomialPart.subtype he
  exact (parameter_irreducible.isUnit_or_isUnit h).imp
    (subring_reflects_units polynomialPart a) (subring_reflects_units polynomialPart b)

/-- For `t²`, the two copies of `t` give one explicit factorization among
finitely many. The element has order two in the actual field. -/
theorem polynomialPart_parameter_sq_factorizations :
    let t := polynomialParameter
    PrimaryStabilization.tOrder ((t.val : RatFunc ℚ)^2) = 2 ∧
    {Associates.mk t, Associates.mk t} ∈ atomicFactorizationClasses (t^2) ∧
    (atomicFactorizationClasses (t^2)).Finite := by
  intro t
  have h0 := pow_ne_zero 2 polynomialParameter_irreducible.ne_zero
  refine ⟨?_,⟨?_,?_⟩,(classes_of_finite_divisors _ h0 (polynomialPart_finite_divisors _ h0)).2⟩
  · change PrimaryStabilization.tOrder ((RatFunc.X : RatFunc ℚ)^2) = 2
    rw [pow_two,PrimaryStabilization.tOrder_mul RatFunc.X_ne_zero RatFunc.X_ne_zero,PrimaryStabilization.tOrder_X]
    decide
  · intro a ha
    have he : a = Associates.mk t := by simpa using ha
    exact he ▸ Associates.irreducible_mk.mpr polynomialParameter_irreducible
  · simp [pow_two,Associates.mk_mul_mk]

end UnconditionalCounterexample.PaperConstruction
