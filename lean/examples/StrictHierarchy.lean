import UnconditionalCounterexample

open UnconditionalCounterexample Factorization

open Hierarchy GuardSupport in
noncomputable example (E : EvaluationFibers) (p : PrimeIndex) (hc : IsCompact (E p)) :
    (evaluationPolynomials E ⧸ Ideal.span {(p.val : evaluationPolynomials E)}) ≃+*
      LocallyConstant (E p) (ZMod p.val) :=
  evaluationQuotientEquiv E p hc

/-- One literal inclusion induces the fraction field on every ring in the classes. -/
example {P : Subring (RatFunc ℚ) → Prop} {R : Subring (RatFunc ℚ)} (h : R ∈ StrictHierarchy.rings P) :
    IsFractionRing R (RatFunc ℚ) := StrictHierarchy.fractionRing_of_mem h

open StrictHierarchy in
example :
    (rings (fun R => IsFFDomain R) ⊂ rings (fun R => IsBFDomain R)) ∧
    (rings (fun R => IsBFDomain R) ⊂ rings (fun R => WfDvdMonoid R)) ∧
    (rings (fun R => WfDvdMonoid R) ⊂ rings (fun R => IsWeakACCP R)) ∧
    (rings (fun R => IsWeakACCP R) ⊂ rings (fun R => IsStronglyAtomicDomain R)) ∧
    (rings (fun R => IsStronglyAtomicDomain R) ⊂ rings (fun R => IsAtomicDomain R)) ∧
    (rings (fun R => IsAtomicDomain R) ⊂ rings (fun R => IsAlmostAtomicDomain R)) ∧
    (rings (fun R => IsAlmostAtomicDomain R) ⊂ rings (fun R => IsQuasiAtomicDomain R)) :=
  strictInclusions

/-- All seven forward implications apply to any integral domain. -/
example (R : Type*) [CommRing R] [IsDomain R] :
    (IsFFDomain R → IsBFDomain R) ∧ (IsBFDomain R → WfDvdMonoid R) ∧
    (WfDvdMonoid R → IsWeakACCP R) ∧ (IsWeakACCP R → IsStronglyAtomicDomain R) ∧
    (IsStronglyAtomicDomain R → IsAtomicDomain R) ∧
    (IsAtomicDomain R → IsAlmostAtomicDomain R) ∧
    (IsAlmostAtomicDomain R → IsQuasiAtomicDomain R) :=
  ⟨IsFFDomain.isBFDomain, IsBFDomain.wfDvdMonoid, isWeakACCP_of_wfDvdMonoid,
    IsWeakACCP.isStronglyAtomicDomain, IsStronglyAtomicDomain.isAtomicDomain,
    IsAtomicDomain.isAlmostAtomicDomain, IsAlmostAtomicDomain.isQuasiAtomicDomain⟩

open Hierarchy.Prescribed in
example : {s ∈ atomicFactorizationClasses (2 : binaryRing) | s.card = 2}.Infinite :=
  binary_two_factorizations

open Hierarchy.Prescribed in
example (n : ℕ) : n + 2 ∈ factorizationLengths (2 : unboundedRing) :=
  unbounded_two_lengths n

open StrictHierarchy Hierarchy in
example :
    Witness (fun R => IsFFDomain R) (fun R => IsBFDomain R) Prescribed.binaryRing ∧
    Witness (fun R => IsBFDomain R) (fun R => WfDvdMonoid R) Prescribed.unboundedRing ∧
    Witness (fun R => WfDvdMonoid R) (fun R => IsWeakACCP R) PaperConstruction.domain ∧
    Witness (fun R => IsWeakACCP R) (fun R => IsStronglyAtomicDomain R) TwoChains.domain ∧
    Witness (fun R => IsStronglyAtomicDomain R) (fun R => IsAtomicDomain R) Variations.DyadicCounterexample.ring ∧
    Witness (fun R => IsAtomicDomain R) (fun R => IsAlmostAtomicDomain R) AlmostAtomicPolynomial.fieldRing ∧
    Witness (fun R => IsAlmostAtomicDomain R) (fun R => IsQuasiAtomicDomain R) Weighted.selectedRing :=
  ⟨Prescribed.binaryWitness, Prescribed.unboundedWitness, original_witness,
    twoChain_overring.1, dyadic_overring.1, AlmostAtomicPolynomial.witness, Weighted.weightedWitness⟩

open Hierarchy.AlmostAtomicPolynomial in
example : fieldQuadratic.val = RatFunc.X * (RatFunc.X - 1) / 2 :=
  fieldQuadratic_value

open Hierarchy.AlmostAtomicPolynomial in
example : ¬ HasAtomicFactorization fieldQuadratic ∧ Irreducible (2 : fieldRing) ∧
    Irreducible fieldParameter ∧ Irreducible (fieldParameter - 1) ∧
    2 * fieldQuadratic = fieldParameter * (fieldParameter - 1) ∧
    HasAtomicFactorization (2 * fieldQuadratic) :=
  fieldQuadratic_repair

open Hierarchy.Weighted in
example : IsQuasiAtomicDomain selectedRing ∧
    ∃ b : selectedRing, b ≠ 0 ∧ b ∣ (firstPrime.val : selectedRing)^8 ∧ ringWeight b = 1 :=
  ⟨selected_quasiAtomic, exists_weightOne_divisor⟩
