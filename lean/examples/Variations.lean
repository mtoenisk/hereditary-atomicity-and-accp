import UnconditionalCounterexample

open UnconditionalCounterexample

/-- The original counterexample is weakly ACCP in each unital subring.
The divisor and its cofactor are elements of that subring. -/
example (T : Subring PaperConstruction.domain) (s : Finset T) (hs : s.Nonempty)
    (hn : ∀ x ∈ s, x ≠ 0) :
    ∃ d : T, (∀ x ∈ s, d ∣ x) ∧ ∃ x ∈ s, ∃ q : T, x = d * q ∧ Acc DvdNotUnit q :=
  (PaperConstruction.hereditarilyWeakACCP T).2 s hs hn

/-- The two square chains and all intrinsic subring conclusions use the same
explicit domain and rational-function parameter. -/
example : (TwoChains.parameter : RatFunc ℚ) = RatFunc.X ∧
    IsFractionRing TwoChains.domain (RatFunc ℚ) ∧
    HasStrictChainAt (TwoChains.parameter^2) ∧ HasStrictChainAt ((1-TwoChains.parameter)^2) ∧
    IsCoprime (TwoChains.parameter^2) ((1-TwoChains.parameter)^2) ∧
    ¬ Factorization.IsWeakACCP TwoChains.domain ∧
    ∀ T : Subring TwoChains.domain, Factorization.IsStronglyAtomicDomain T :=
  TwoChains.conclusion

/-- Listed words in a fixed subring of the alternating construction give a
single integer conductor in that ring. -/
example (T : Subring (Variations.Univariate.domain Variations.UnivariateClient.alternating.requirements))
    (L : Variations.Univariate.ListedSequence Variations.UnivariateClient.alternating.requirements T) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : Variations.Univariate.domain Variations.UnivariateClient.alternating.requirements,
      (n : Variations.Univariate.domain Variations.UnivariateClient.alternating.requirements) * z ∈ T := by
  obtain ⟨⟨n, hn, hnt⟩, h⟩ := L.integer_conductor
  exact ⟨n, hn, h n hnt⟩

namespace DyadicExample
open Variations.DyadicCounterexample

/-- The same ring carries hereditary atomicity and a named nonzero pair with
no maximal common divisor. All divisibility is internal to that ring. -/
example : (∀ T : Subring ring, ∀ z : T, z ≠ 0 →
    ∃ s : Multiset T, (∀ p ∈ s, Irreducible p) ∧ Associated s.prod z) ∧ x ≠ 0 ∧ y ≠ 0 ∧
    (∀ d : ring, d ∣ x → d ∣ y → ∃ u : ring, ¬ IsUnit u ∧ d*u ∣ x ∧ d*u ∣ y) ∧
    ¬ Factorization.IsStronglyAtomicDomain ring ∧ ¬ Factorization.IsWeakACCP ring := counterexample

/-- Each early plus entry and the common tail are computed on the actual
elements selected by the construction, in both channels. -/
example (k : Bool) :
    let v := Variations.DyadicLedger.Calibrated.valuation Variations.DyadicLedger.ScheduledSplit.policy
    (DiscreteOrders.natOrder (v (.plus k 0)) x.val = 2 ∧ DiscreteOrders.natOrder (v (.plus k 1)) x.val = 0) ∧
    (DiscreteOrders.natOrder (v (.plus k 0)) y.val = 0 ∧ DiscreteOrders.natOrder (v (.plus k 1)) y.val = 4) ∧
    ∀ n ≥ 2, DiscreteOrders.natOrder (v (.plus k n)) x.val = 1 ∧ DiscreteOrders.natOrder (v (.minus k n)) y.val = 1 := by
  let a : Variations.DyadicLedger.Calibrated.Policy := Variations.DyadicLedger.ScheduledSplit.policy
  have hx := Variations.DyadicLedger.Calibrated.pairElement_values a false
  have hy := Variations.DyadicLedger.Calibrated.pairElement_values a true
  refine ⟨⟨hx (.plus k 0),hx (.plus k 1)⟩,⟨hy (.plus k 0),hy (.plus k 1)⟩,?_⟩
  intro n hn
  simpa [a,x,y,DyadicProfiles.Profile.values,DyadicProfiles.witness,show n ≠ 0 by omega,
    show n ≠ 1 by omega,show ¬ n ≤ 1 by omega] using And.intro (hx (.plus k n)) (hy (.minus k n))

end DyadicExample

open UnconditionalCounterexample UnconditionalCounterexample.Variations

/-- In each positive number of variables the two boundary dimensions occur.
The chain begins at the cube of the first coordinate in the displayed domain. -/
example (n : ℕ) (d : ℕ) (hd : d = n+1 ∨ d = n+2) :
    ∃ D : Subring (FractionRing (MvPolynomial (Fin (n+1)) ℚ)),
      IsFractionRing D (FractionRing (MvPolynomial (Fin (n+1)) ℚ)) ∧
      IsIntegrallyClosed D ∧ ringKrullDim D = d ∧ Algebra.trdeg ℤ D = n+1 ∧
      (∀ T : Subring D, ∀ x : T, x ≠ 0 → ∃ factors : Multiset T,
        (∀ p ∈ factors, Irreducible p) ∧ Associated factors.prod x) ∧
      ∃ t : D, (t : FunctionField (n+1)) = MultiDomain.coordinate 0 ∧
        ∃ x : ℕ → D, x 0 = t^3 ∧ (∀ i, x i ≠ 0) ∧
          StrictMono (fun i => Ideal.span ({x i} : Set D)) := by
  obtain ⟨D, hD, ht⟩ : ∃ D : Subring (FunctionField (n+1)),
      PrescribedDimension D d ∧ (∃ t : D, (t : FunctionField (n+1)) = MultiDomain.coordinate 0 ∧
        HasStrictChainAt (t^3)) := by
    rcases hd with rfl | rfl
    · exact ⟨ordinaryDimensionDomain n, ordinaryDimensionDomain_spec n, ordinaryDimensionDomain_chain n⟩
    · exact ⟨upperDimensionDomain n, upperDimensionDomain_spec n, upperDimensionDomain_chain n⟩
  obtain ⟨hf, hn, hdim, hHA, _⟩ := hD
  let := hf
  exact ⟨D, hf, hn, hdim, by simpa using subring_trdeg_of_fractionRing (n+1) D, hHA, ht⟩

open UnconditionalCounterexample UnconditionalCounterexample.Variations

/-- The prescribed domain uses the inclusion into the indicated fraction field.
The factors and their irreducibility are intrinsic to the chosen unital subring. -/
example (r d : ℕ) (hr : 1 ≤ r) (hd : 1 ≤ d) (hbound : d ≤ r+1) :
    let D := PrescribedDimensions.domain r d hr hd hbound
    IsFractionRing D (FractionRing (MvPolynomial (Fin r) ℚ)) ∧ IsIntegrallyClosed D ∧
      ringKrullDim D = d ∧ Algebra.trdeg ℤ D = r ∧
      (∀ T : Subring D, ∀ x : T, x ≠ 0 → ∃ factors : Multiset T,
        (∀ p ∈ factors, Irreducible p) ∧ Associated factors.prod x) ∧
      ∃ I : ℕ → Ideal D, (∀ n, (I n).IsPrincipal) ∧ StrictMono I := by
  obtain ⟨⟨hf, hn, hdim, hHA, hchain⟩, hdeg⟩ := PrescribedDimensions.conclusion r d hr hd hbound
  exact ⟨hf, hn, hdim, hdeg, hHA, Factorization.not_wfDvdMonoid_iff_exists_strictMono_principalIdealChain.mp hchain⟩
