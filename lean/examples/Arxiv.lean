import UnconditionalCounterexample

open UnconditionalCounterexample PaperConstruction
open scoped nonZeroDivisors

/-- The quotient isomorphism takes each polynomial class to its class in the
counterexample domain for every positive modulus. -/
example (n : ℕ) (hn : 0 < n) (f : polynomialPart) :
    polynomialPartQuotientEquiv n hn (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk (Ideal.span {(n : domain)}) (f : domain) :=
  polynomialPartQuotientEquiv_mk n hn f

/-- The integral multiples of the witness determine infinitely many additive
cosets of the polynomial part. -/
example : ¬ IsOfFinAddOrder (polynomialIndexWitness : domain ⧸ polynomialPart.toAddSubgroup) :=
  polynomialIndexWitness_infiniteOrder

/-- The factors, their irreducibility and association are taken inside the
given unital subring of the polynomial part. -/
example (T : Subring polynomialPart) (f : T) (hf : f ≠ 0) :
    let S := {s : Multiset (Associates T) | (∀ a ∈ s, Irreducible a) ∧ s.prod = Associates.mk f}
    S.Nonempty ∧ S.Finite :=
  polynomialPart_subring_factorization_classes T f hf

/-- The square has order two and the two copies of the parameter give one of
its finitely many factorizations. -/
example : let t := polynomialParameter
    PrimaryStabilization.tOrder ((t.val : RatFunc ℚ)^2) = 2 ∧
    {Associates.mk t, Associates.mk t} ∈ atomicFactorizationClasses (t^2) ∧
    (atomicFactorizationClasses (t^2)).Finite :=
  polynomialPart_parameter_sq_factorizations

section VerticalIdeals

open PaperIdealProfiles FractionalIdealProfiles
local instance : IsFractionRing domain (RatFunc ℚ) := fractionRing

/-- The two invertible ideals have opposite singleton profiles above the
selected prime, and their orders vanish at the other places. -/
example (j : ℕ) (r : ℤ)
    (hr : (r : ZMod (places.primes j).val) = PadicInt.toZMod (places.guard (places.primes j))) :
    let p := places.primes j
    let I := FractionalIdeal.spanSingleton domain⁰ (p.val : RatFunc ℚ) +
      FractionalIdeal.spanSingleton domain⁰ RatFunc.X
    let J := FractionalIdeal.spanSingleton domain⁰ (p.val : RatFunc ℚ) +
      FractionalIdeal.spanSingleton domain⁰ (RatFunc.X - (r : RatFunc ℚ))
    IsUnit I ∧ IsUnit J ∧
      HasProfile v I (fun l => if l = verticalLabel (.inl j) then 1 else 0) ∧
      HasProfile v J (fun l => if l = verticalLabel (.inr p) then 1 else 0) := by
  refine ⟨?_, parameterPair_isUnit _ r, parameterIdeal_hasProfile j, shiftedParameterIdeal_hasProfile _ r hr⟩
  simpa only [parameterPair, Int.cast_zero, sub_zero] using parameterPair_isUnit (places.primes j) 0

end VerticalIdeals
