# Factorization in almost Dedekind overrings of Int(ℤ)

This is a supplementary theorem of the Lean library. The HA manuscript's original domain witnesses the strict inclusion of ACCP in weak ACCP. The library places it in a chain of seven strict inclusions, each with a named witness.

The ambient rings are unital subrings of $\mathbb Q(t)$ containing the integer-valued polynomials. At every maximal ideal their localization is a discrete valuation ring. Inclusion gives each of these rings fraction field $\mathbb Q(t)$. Factorization, divisibility and units are taken in each subring. [Integer-valued polynomials](UnconditionalCounterexample/Hierarchy/IntegerValued.lean) · [Class and fraction field](UnconditionalCounterexample/Hierarchy/StrictClasses.lean)

For the ring of rational polynomials integral on the prescribed fibers, reduction modulo $p$ gives the ring of locally constant functions from the compact fiber at $p$ to $\mathbb F_p$. [Residue-function quotient](UnconditionalCounterexample/Hierarchy/EvaluationQuotient.lean)

For arbitrary integral domains, Lean proves every implication in the chain

$$
\mathrm{FFD}\Rightarrow\mathrm{BFD}\Rightarrow\mathrm{ACCP}\Rightarrow
\text{weak ACCP}\Rightarrow\text{strongly atomic}\Rightarrow\text{atomic}
\Rightarrow\text{almost atomic}\Rightarrow\text{quasi-atomic}.
$$

FFD counts unordered factorizations into associate classes of irreducibles. The almost atomic multiplier must itself be a product of atoms. For quasi-atomicity an arbitrary nonzero multiplier is allowed. [Factorization predicates](Factorization/StrictHierarchy.lean) · [Public client for all seven implications](examples/StrictHierarchy.lean)

## Verified strict inclusions

With `import UnconditionalCounterexample`, the theorem `UnconditionalCounterexample.StrictHierarchy.strictInclusions` gives all seven proper inclusions in the displayed order. [Combined theorem](UnconditionalCounterexample/Hierarchy/StrictImplications.lean) · [Public client](examples/StrictHierarchy.lean)

| Proper subclass | Witness and checked conclusions |
| --- | --- |
| FFD inside BFD | In the binary-row ring, $2$ has infinitely many distinct factorizations of length two up to permutation and associates. Every nonzero element has bounded factorization lengths. `UnconditionalCounterexample.StrictHierarchy.ffd_ssubset_bfd`. [Binary-row witness](UnconditionalCounterexample/Hierarchy/PrescribedWitnesses.lean) |
| BFD inside ACCP | The growing-row ring satisfies ACCP. For each natural number $n$, the element $2$ has an atom factorization of length $n+2$ in this ring. `UnconditionalCounterexample.StrictHierarchy.bfd_ssubset_accp`. [Growing-row witness](UnconditionalCounterexample/Hierarchy/PrescribedWitnesses.lean) |
| ACCP inside weak ACCP | The original domain contains $\operatorname{Int}(\mathbb Z)$, has DVR localizations at every maximal ideal, and satisfies weak ACCP. A strict chain of principal ideals starts at $(t^2)$. `UnconditionalCounterexample.StrictHierarchy.original_witness` and `UnconditionalCounterexample.StrictHierarchy.accp_ssubset_weakACCP` identify the ring and prove the proper inclusion. [Witness and strict inclusion](UnconditionalCounterexample/Manuscript/StrictHierarchy.lean) · [Square chain](UnconditionalCounterexample/PaperSquareChainActual.lean) |
| Weak ACCP inside strong atomicity | The two-chain ring is strongly atomic. The comaximal squares $t^2,(1-t)^2$ each start a strictly ascending chain of principal ideals, so the ring fails weak ACCP. `UnconditionalCounterexample.StrictHierarchy.weakACCP_ssubset_stronglyAtomic`. [Overring and square chains](UnconditionalCounterexample/Hierarchy/UnivariateOverrings.lean) |
| Strong atomicity inside atomicity | The dyadic ring is atomic. Every common divisor of the named nonzero pair $x,y$ extends by a nonunit while still dividing both. `UnconditionalCounterexample.StrictHierarchy.stronglyAtomic_ssubset_atomic`. [Overring and named pair](UnconditionalCounterexample/Hierarchy/UnivariateOverrings.lean) |
| Atomicity inside almost atomicity | The two-point polynomial evaluation ring is almost atomic. Its element $t(t-1)/2$ has no atom factorization, and doubling it gives the product of the two atoms $t$ and $t-1$. `UnconditionalCounterexample.Hierarchy.AlmostAtomicPolynomial.strict_inclusion`. [Witness and quadratic element](UnconditionalCounterexample/Hierarchy/AlmostAtomicPolynomial.lean) |
| Almost atomicity inside quasi-atomicity | In the ring with marked fibers, every nonzero element divides an atomic product. An element $b$ of weight one divides the eighth power of the first selected rational prime. Atomic products have weight zero, so $b$ has no atomic multiplier. `UnconditionalCounterexample.StrictHierarchy.almostAtomic_ssubset_quasiAtomic`. [Quasi-atomicity and the weight obstruction](UnconditionalCounterexample/Hierarchy/WeightedSeparation.lean) |
