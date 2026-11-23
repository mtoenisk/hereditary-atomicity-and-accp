# Variations on the construction

This map follows §9 of the November 23, 2026 draft of *A Hereditarily Atomic Domain without ACCP*. The reviewed `main.tex` (revision `24ed23d`) has SHA-256 `a43912b88130e84f3d98e9ab846112fee3327bf3e303a4193f7d3bfd41bd49b9`. The November 17 edition has its own [map of 46 numbered statements](THEOREMS.md).

## §9.1. Krull dimension and absolute transcendence degree

| Result | Checked mathematical statement | Lean declarations |
| --- | --- | --- |
| Prescribed dimensions | For each $r\geq1$ and $1\leq d\leq r+1$ there is a named subring of $\mathbb Q(X_1,\ldots,X_r)$ with this fraction field under inclusion. It is integrally closed and hereditarily atomic, fails ACCP, has Krull dimension $d$ and has absolute transcendence degree $r$. | `UnconditionalCounterexample.Variations.PrescribedDimensions.conclusion`, `UnconditionalCounterexample.Variations.PrescribedDimensions.exists_domain` |
| Boundary dimensions | For each $r\geq1$, two subrings of $\mathbb Q(X_1,\ldots,X_r)$ have Krull dimensions $r$ and $r+1$. Both are integrally closed, have the indicated fraction field under inclusion, are hereditarily atomic and fail ACCP. | `UnconditionalCounterexample.Variations.ordinaryDimensionDomain_spec`, `UnconditionalCounterexample.Variations.upperDimensionDomain_spec` |
| Principal chains | In the lower-dimensional and boundary examples a strictly ascending chain of principal ideals starts at the cube of the first coordinate. | `UnconditionalCounterexample.Variations.lowerDimensionDomain_chain`, `UnconditionalCounterexample.Variations.ordinaryDimensionDomain_chain`, `UnconditionalCounterexample.Variations.upperDimensionDomain_chain` |
| Absolute transcendence degree | The rational function field in $r$ variables has transcendence degree $r$ over $\mathbb Q$. A subring having this fraction field has transcendence degree $r$ over $\mathbb Z$. | `UnconditionalCounterexample.Variations.rationalFunctionField_trdeg`, `UnconditionalCounterexample.Variations.subring_trdeg_of_fractionRing` |
| One-dimensional plane example | A specified integrally closed, hereditarily atomic subring of $\mathbb Q(X,Y)$ has dimension one and absolute transcendence degree two. The cube of the first coordinate starts a strictly ascending principal-ideal chain. | `UnconditionalCounterexample.Variations.PrivateGuards.PlaneClient.spec`, `UnconditionalCounterexample.Variations.PrivateGuards.PlaneClient.transcendenceDegree`, `UnconditionalCounterexample.Variations.PrivateGuards.PlaneClient.principal_chain` |

In the multivariate construction the primary tuples lie in $\mathbb Q_p$, and the ordinary guard tuples lie in finite unramified extensions of $\mathbb Q_p$. [Guard and primary evaluations](UnconditionalCounterexample/Variations/MultiDomainEvaluated.lean#L49)

Lean proves that $x_0=t^2$ starts a strict chain in $D$ with $x_n=q_{2n}x_{n+1}$ and each $q_{2n}$ a nonunit. [Square chain](UnconditionalCounterexample/Manuscript/Construction.lean#L212)

The manuscript takes $z_n=Yx_n$ and lets $P=(z_0,z_1,\ldots)$ in $D[Y]$ and $C=\mathbb Z[q_0,q_2,\ldots]$. Evaluation at $Y=0$ fixes $C$ and vanishes on $P$, so $C\cap P=(0)$. The proof of Coykendall–Gotti–Hasenauer, Theorem 6.4(6), then shows that $z_0=Yt^2$ has no factorization into atoms in $C+P$.

## §9.2. Two chains witnessing failure of weak ACCP

| Result | Checked mathematical statement | Lean declarations |
| --- | --- | --- |
| Original domain | Every unital subring of the original domain is weakly ACCP. For each nonempty finite family of nonzero elements there is a common divisor whose removal from one member gives an accessible cofactor. | `UnconditionalCounterexample.PaperConstruction.hereditarilyWeakACCP`, `UnconditionalCounterexample.PaperConstruction.weakACCP` |
| Two chains | A single subring $D$ of $\mathbb Q(t)$ has fraction field $\mathbb Q(t)$. Two strictly ascending chains of principal ideals start at $(t^2)$ and $((1-t)^2)$. These ideals are comaximal, $D$ fails weak ACCP, and every unital subring of $D$ is strongly atomic. | `UnconditionalCounterexample.TwoChains.conclusion` |
| Chain criterion | For a nonzero element, failure of accessibility for strict divisibility is equivalent to an infinite strict principal-ideal chain starting at that element. Two comaximal elements with such chains preclude weak ACCP. | `UnconditionalCounterexample.not_acc_dvdNotUnit_iff_hasStrictChainAt`, `Factorization.not_isWeakACCP_of_isCoprime_of_strictChains` |
| Conductor transfer | For a subring of the univariate construction, a sequence of listed words supplies the local tensor inclusion and a positive integer conductor. The original coefficient choices and a schedule with primaries near both $0$ and $1$ are checked clients. | `UnconditionalCounterexample.Variations.Univariate.ListedSequence.local_tensor_inclusion`, `UnconditionalCounterexample.Variations.Univariate.ListedSequence.integer_conductor`, `UnconditionalCounterexample.Variations.Univariate.original_choice`, `UnconditionalCounterexample.Variations.UnivariateClient.opposite_centres` |
| Two-centre divisor bounds | The two square generators have opposite minimum orders at the two centres, and their common divisors have finitely many associate classes. | `UnconditionalCounterexample.TwoChains.square_pair_box` |

The weak-ACCP and strong atomicity predicates use divisibility, irreducibles and units in the ring under consideration. The [downstream examples](examples/Variations.lean) apply the results through the package import.

## §9.3. A pair without a maximal common divisor

Both witnesses belong to one explicit subring of $\mathbb Q(t)$. Their centre heights are $(1,1)$, and the first two plus entries in each channel are $(2,0)$ for $x$ and $(0,4)$ for $y$. All four regular sequences have value one from index two onward.

| Result | Checked mathematical statement | Lean declarations |
| --- | --- | --- |
| Dyadic counterexample | Every unital subring of the dyadic domain is atomic. This domain fails strong atomicity and weak ACCP. | `UnconditionalCounterexample.Variations.DyadicCounterexample.counterexample` |
| Dyadic mass and stabilization | When all supplementary coordinates of a nonzero element vanish, its two weighted differences give the orders at $0$ and $1$. In each channel the plus sequence stabilizes at the order at $0$ and the minus sequence at the order at $1$. For a common divisor of the witnesses both orders vanish, so all four tails vanish. | `UnconditionalCounterexample.Variations.DyadicLedger.Calibrated.realization`, `UnconditionalCounterexample.DyadicProfiles.mass_eq_sum`, `UnconditionalCounterexample.DyadicProfiles.common_profile_heights_zero`, `UnconditionalCounterexample.DyadicProfiles.common_profile_eventually_zero` |
| Explicit pair | The named nonzero elements have the stated valuation profiles. Every common divisor $d$ admits a nonunit $u$ such that $du$ still divides both elements. | `UnconditionalCounterexample.Variations.DyadicCounterexample.x`, `UnconditionalCounterexample.Variations.DyadicCounterexample.y`, `UnconditionalCounterexample.Variations.DyadicCounterexample.pair_extension`, `UnconditionalCounterexample.Variations.DyadicLedger.Calibrated.pairElement_values` |
| Coprime splitting | For nonzero $z$ with positive orders at both centres and each $m>0$, one can write $z=uv$ and $m=ab$ with $a,b$ coprime. The factor $u$ has order zero at $1$ and $u\equiv1\pmod{aD'}$, and $v$ has order zero at $0$ and $v\equiv1\pmod{bD'}$. If $z\in T$ and $mD'\subseteq T$, the two congruences put both factors in $T$. | `UnconditionalCounterexample.Variations.DyadicCounterexample.splits`, `UnconditionalCounterexample.DyadicSplit.factors_mem_of_coprime_returns` |
| Maximal common divisors | In a weakly ACCP domain, every nonempty finite set of nonzero elements has a maximal common divisor. In particular the domain is strongly atomic. | `Factorization.IsWeakACCP.exists_maximalCommonDivisor`, `Factorization.IsWeakACCP.isStronglyAtomicDomain` |

Run `python3 check_variations.py --lean .` to resolve every declaration in the map. The optional `--source path/to/main.tex` verifies the dated draft's hash and subsection headings.
