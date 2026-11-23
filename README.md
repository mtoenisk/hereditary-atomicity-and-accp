# Hereditary Atomicity and ACCP

If every unital subring of an integral domain is atomic, must the domain satisfy the ascending chain condition on principal ideals (ACCP)? These two manuscripts give a positive answer for semilocal domains and an unconditional counterexample in general.

The [Lean theorem map](lean/THEOREMS.md) links all 46 numbered results in the two manuscripts to their formal proofs. The [revised manuscript map](lean/ARXIV_THEOREMS.md) also records the correspondence with the later exposition of the counterexample. The [package README](lean/README.md) explains how to check the proofs and import the libraries.

A domain is **atomic** if every nonzero nonunit is a finite product of irreducibles. It is **hereditarily atomic** if every unital subring is atomic. Coykendall, Gotti, and Hasenauer conjectured that in a hereditarily atomic domain every unital subring satisfies ACCP. [*Hereditary atomicity in integral domains*, Conjecture 6.1](https://arxiv.org/abs/2112.00264)

## A hereditarily atomic domain without ACCP

The paper constructs an almost Dedekind domain $D$ with fraction field $\mathbb{Q}(t)$. Every unital subring of $D$ is atomic. Yet $t$ is irreducible in $D$, and the principal ideal $(t^2)$ starts an infinite strictly ascending chain. The successive ratios in this chain are multiplicatively independent modulo $\mathbb{Q}^{\times}$.

The same example admits an exact description of where ACCP fails. The unital subrings of $D$ that fail ACCP are precisely $\mathbb{Z}+nD$ for positive integers $n$. There is exactly one of each finite additive index $n$.

[Read the paper (PDF)](counterexample/main.pdf) · [LaTeX source files](counterexample/)

## Hereditary atomicity and hereditary ACCP in semilocal domains

Every local domain that fails ACCP contains a nonatomic subring. More generally, if $D$ is semilocal (has finitely many maximal ideals), then every unital subring of $D$ is atomic if and only if every unital subring of $D$ satisfies ACCP. Thus any hereditarily atomic counterexample to ACCP must have infinitely many maximal ideals.

[Read the paper (PDF)](semilocal/main.pdf) · [LaTeX source](semilocal/main.tex)

## A further counterexample to weak ACCP

We have also constructed a hereditarily atomic domain in $\mathbb{Q}(t)$ that fails even the weak-ACCP condition of Gotti and Li. In this example, $t^2$ and $(1-t)^2$ have only units as common divisors, yet each generates a principal ideal that starts an infinite strictly ascending chain. [Gotti and Li, *Divisibility and a weak ascending chain condition on principal ideals*](https://arxiv.org/abs/2212.06213)

Every unital subring of this example is **strongly atomic**, meaning that it is atomic and every pair of nonzero elements has a maximal common divisor.

## A hereditarily atomic domain that fails strong atomicity

**Hereditary atomicity does not imply strong atomicity.** In a separate construction, we obtain a hereditarily atomic domain $D \subseteq \mathbb{Q}(t)$ containing two nonzero elements $x,y$ with no maximal common divisor. For every common divisor $d$ of $x$ and $y$, there is a nonunit $u \in D$ such that $du$ still divides both $x$ and $y$.

The [variations theorem map](lean/SECTION9.md) gives the Lean statements and proofs for both examples and for the prescribed dimension and transcendence degree. The strong-atomicity construction has received independent AI review. Human verification is pending.

## Manuscripts and Lean proofs

The November 17, 2026 manuscript edition is tagged `v1.0.0`. The Lean package is version 1.0.0 and uses the release tag `lean-v1.0.0` and Lean 4.34.1. To cite a formalized result, give the manuscript title, theorem number, and Lean release tag.

GPT-6.2 Astra discovered the counterexample in the first manuscript, building on earlier results discovered by GPT-6 Astra, Claude Opus 5.5, and Fable 5.2. GPT-6.2 Astra also wrote the semilocal manuscript. Claude Opus 5.5 discovered its theorem on constructing a nonatomic subring containing a prescribed discrete valuation ring.

These two AI-authored manuscripts are archived here to document the results and their public release. If you use a result or discuss a proof, please link to the dated release and cite the relevant manuscript by title. For the variations, cite the versioned Lean package and the result in the variations theorem map.
