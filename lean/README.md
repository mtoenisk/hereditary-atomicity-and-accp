# Hereditary atomicity and ACCP

This Lean package proves that every hereditarily atomic semilocal domain is hereditarily ACCP, and constructs a hereditarily atomic domain in $\mathbb Q(t)$ that fails ACCP. Its [theorem map](THEOREMS.md) follows all 46 numbered results in the two November 17, 2026 manuscripts. The [variations map](SECTION9.md) includes weak ACCP for the original domain, a second domain with strict principal-ideal chains starting at both $t^2$ and $(1-t)^2$, and a hereditarily atomic domain with a pair without a maximal common divisor. It also proves the prescribed dimensions for all parameters.

The [arXiv theorem map](ARXIV_THEOREMS.md) follows the November 23 counterexample manuscript.

The Lean library also proves seven strict factorization inclusions among almost Dedekind overrings of the integer-valued polynomials. The original HA example supplies one witness for this supplementary theorem. [Hierarchy theorem and witnesses](STRICT_HIERARCHY.md)

## Build and verify

Install Git, Bash, Python 3.9 or later, and [elan](https://lean-lang.org/install/). Run these commands from the package directory (`lean/` in the GitHub repository). Elan selects Lean 4.34.1. Lake obtains the dependencies at the revisions recorded in the manifest, and the first command downloads the public mathlib build cache.

```sh
lake exe cache get
bash scripts/check.sh
```

The check imports every module listed in [MODULES](MODULES), builds the three libraries with warnings as errors, compiles the manuscript statements and downstream examples, and checks the transitive axioms of every shipped library declaration. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

To compare the map with the dated TeX, obtain the manuscript source archive and run `python3 check_map.py MANUSCRIPTS`, where `MANUSCRIPTS` is its extracted directory containing `semilocal/` and `counterexample/`. The checker compares SHA-256 hashes, printed theorem numbers, and TeX labels, including definitions and remarks that contribute to numbering. [Manuscript release and source archive](https://github.com/mtoenisk/hereditary-atomicity-and-accp/releases/tag/v1.0.0)

## Use the libraries

To use version 1.0.0, add this dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "hereditaryAtomicityAndACCP"
git = { url = "https://github.com/mtoenisk/hereditary-atomicity-and-accp.git", subDir = "lean" }
rev = "lean-v1.0.0"
```

Choose an import according to the result you need.

| Import | Example |
| --- | --- |
| `Factorization` | [Factor an element inside a chosen subring](examples/Factorization.lean). The shared library supplies atomicity, bounded factorization, hereditary predicates, and principal ideal chains. |
| `HereditaryAtomicity` | [Apply the prescribed-DVR theorem](examples/PrescribedDVR.lean). A local domain failing ACCP contains a nonatomic subring containing the specified DVR when its fraction field is algebraic over that of the DVR. |
| `UnconditionalCounterexample` | [Use both main theorems on the same domain](examples/Counterexample.lean). The subrings failing ACCP are precisely those of finite additive index. |

The results use unital subrings and their intrinsic units, divisibility, and irreducible factors. For instance, `Factorization.IsHereditarilyAtomic R` quantifies over all unital subrings of $R$, and `WfDvdMonoid R` is the ACCP predicate.

## Citation

*Hereditary Atomicity and ACCP*, Lean 4 formalization, version 1.0.0 (Git tag `lean-v1.0.0`). [Project repository](https://github.com/mtoenisk/hereditary-atomicity-and-accp)

For results in the November 17, 2026 manuscripts, cite the relevant title and theorem number together with the dated manuscript release and the Git revision of the Lean source used. For the supplementary hierarchy, cite `UnconditionalCounterexample.StrictHierarchy.strictInclusions` and the Git revision of the Lean source.

- *A hereditarily atomic domain without ACCP*. [Manuscript](https://github.com/mtoenisk/hereditary-atomicity-and-accp/blob/c6054aa514779d63b96eb44a93cf82a629ac7b63/counterexample/main.pdf)
- *Hereditary atomicity and hereditary ACCP in semilocal domains*. [Manuscript](https://github.com/mtoenisk/hereditary-atomicity-and-accp/blob/c6054aa514779d63b96eb44a93cf82a629ac7b63/semilocal/main.pdf)

Both manuscripts identify themselves as AI-authored. GPT-6.2 Astra discovered the counterexample in the first manuscript, building on earlier results discovered by GPT-6 Astra, Claude Opus 5.5, and Fable 5.2. GPT-6.2 Astra also wrote the semilocal manuscript. Claude Opus 5.5 discovered its theorem on constructing a nonatomic subring containing a prescribed discrete valuation ring. [Manuscript release credits](https://github.com/mtoenisk/hereditary-atomicity-and-accp/tree/c6054aa514779d63b96eb44a93cf82a629ac7b63)

## License

The original Lean source is dedicated to the public domain under [CC0 1.0 Universal](LICENSE). Dependencies retain their upstream licenses. [Third-party notices](THIRD_PARTY.md)
