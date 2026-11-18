# Hereditary atomicity and ACCP

This Lean package proves that every hereditarily atomic semilocal domain is hereditarily ACCP, and constructs a hereditarily atomic domain in $\mathbb Q(t)$ that fails ACCP. Its [theorem map](THEOREMS.md) follows all 46 numbered results in the two November 17, 2026 manuscripts.

## Build and verify

Install Git, Bash, Python 3.9 or later, and [elan](https://lean-lang.org/install/). Run these commands from the repository root. Elan selects Lean 4.34.1. Lake obtains the dependencies at the revisions recorded in the manifest and downloads the public mathlib build cache.

```sh
cd lean
lake exe cache get
bash scripts/check.sh
python3 check_map.py ..
```

The check imports every module listed in [MODULES](MODULES), builds the three libraries with warnings as errors, compiles the manuscript statements, and checks the transitive axioms of every shipped library declaration. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The last command compares the theorem map with the manuscripts included in this release. It checks SHA-256 hashes, printed theorem numbers, and TeX labels, including definitions and remarks that contribute to numbering. [November 17 manuscript release](https://github.com/mtoenisk/hereditary-atomicity-and-accp/releases/tag/v1.0.0)

## Use the libraries

Add this dependency to your project's `lakefile.toml` to use the formalization from the companion release.

```toml
[[require]]
name = "hereditaryAtomicityAndACCP"
git = { url = "https://github.com/mtoenisk/hereditary-atomicity-and-accp.git", subDir = "lean" }
rev = "lean-v0.1.0"
```

Choose an import according to the result you need.

| Import | Example |
| --- | --- |
| `Factorization` | [Factor an element inside a chosen subring](examples/Factorization.lean). The shared library supplies atomicity, bounded factorization, hereditary predicates, and principal ideal chains. |
| `HereditaryAtomicity` | [Apply the prescribed-DVR theorem](examples/PrescribedDVR.lean). A local domain failing ACCP contains a nonatomic subring containing the specified DVR when its fraction field is algebraic over that of the DVR. |
| `UnconditionalCounterexample` | [Use both main theorems on the same domain](examples/Counterexample.lean). The subrings failing ACCP are precisely those of finite additive index. |

The results use unital subrings and their intrinsic units, divisibility, and irreducible factors. For instance, `Factorization.IsHereditarilyAtomic R` quantifies over all unital subrings of $R$, and `WfDvdMonoid R` is the ACCP predicate.

## Cite the mathematics

Cite the relevant November 17, 2026 manuscript by title and theorem number, together with the dated manuscript release and the Git revision of the Lean source used.

- *A hereditarily atomic domain without ACCP*. [Manuscript](https://github.com/mtoenisk/hereditary-atomicity-and-accp/blob/c6054aa514779d63b96eb44a93cf82a629ac7b63/counterexample/main.pdf)
- *Hereditary atomicity and hereditary ACCP in semilocal domains*. [Manuscript](https://github.com/mtoenisk/hereditary-atomicity-and-accp/blob/c6054aa514779d63b96eb44a93cf82a629ac7b63/semilocal/main.pdf)

Both manuscripts identify themselves as AI-authored. GPT-6.2 Astra discovered the counterexample in the first manuscript, building on earlier results discovered by GPT-6 Astra, Claude Opus 5.5, and Fable 5.2. GPT-6.2 Astra also wrote the semilocal manuscript. Claude Opus 5.5 discovered its theorem on constructing a nonatomic subring containing a prescribed discrete valuation ring. [Manuscript release credits](https://github.com/mtoenisk/hereditary-atomicity-and-accp/tree/c6054aa514779d63b96eb44a93cf82a629ac7b63)

## License

The original Lean source is dedicated to the public domain under [CC0 1.0 Universal](LICENSE). Dependencies retain their upstream licenses. [Third-party notices](THIRD_PARTY.md)
