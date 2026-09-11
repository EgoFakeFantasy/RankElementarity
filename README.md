# Unbounded reflection of elementary rank inclusions

[![Lean proof verification](https://github.com/EgoFakeFantasy/RankElementarity/actions/workflows/lean.yml/badge.svg)](https://github.com/EgoFakeFantasy/RankElementarity/actions/workflows/lean.yml)

Lean formalization of the following theorem, in the actual `ZFSet` cumulative
hierarchy with the pure membership language:

> If a < b < c are cardinals and V_a ≺ V_b ≺ V_c through the natural
> inclusions, then the ordinals delta < b with V_a ≺ V_delta are unbounded in b.

The public cardinal theorem is
`RankReflection.rankElementaryInclusion_unbounded` in
`RankReflection/Unbounded.lean`.

The proof establishes the stronger ordinal theorem
`RankReflection.exists_rankElementaryInclusion_between`: for arbitrary
ordinals alpha < beta < gamma and elementary natural inclusions
V_alpha ≺ V_beta ≺ V_gamma, every xi < beta has a witness delta with

    max alpha xi < delta < beta, and V_alpha ≺ V_delta.

`RankElementaryInclusion` means a Mathlib elementary embedding whose underlying
map fixes every actual set. It includes all first-order formulas with finite
parameters. It is not elementary equivalence or an arbitrary embedding.

## Proof

1. Proper elementary rank inclusions imply that the relevant heights are
   nonzero limits above omega. These facts are derived, not extra assumptions.
2. Relativize finite formulas to smaller rank domains and represent their
   actual satisfaction classes by genuine sets in larger domains.
3. Construct a finite pure membership formula for elementary inclusion and
   prove its full semantic correctness.
4. Construct a finite formula for the cumulative hierarchy using actual
   recursion graphs, and prove that its witnesses are the actual V_delta.
5. In V_gamma use beta as an existence witness, then reflect the single finite
   existence statement through V_beta ≺ V_gamma and decode the lower witness.

No regularity, inaccessibility, model-of-ZFC premise, truth oracle, or extra
reflection/definability hypothesis is added to the public theorem.

## Build and audit

Toolchain: `leanprover/lean4:v4.30.0`.

With [elan](https://github.com/leanprover/elan) installed:

```sh
git clone https://github.com/EgoFakeFantasy/RankElementarity.git
cd RankElementarity
lake exe cache get
lake build
```

The default target includes every project module and `RankReflection.AxiomAudit`.
The audit traverses all project theorem constants, collects their transitive
axiom dependencies, and fails on anything other than `propext`,
`Classical.choice`, and `Quot.sound`.

All dependencies use public Git repositories and are pinned in
`lake-manifest.json`. The direct dependency is
[FullMarkedBLP at b30d35a](https://github.com/EgoFakeFantasy/FullMarkedBLP/tree/b30d35a7801859f8bc100396616050d55c2df553),
which supplies the set-theoretic coding infrastructure and depends on Mathlib
v4.30.0. No sibling checkout or local path configuration is required.
Exact revisions are also listed in `dependencies.json`.

GitHub Actions builds the project from a fresh Ubuntu checkout, checks the
verified source hashes, and runs the axiom audit. The linked workflow reports
the current result. The original local verification covered 1,244 build jobs
and all 102 project theorem constants; the 12 Lean files total 905 lines.

The formalization is a Lean theorem about Mathlib's actual `ZFSet` objects.
It does not additionally produce an object-level YesMetaZFC derivation certificate.

## Source responsibilities

| Module | Mathematical responsibility |
|---|---|
| RankInclusion | Natural inclusions and full first-order elementarity |
| FormulaRelativization | Restriction of quantifiers and elimination of class predicates |
| SetSatisfaction | Actual truth sets and the finite truth formula |
| TruthAgreement | Truth comparison equivalent to elementary inclusion |
| ElementaryInclusionFormula | Finite pure formula and its bidirectional correctness |
| RankLimits | Limit and coding bounds derived from elementary inclusion |
| HierarchyFormula | Internal hierarchy graphs identify actual rank stages |
| ReflectionFormula | One finite existential statement used in reflection |
| ReflectionSemantics | Decoding all internal witnesses to the mathematical statement |
| Unbounded | Stronger ordinal theorem and the requested cardinal theorem |
| AxiomAudit | Default-built, fail-closed transitive axiom audit |

## Sources

The proof uses [Mathlib](https://github.com/leanprover-community/mathlib4)'s
`SetTheory/ZFC/VonNeumann`, `ModelTheory/ElementaryMaps`, ordinal and cardinal
interfaces, and [FullMarkedBLP](https://github.com/EgoFakeFantasy/FullMarkedBLP)'s rank-domain language,
formula coding, truth matrix, finite assignments and hierarchy recursion.
It imports the existing libraries rather than copying their source.
See `ProofNaming.md` for naming conventions and `VERIFICATION.md` for the
completed verification record.
