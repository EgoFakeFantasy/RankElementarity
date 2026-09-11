# Proof naming convention

This project follows PCFAlephOmega4 and FullMarkedBLP.

- Files, structures and main predicates use `UpperCamelCase`.
- Data-producing functions use `lowerCamelCase`.
- Theorem names use mathematical clauses separated by underscores; established
  domain expressions such as `rankElementaryInclusion` remain intact.
- Existence theorems begin with `exists_`; `_iff`, `_of_`, `_le`, and `_lt`
  describe the actual mathematical relationship.
- Cardinals use `a`, `b`, `c`; ordinal heights use `alpha`, `beta`, `gamma`,
  `delta`, `eta`; `xi` is a prescribed lower bound.
- Hypotheses use semantic names such as `hAB`, `hElemAB`, `hOmegaAlpha`,
  `hBooks`, and `hDomain`.
- Public names do not encode development history. Public interfaces explain
  their actual hypotheses and mathematical meaning.
- This is a host-level Mathlib proof about actual ZFSet rank domains. It does
  not adopt the object-theory layer suffixes of YesMetaZFC.
