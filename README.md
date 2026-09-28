# Mathlib catalogue

Evidence about Mathlib's definitions, declared from outside Mathlib with
[TrustAnnotations](https://github.com/LeanTrustBuilders/annotations): where each definition is meant
to apply (`@[domain]`), what it is determined up to (`@[up_to]`), and characterizations stated by one theorem, with the specification lemmas
that show the definition has its property. Part of the [LeanTrustBuilders](https://github.com/LeanTrustBuilders)
suite; see `well-definedness.md` in the design notes.

| module | about |
|---|---|
| `MathlibCatalogue.Real` | the real numbers, characterized up to isomorphism as the conditionally complete linearly ordered field, by an isomorphism that also preserves the operations Mathlib defines on `ℝ` separately (`0`, `1`, `-`, `⁻¹`, `<`, `max`, `min`, the casts) |
| `MathlibCatalogue.Moments` | the domains of `Real.log` (`0 < x`) and of `moment`, `centralMoment`, `mgf` and `cgf`: the well-definedness analyzer checks their bodies under them, and their uses in Mathlib's statements |
| `MathlibCatalogue.Discharger` | `mathlib_catalogue_discharger`: the facts that show the catalogue's domains in probability theory (L² random variables, martingales, set integrals, stopped processes), a `solve_by_elim` the well-definedness analyzer tries after its default dischargers |
| `MathlibCatalogue.MeasureTheory` | the Bochner integral (domain; characterization of the real case by ∫⁺ − ∫⁻), conditional expectation and the Radon–Nikodym derivative (each: domain, determined up to a.e. equality, characterization by Mathlib's uniqueness theorem) |

Mathlib's own theorems cannot carry an annotation written outside Mathlib (TrustAnnotations refuses
an entry whose two declarations are both imported), so characterizations and specification lemmas
are restated here, each proved by the Mathlib lemma it restates. Domains need no restatement:
`attribute [domain …] d` works on a definition of another library.

## How it reaches a site

CI builds the catalogue against Mathlib at the release tag in `lakefile.toml`, extracts its dataset
with the [extractor](https://github.com/LeanTrustBuilders/extractor) (its own theorems as the
project, the Mathlib declarations they mention as upstream nodes, with the annotations), and
publishes it as the release `dataset-<commit12>`. A site merges it into the Mathlib dataset of the
same tag (`evidence-core merge`), which checks that the two agree on every declaration they share,
and builds from the result: the [Mathlib probability site](https://leantrustbuilders.github.io/site-pilot/mathlib-probability/).

## Adding to it

A new module under `MathlibCatalogue/`, imported by `MathlibCatalogue.lean`. Keep Mathlib at the tag
of the newest Mathlib dataset, and TrustAnnotations on the branch for its toolchain.
