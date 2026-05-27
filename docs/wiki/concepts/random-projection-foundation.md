# Random-projection foundation: sketch matrix application

**ID:** `random-projection-foundation`  
**Chapter:** Ch10 (Bach §F7)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

Required prereq for Ch 10/12.

## Bach's textbook treatment

# Bach textbook excerpt — Random-projection foundation: sketch matrix application

**Concept ID:** `random-projection-foundation`
**Chapter:** Ch 10
**Section:** F7 (foundation derived from §10.2 "Random Projections and Averaging")
**Pages:** 288-290
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Section 10.2 (page 288) introduces sketching / random projection as two ways to apply
a random linear map to the OLS least-squares problem:

> "In this section, we consider random projections for ordinary least-squares (OLS),
> with the same notation as in chapter 3, with `y ∈ ℝⁿ` the response vector and
> `Φ ∈ ℝⁿˣᵈ` the design matrix, in two settings:
>
> • **Sketching:** Replacing `min_{θ ∈ ℝᵈ} ‖y − Φθ‖₂²` by
>   `min_{θ ∈ ℝᵈ} ‖Sy − SΦθ‖₂²`, where `S ∈ ℝˢˣⁿ` is an i.i.d. Gaussian matrix
>   (with independent zero mean and unit variance elements). This is an
>   idealization of subsampling done in the previous section. Here, we typically
>   have `n ≥ s ≥ d` (more observations than the feature dimension), and one of
>   the benefits of sketching is to be able to store a reduced representation of
>   the data (`ℝˢˣᵈ` instead of `ℝⁿˣᵈ`).
>
> • **Random projection:** Replacing `min_{θ ∈ ℝᵈ} ‖y − Φθ‖₂²` by
>   `min_{η ∈ ℝˢ} ‖y − ΦSη‖₂²`, where `S ∈ ℝᵈˣˢ` is a more general sketching
>   matrix. Here, we typically have `d ≥ n ≥ s` (high-dimensional situation).
>   The benefits of random projection are twofold: reduction in computation
>   time and regularization."

The foundation concept abstracts the common operation that underlies both
settings: applying a sketch matrix `S` (or `Φ`) to a vector to produce a
lower-dimensional projection.

## Proof (verbatim)
Definitional — the operation `(Φ, x) ↦ Φ · x` is the standard matrix-vector
product. The textbook does not "prove" the operation itself; it sets up the
algebraic playground in which Section 10.2's analyses (equations 10.1–10.6,
pages 290–296) take place.

## Notes
- The F7 anchor exists because Chapters 10 and 12 (random-feature models) both
  consume the sketch operation. Keeping it as a tiny Mathlib re-export
  avoids duplicating algebraic plumbing inside each chapter.
- The Gaussian assumption (i.i.d. `𝒩(0,1)`) is *not* part of the F7 definition;
  it is a hypothesis layered on top in §10.2.1 (Gaussian sketching, page 290).
- Technique in one line: package `Matrix.mulVec` under an LTFP-namespaced
  alias so the §10.2 algebra reads symbolically as `sketch Φ x`.
- Ambiguity: Bach uses `S` for the random matrix and `Φ` for the design matrix,
  but Lean's foundation uses `Φ` for "the sketch" since the same operator
  applies in both sketching (`S` left-multiplies `y`) and random-projection
  (`S` right-multiplies `Φ`) modes.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`sketch-add-mat`](./sketch-add-mat.md) — Sketching is linear in matrix
- [`sketch-add-matrix`](./sketch-add-matrix.md) — Sketch is linear in matrix
- [`sketch-linearity`](./sketch-linearity.md) — Random projection sketch is linear in input
- [`sketch-one`](./sketch-one.md) — Sketching by identity is identity
- [`sketch-smul-matrix`](./sketch-smul-matrix.md) — Sketching scales the matrix
- [`sketch-zero-matrix`](./sketch-zero-matrix.md) — Sketching with the zero matrix annihilates input

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/RandomProjection.lean`
- **Theorem/def name:** `sketch`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

