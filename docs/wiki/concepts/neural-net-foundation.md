# Neural-network foundation: ReLU activation

**ID:** `neural-net-foundation`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Neural-network`

## Statement

Required prereq for Ch 9/12.

## Bach's textbook treatment

# Bach textbook excerpt — Neural-network foundation: ReLU activation

**Concept ID:** `neural-net-foundation`
**Chapter:** Ch 9
**Section:** 9.2 (and F6, the LTFP-Lean "Foundations" auxiliary file)
**Pages:** 249, 253 (book; PDF pages 265, 269)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The ReLU (Rectified Linear Unit) activation function is

>     σ(u) = (u)_+ = max{u, 0}.

Bach introduces it at p. 249 as one of the activation functions of choice, and at
p. 253 announces:

> From now on, we will mostly focus on the ReLU activation σ(u) = u_+. The main
> property that we will employ is its "positive homogeneity"; that is, for α > 0,
> (αu)_+ = α u_+.

## Proof (verbatim)

This concept is a **definition / data carrier**, not a theorem. The mathematical
content is the choice of the ReLU as the activation, and the announcement that
positive homogeneity is the load-bearing property.

The other elementary algebraic facts about `max(u, 0)` — monotonicity, subadditivity,
non-negativity, identity on non-negatives, vanishing on non-positives, vanishing iff
non-positive — are used implicitly throughout chapter 9 but are not isolated as
lemmas in the textbook. They are catalogued under "F6" in the LTFP-Lean concept
registry precisely because they are the *foundation file's* obligation, not a
theorem Bach proves.

## Notes

- **Intermediate lemmas (downstream registry entries):**
  - `relu-positive-homog`: (α u)_+ = α u_+ for α ≥ 0 — Bach's "main property" (p. 253).
  - `relu-of-nonneg`, `relu-eq-self-of-nonneg`, `relu-le-id-of-nonneg`: identity-on-
    non-negatives behaviour.
  - `relu-neg-eq-zero`, `relu-eq-zero-iff`: vanishing on the non-positive half.
  - `relu-mono`: monotonicity (z ≤ z' ⇒ z_+ ≤ z'_+).
  - `relu-add-le`: subadditivity (x + y)_+ ≤ x_+ + y_+.
  - `relu-eq-relu`: reflexivity anchor.
- **Technique in one line:** ReLU = max(·, 0); all listed properties are immediate
  from max-of-zero algebra.
- **Where in Bach these foundational lemmas are USED (implicitly):**
  - **Positive homogeneity** (p. 253): drives the rescaling argument that lets
    Bach normalize ‖w_j‖₂² + b_j²/R² = 1 and put the ℓ_1-penalty on η — i.e., the
    setup for both estimation error (§9.2.3) and approximation theory (§9.3.2).
  - **Identity on non-negatives + vanishing on non-positives** (p. 256-257): the
    CPA-representation argument uses `(x − a_j)_+` to "switch on" a slope change at
    knot a_j and leave the function unchanged left of a_j.
  - **(0)_+ = 0** (p. 254, just before equation (9.3)): used directly to invoke
    proposition 4.4 in the Rademacher-complexity calculation that yields the 16GDR/√n
    estimation bound.
- **Ambiguities for Lean formalization.**
  - The ReLU may be defined in Lean as `Real.toNNReal` cast back to ℝ, as
    `max z 0`, as `if 0 ≤ z then z else 0`, or as `(z + |z|) / 2`. All four are
    extensionally equal; the F6 collection records the algebraic identities that any
    of these representations must satisfy.
  - The "F6" section tag is an internal LTFP-Lean convention, not a Bach section.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`relu-add-le`](./relu-add-le.md) — ReLU subadditivity: relu(x+y) ≤ relu x + relu y
- [`relu-eq-relu`](./relu-eq-relu.md) — ReLU equals itself (reflexivity anchor)
- [`relu-eq-self-of-nonneg`](./relu-eq-self-of-nonneg.md) — relu z = z when z ≥ 0
- [`relu-eq-zero-iff`](./relu-eq-zero-iff.md) — ReLU(z) = 0 ↔ z ≤ 0
- [`relu-le-id-of-nonneg`](./relu-le-id-of-nonneg.md) — relu z ≤ z when z ≥ 0
- [`relu-mono`](./relu-mono.md) — ReLU is monotone
- [`relu-neg-eq-zero`](./relu-neg-eq-zero.md) — ReLU at strictly negative is zero
- [`relu-of-nonneg`](./relu-of-nonneg.md) — ReLU is identity on nonneg inputs
- [`relu-positive-homog`](./relu-positive-homog.md) — ReLU positive homogeneity: relu(c·z) = c·relu(z) for c ≥ 0
- [`single-hidden-relu`](./single-hidden-relu.md) — Single-hidden-layer ReLU neural network

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

