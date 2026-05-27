# RKHS foundation: real Hilbert space + feature map

**ID:** `rkhs-foundation`  
**Chapter:** Ch07 (Bach §F4b)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `RKHS`

## Statement

Required prereq for Ch 7/9/12.

## Bach's textbook treatment

# Bach textbook excerpt — RKHS foundation: real Hilbert space + feature map

**Concept ID:** `rkhs-foundation`
**Chapter:** Ch 7
**Section:** §7.3 (Kernels) / Foundation F4b
**Pages:** 183-184 (book) / PDF pp. 199-200
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Proposition 7.3 (Aronszajn, 1950). *The function* $k : \mathcal{X} \times \mathcal{X} \to \mathbb{R}$ *is a positive-definite kernel if and only if there exists a Hilbert space* $\mathcal{H}$, *and a function* $\phi : \mathcal{X} \to \mathcal{H}$ *such that for all* $x, x' \in \mathcal{X}$, $k(x, x') = \langle\phi(x), \phi(x')\rangle_\mathcal{H}.$

The space $\mathcal{H}$ thus produced is called the **feature space** and $\phi$ the **feature map**; for any positive-definite kernel $k$, the canonical such space is the **reproducing kernel Hilbert space (RKHS)** associated with $k$, with $\phi(x) = k(\cdot, x)$.

## Proof (verbatim)

"Partial proof: We first assume that $k(x,x') = \langle\phi(x),\phi(x')\rangle_\mathcal{H}$. Then, for any $\alpha \in \mathbb{R}^n$ and points $x_1, \dots, x_n \in \mathcal{X}$, we have, for the kernel matrix $K$ associated with these points,
$\alpha^\top K\alpha = \sum_{i,j=1}^n \alpha_i \alpha_j \langle\phi(x_i),\phi(x_j)\rangle_\mathcal{H} = \big\|\sum_i \alpha_i \phi(x_i)\big\|_\mathcal{H}^2 \ge 0.$
Thus, $k$ is a positive-definite kernel.

For the other direction, we consider a positive-definite kernel, and we will construct a space of functions explicitly from $\mathcal{X}$ to $\mathbb{R}$ with a dot product. We define $\mathcal{H}' \subset \mathbb{R}^\mathcal{X}$ as the set of linear combinations of kernel functions $\sum_{i=1}^n \alpha_i k(\cdot, x_i)$ for any integer $n$, any set of $n$ points, and any $\alpha \in \mathbb{R}^n$. This is a vector space on which we can define a dot product through
$$\Big\langle \sum_{i=1}^n \alpha_i k(\cdot,x_i),\ \sum_{j=1}^m \beta_j k(\cdot, x'_j)\Big\rangle = \sum_{i=1}^n \sum_{j=1}^m \alpha_i \beta_j k(x_i, x'_j). \quad (7.3)$$

We first check that this is a well-defined function on $\mathcal{H}' \times \mathcal{H}'$; that is, the value does not depend on the chosen representation as a linear combination of kernel functions. … This dot product is bi-linear and always nonnegative when applied to the same function… Moreover, this dot product satisfies the two properties for any $f \in \mathcal{H}'$, $x, x' \in \mathcal{X}$:
$$\langle k(\cdot, x), f\rangle = f(x) \quad \text{and} \quad \langle k(\cdot, x), k(\cdot, x')\rangle = k(x, x').$$
These are called 'reproducing properties' and correspond to an explicit construction of the feature map $\phi(x) = k(\cdot, x)$.

To obtain a dot product, we only need to show that $\langle f, f\rangle = 0$ implies $f = 0$. This can be shown using Cauchy-Schwarz inequality, leading to … $f(x)^2 = \langle f, k(\cdot,x)\rangle^2 \le \langle f, f\rangle \langle k(\cdot,x), k(\cdot,x)\rangle = \langle f,f\rangle k(x,x)$, leading to $f = 0$ as soon as $\langle f, f\rangle = 0$.

Space $\mathcal{H}'$ is called 'pre-Hilbertian' because it is not complete. It can be completed into a Hilbert space $\mathcal{H}$ with the same reproducing property. **See Aronszajn (1950) and Berlinet and Thomas-Agnan (2004) for more details.**"

## Notes

- **Bach defers the completion step** to Aronszajn (1950) and Berlinet & Thomas-Agnan (2004). The Lean side handles this in `LTFP/MathlibExt/Analysis/InnerProductSpace/AronszajnCompletion.lean`.
- Proof technique: explicit construction of pre-Hilbert space of finite kernel sums, equip with the bilinear form (7.3), invoke Cauchy-Schwarz to get nondegeneracy, then metric completion.
- Key intermediate lemmas: (i) well-definedness of (7.3) (representation-independent because the bilinear form equals $\sum_j \beta_j f(x'_j)$); (ii) Cauchy-Schwarz for positive semidefinite bilinear forms (Bach footnote 2 cautions this is the symmetric-PSD version, which need not be definite); (iii) reproducing property $\langle k(\cdot,x), f\rangle = f(x)$.
- "No assumption is needed about the input space $\mathcal{X}$, and no regularity assumption is needed for $k$."
- Up to isomorphism the (feature space, feature map) pair is unique — this is why one can refer to *the* RKHS.
- **Flagged ambiguity:** PDF extraction shows ≥ as ">" and ≤ as "6" in places — corrected above.

## Prerequisites (Bach's dependency graph)

- [`kernel-foundation`](./kernel-foundation.md) — Positive-definite kernel foundation: IsPSDKernel

## Dependents (concepts that use this)

- [`representer-theorem`](./representer-theorem.md) — Representer theorem (orthogonal-projection core)
- [`rkhs-kernel-def`](./rkhs-kernel-def.md) — RKHS kernel extensional definition
- [`rkhs-kernel-self-nonneg`](./rkhs-kernel-self-nonneg.md) — RKHS kernel self-evaluation is nonneg

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/RKHS.lean`
- **Theorem/def name:** `RKHS`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

