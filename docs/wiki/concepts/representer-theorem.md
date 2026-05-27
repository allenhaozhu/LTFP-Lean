# Representer theorem (orthogonal-projection core)

**ID:** `representer-theorem`  
**Chapter:** Ch07 (Bach §7.2, p. 181)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** B  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `RKHS`, `Ridge`, `ERM`

## Statement

Promoted from Tier C (was: Aronszajn / Moore-Aronszajn RKHS theorem — RKHS module mostly absent in Mathlib). Landed the orthogonal-projection algebraic core via Mathlib's Submodule.starProjection: in any real inner-product space E, for vectors e : Fin n → E and S = span ℝ (range e) with HasOrthogonalProjection, the projection f_S = S.starProjection f satisfies ⟨f_S, eⱼ⟩ = ⟨f, eⱼ⟩ for all j (data-fit term unchanged) and ‖f_S‖ ≤ ‖f‖ (regularizer non-increased). Corollary `representer_objective_le` shows that for any objective L((⟨f,eⱼ⟩)ⱼ) + Ω(‖f‖) with Ω monotone, replacing f by f_S weakly decreases the objective. The RKHS-specific bridge (reproducing property f(xⱼ) = ⟨f, k(·, xⱼ)⟩_ℋ) remains pending until Mathlib lands a proper RKHS construction; the algebraic skeleton is now complete and Mathlib- compatible.

## Bach's textbook treatment

# Bach textbook excerpt — Representer theorem (orthogonal-projection core)

**Concept ID:** `representer-theorem`
**Chapter:** Ch 7
**Section:** §7.2 (Representer Theorem)
**Pages:** 181-182 (book) / PDF pp. 197-198
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Proposition 7.1 (Representer theorem). *Consider a feature map* $\phi : \mathcal{X} \to \mathcal{H}$. *Let* $(x_1, \dots, x_n) \in \mathcal{X}^n$, *and assume that the functional* $\Psi : \mathbb{R}^{n+1} \to \mathbb{R}$ *is strictly increasing with respect to the last variable. Then the infimum of*
$$\Psi(\langle \theta, \phi(x_1)\rangle, \dots, \langle \theta, \phi(x_n)\rangle, \|\theta\|^2)$$
*can be obtained by restricting to a vector* $\theta$ *in the span of* $\phi(x_1), \dots, \phi(x_n)$; *that is, of the form*
$$\theta = \sum_{i=1}^n \alpha_i \, \phi(x_i),\qquad \alpha \in \mathbb{R}^n.$$

Corollary 7.1 (Representer theorem for supervised learning). *For* $\lambda > 0$, *the infimum of*
$\frac{1}{n} \sum_{i=1}^n \ell(y_i, \langle \theta, \phi(x_i)\rangle) + \frac{\lambda}{2}\|\theta\|^2$
*can be obtained by restricting to vector* $\theta$ *of the form* $\theta = \sum_{i=1}^n \alpha_i \phi(x_i)$, *with* $\alpha \in \mathbb{R}^n$.

## Proof (verbatim)

"Let $\theta \in \mathcal{H}$, and $\mathcal{H}_D = \{\sum_{i=1}^n \alpha_i \phi(x_i),\ \alpha \in \mathbb{R}^n\} \subset \mathcal{H}$, the linear span of the observed feature vectors. Let $\theta_D \in \mathcal{H}_D$ and $\theta_\perp \in \mathcal{H}_D^\perp$ be such that $\theta = \theta_D + \theta_\perp$, a decomposition that is using the Hilbertian structure of $\mathcal{H}$. Then $\forall i \in \{1, \dots, n\}$, $\langle \theta, \phi(x_i)\rangle = \langle \theta_D, \phi(x_i)\rangle + \langle \theta_\perp, \phi(x_i)\rangle$ with $\langle \theta_\perp, \phi(x_i)\rangle = 0$, by definition of the orthogonal.

From the Pythagorean theorem, we get $\|\theta\|^2 = \|\theta_D\|^2 + \|\theta_\perp\|^2$. Therefore, we have
$\Psi(\langle\theta,\phi(x_1)\rangle,\dots,\langle\theta,\phi(x_n)\rangle,\|\theta\|^2) = \Psi(\langle\theta_D,\phi(x_1)\rangle,\dots,\langle\theta_D,\phi(x_n)\rangle,\|\theta_D\|^2 + \|\theta_\perp\|^2) \ge \Psi(\langle\theta_D,\phi(x_1)\rangle,\dots,\langle\theta_D,\phi(x_n)\rangle,\|\theta_D\|^2),$
with equality if and only if $\theta_\perp = 0$ (since $\Psi$ is strictly increasing with respect to the last variable). Thus,
$\inf_{\theta \in \mathcal{H}} \Psi(\dots, \|\theta\|^2) = \inf_{\theta \in \mathcal{H}_D} \Psi(\dots, \|\theta\|^2)$,
which is exactly the desired result."

## Notes

- Bach attributes Corollary 7.1 to Kimeldorf and Wahba (1971); the general form (Proposition 7.1) to Schölkopf et al. (2001).
- Proof technique: **orthogonal decomposition** $\theta = \theta_D + \theta_\perp$ w.r.t. the data-span subspace $\mathcal{H}_D$, then Pythagoras + strict monotonicity of $\Psi$ in the last argument.
- **High-stakes carrier B7** (`representer_theorem_via_feature_map`) and a wiki-flagged orphan. The Lean encoding (`LTFP/Ch07_Kernels/Representer.lean#representer_objective_le`) names the bound "objective decreases under projection," which corresponds to Bach's inequality $\Psi(\dots,\|\theta\|^2) \ge \Psi(\dots,\|\theta_D\|^2)$ above.
- Key intermediate lemmas cited by Bach: (i) orthogonal decomposition in a real Hilbert space; (ii) Pythagorean identity $\|\theta\|^2 = \|\theta_D\|^2 + \|\theta_\perp\|^2$; (iii) the reproducing-property fact $\langle \theta_\perp, \phi(x_i)\rangle = 0$ for $\theta_\perp \in \mathcal{H}_D^\perp$.
- No assumption on the loss $\ell$ (no convexity needed) — Bach emphasizes this is "to be contrasted to the use of duality in section 7.4.4, where convexity will play a major role."
- **Flagged ambiguity:** Bach uses ">" in the displayed inequality `Ψ(...) > Ψ(...,||θ_D||²)` in the original prose — this should be "≥" since the inequality is non-strict (it is strict iff $\theta_\perp \ne 0$). PDF appears to use ≥ but text extraction renders it as `>`. The verbatim above preserves the intended ≥.

## Prerequisites (Bach's dependency graph)

- [`kernel-expansion`](./kernel-expansion.md) — Kernel-expansion predictor f(x) = ∑ᵢ αᵢ k(x, xᵢ)
- [`rkhs-foundation`](./rkhs-foundation.md) — RKHS foundation: real Hilbert space + feature map

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Representer.lean`
- **Theorem/def name:** `representer_objective_le`
- **Status:** B
- **Primary closing commit:** `008f09c` (theorem `representer_theorem_rkhs`)
- **Audit class:** **B**
- **Audit notes:** General kernel needs `IsReproducingFeatureMap` witness from caller

## Audit history (if any)

- commit `008f09c` — theorem `representer_theorem_rkhs` — classified **B** in PROGRESS.md §10 (General kernel needs `IsReproducingFeatureMap` witness from caller)

## Notes / open questions

- Carrier is **parametric** — at least one substantive hypothesis is passed through, not discharged.
- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

