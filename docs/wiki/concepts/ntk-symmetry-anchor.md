# NTK kernel symmetry algebraic anchor

**ID:** `ntk-symmetry-anchor`  
**Chapter:** Ch12 (Bach §12.4, p. 375)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `RKHS`, `Kernel`, `Neural-network`

## Statement

Tier C anchor for ntk-lazy-training (Bach 2024 §12.4). Promoted
from a single mul_comm placeholder to two real Lean proofs:
(1) `linearization_quadratic` proves the algebraic skeleton of
first-order NTK linearization for `f(θ) = ½‖θ‖²`,
`f(θ+Δθ) - f(θ) - ⟨∇f(θ), Δθ⟩ = ½‖Δθ‖²` (exact, by `ring`).
(2) `lazy_regime_param_movement` proves `1/√m → 0` in the
ε-N (tendsto) form, encoding the rate at which relative parameter
movement vanishes as width m → ∞. Documented gap: the full NTK
convergence theorem (gradient flow on the wide network tracks
gradient flow on the kernel) requires Mathlib infrastructure for
Fréchet derivatives + Bochner integrals over RKHS not yet
vendored.


## Bach's textbook treatment

# Bach textbook excerpt — NTK kernel symmetry algebraic anchor

**Concept ID:** `ntk-symmetry-anchor`
**Chapter:** Ch 12
**Section:** 12.4 Lazy Regime and Neural Tangent Kernels
**Pages:** 375-377
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
> **Lazy training.** We now consider a third training regime, which we refer to as the
> "lazy" regime, following Chizat et al. (2019). It corresponds to initializing each η_j
> with a scaling proportional to √m. This is made possible by having zero mean
> initializations so that a mean of m terms is of order O(1/√m) and not O(1) (leading
> to an overall predictor that remains O(1)). We will formalize this training regime
> by seeing this model as a diverging constant α (here √m) multiplied by a classical
> model with a mean-field limit.

> In the lazy regime, we end up minimizing G(V) = R(α·h(V)) with respect to
> V = (v₁, …, v_m), with a scaling factor α > 0 that tends to infinity, using a
> gradient flow on V, started at V(0) such that α·h(V(0)) remains bounded. In our
> neural network example, α = √m and h is the regular neural network in
> equation (12.26). Note that αh(V) = (1/√m)·Σⱼ Ψ(vⱼ), and the overall rescaling
> constant is now 1/√m.

> We consider the gradient flow to minimize G(V), with a step size 1/α² (scaling
> adapted to have a nontrivial dynamic); that is,
>   (d/dt) V(t) = −(1/α²) G'(V) = −(1/α) Dh(V)⊤ R'(α·h(V(t))),   (12.27)
> where Dh(V) is the differential of h at V. For the predictor αh(V), we get
>   (d/dt) [α·h(V(t))] = −Dh(V(t)) Dh(V(t))⊤ R'(α·h(V(t))).      (12.28)

> **Neural tangent kernel (◇).** If we assume that h(V(0)) = 0 (e.g., for neural
> networks, assuming that all initial neurons come in pairs, with the same input
> weights and opposite output weights), then the affine model has only a linear part
> proportional to Dh(αV(0))·V. We can thus associate to it a kernel, referred to as
> the "neural tangent kernel" (Jacot et al., 2018).

## Proof (verbatim)
> To make things concrete, for neural networks with one hidden layer,
>   h(x, v₁, …, v_m) = (1/√m) Σⱼ ηⱼ σ(wⱼ⊤ x + bⱼ),
> the corresponding features for each j ∈ {1, …, m} are
>   derivative w.r.t. ηⱼ:  (1/√m) σ(wⱼ(0)⊤ x + bⱼ(0))
>   derivative w.r.t. wⱼ:  (1/√m) ηⱼ(0) σ'(wⱼ(0)⊤ x + bⱼ(0)) x
>   derivative w.r.t. bⱼ:  (1/√m) ηⱼ(0) σ'(wⱼ(0)⊤ x + bⱼ(0)).
>
> When the initialization of neuron weights is random, we get the equivalent kernel
> by the law of large numbers:
>   k(x, x') = E[σ(w⊤x + b)σ(w⊤x' + b)]
>            + E[σ'(w⊤x + b)σ'(w⊤x' + b)·(x⊤x' + 1)],     (12.29)
> where the expectations are taken with respect to parameters (w, b) with
> distributions given by the chosen initialization (e.g., Gaussians). The first part
> in the right side of equation (12.29) is the traditional random feature kernel
> discussed in section 9.5, but it also has an additional part, which creates a
> richer model but cannot correct entirely the intrinsic limitations of kernel
> methods (see, e.g., Bietti and Bach, 2021, and references therein).

## Notes
- This concept is the algebraic Tier-C anchor for `ntk-lazy-training` (B8 carrier).
- Symmetry property comes for free: k(x, x') = k(x', x) because the kernel is
  defined as a sum of two expectations of symmetric inner products
  (σ(w⊤x+b)σ(w⊤x'+b) and σ'(w⊤x+b)σ'(w⊤x'+b)(x⊤x'+1)) — both invariant under
  swapping x ↔ x'.
- LAZY TRAINING FINDING: the Lean carrier `lazy_training_generalization_shape`
  encodes "1/√m → 0" rate (parameter movement vanishes as width m → ∞) and the
  "exact algebraic skeleton" of NTK linearization
  f(θ + Δθ) − f(θ) − ⟨∇f(θ), Δθ⟩ = ½‖Δθ‖² for f(θ) = ½‖θ‖² (proved by `ring`).
- NTK random-init concentration (B8 deferred work): the limit k(x, x') is via LLN
  over random init of (w, b); concentration is mentioned informally ("by the law
  of large numbers") but not given a non-asymptotic bound — this is the documented
  gap.
- Technique in one line: first-order Taylor expansion of α·h(V) around V(0) +
  scaling step size 1/α² + α → ∞ ⇒ predictor evolves under a fixed kernel.
- Ambiguities: §12.4 is informal ("◇" = optional/advanced); no proof of full NTK
  convergence theorem (gradient flow on wide network tracks kernel regression) is
  given — Bach cites Jacot et al. (2018) and Du et al. (2018).

## Prerequisites (Bach's dependency graph)

- [`implicit-bias-full-rank`](./implicit-bias-full-rank.md) — Implicit bias of GD = OLS (full-rank case)

## Dependents (concepts that use this)

- [`ntk-concentration-scalar-hoeffding`](./ntk-concentration-scalar-hoeffding.md) — Empirical NTK concentration via scalar Hoeffding + union bound (N4 alt)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch12_Overparameterized/ImplicitBias.lean`
- **Theorem/def name:** `ntk_kernel_symm_anchor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

