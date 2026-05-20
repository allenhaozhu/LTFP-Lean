/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Analysis.InnerProductSpace.RKHS
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Aronszajn completion of the pre-RKHS — Stage 2 (SeparationQuotient)

This module continues the Moore–Aronszajn construction begun in
`LTFP.MathlibExt.Analysis.InnerProductSpace.RKHS`. Stage 1 produced a
`PreInnerProductSpace.Core ℝ (𝒳 →₀ ℝ)` from a symmetric PSD kernel
`K : 𝒳 → 𝒳 → ℝ`, namely `preRKHSCore_of_psd_kernel hsym hpsd`. Stage 2
— the content of this module — passes to the separation quotient of
the resulting seminormed space, turning the *pre-*inner-product on
`𝒳 →₀ ℝ` into an honest inner product on the quotient.

## Construction outline

Concretely, we equip a type synonym `KernelPreRKHS K` (for `𝒳 →₀ ℝ`)
with three pieces of structure, all forwarded from the underlying
`PreInnerProductSpace.Core`:

* `SeminormedAddCommGroup (KernelPreRKHS K)` (via
  `PreInnerProductSpace.Core.toSeminormedAddCommGroup`);
* `NormedSpace ℝ (KernelPreRKHS K)` (via
  `PreInnerProductSpace.Core.toNormedSpace`);
* `InnerProductSpace ℝ (KernelPreRKHS K)` (via
  `InnerProductSpace.ofCore`).

The symmetry + PSD witnesses are bundled into a single class
`IsRKHSKernel K` so that the analytic instances on `KernelPreRKHS K`
can resolve via the typeclass system rather than via explicit
`letI`-threading at every call site.

With these instances available, Mathlib's library
(`Mathlib.Analysis.Normed.Group.Uniform` and
`Mathlib.Analysis.InnerProductSpace.Completion`) automatically
promotes the separation quotient to a `NormedAddCommGroup` and even an
`InnerProductSpace ℝ`. We package the result as
`KernelRKHSQuotient K`, the *quotient pre-RKHS*.

## Why a type synonym?

The free vector space `𝒳 →₀ ℝ` already has many algebra instances
floating around (additive structure, module structure). Attaching a
kernel-dependent seminorm directly to `𝒳 →₀ ℝ` would pollute the
global instance cache. A *type synonym* `KernelPreRKHS K` decouples
the kernel-dependent seminorm from the bare additive structure. The
user can write `KernelPreRKHS K` when they want the inner product and
`𝒳 →₀ ℝ` when they want only the algebra.

## Main definitions

* `KernelPreRKHS K` : a type synonym for `𝒳 →₀ ℝ`, viewed as the
  pre-RKHS of `K`.
* `IsRKHSKernel K` : a class bundling `IsSymmetricKernel K` and
  `IsPSDKernel K`, so the analytic structure on `KernelPreRKHS K`
  resolves via typeclass synthesis.
* `kernelPreRKHSCore` : the canonical
  `PreInnerProductSpace.Core ℝ (KernelPreRKHS K)`.
* `KernelRKHSQuotient K` : `SeparationQuotient (KernelPreRKHS K)`,
  the separation quotient. With `[IsRKHSKernel K]` in scope, this is
  a `NormedAddCommGroup` and an `InnerProductSpace ℝ`.
* `KernelRKHSQuotient.feature` : the quotient of the canonical
  pre-RKHS feature map; sends `x : 𝒳` to `[δ_x]` in
  `KernelRKHSQuotient K`.

## Main results

* `kernelPreRKHSCore_inner_apply` : the inner product on
  `KernelPreRKHS K` agrees with `kernelGramForm K` definitionally.
* `KernelRKHSQuotient.inner_mk_mk` : the quotient map preserves the
  inner product (a re-export of Mathlib's
  `SeparationQuotient.inner_mk_mk`).
* `KernelRKHSQuotient.inner_feature_feature` : the kernel feature
  identity at the quotient level —
  `⟪feature x, feature y⟫ = K x y`. This is the algebraic Aronszajn
  reproducing identity, lifted to the separation quotient.

## Relation to subsequent stages

Stage 3 (Hilbert completion via `UniformSpace.Completion`) and the
feature/evaluation/reproducing-property bundling that lands the result
in `RKHS_of_kernel K` are left to companion modules in this directory.
Phase 3a-1 supplies the Stage-2 backbone that those modules consume.
-/

@[expose] public section

namespace LTFP.MathlibExt.Analysis

open scoped InnerProductSpace

variable {𝒳 : Type*}

/-! ### The pre-RKHS type synonym -/

/-- **The pre-RKHS of a kernel.** A type synonym for `𝒳 →₀ ℝ`, used as
the carrier of the pre-inner product `kernelGramForm K`. The kernel `K`
is a phantom parameter: it does not affect the underlying type, only
the seminorm / inner-product structure attached to it. -/
def KernelPreRKHS (_K : 𝒳 → 𝒳 → ℝ) : Type _ := 𝒳 →₀ ℝ

namespace KernelPreRKHS

variable (K : 𝒳 → 𝒳 → ℝ)

/-- Convert a `KernelPreRKHS K`-valued vector to its underlying
`𝒳 →₀ ℝ` representation. -/
def toFinsupp (f : KernelPreRKHS K) : 𝒳 →₀ ℝ := f

/-- Convert a finitely-supported coefficient vector into the pre-RKHS. -/
def ofFinsupp (c : 𝒳 →₀ ℝ) : KernelPreRKHS K := c

@[simp] theorem toFinsupp_ofFinsupp (c : 𝒳 →₀ ℝ) :
    toFinsupp K (ofFinsupp K c) = c := rfl

@[simp] theorem ofFinsupp_toFinsupp (f : KernelPreRKHS K) :
    ofFinsupp K (toFinsupp K f) = f := rfl

/-- The underlying additive commutative group structure, forwarded from
`𝒳 →₀ ℝ`. -/
noncomputable instance : AddCommGroup (KernelPreRKHS K) :=
  inferInstanceAs (AddCommGroup (𝒳 →₀ ℝ))

/-- The underlying real-vector-space structure, forwarded from
`𝒳 →₀ ℝ`. -/
noncomputable instance : Module ℝ (KernelPreRKHS K) :=
  inferInstanceAs (Module ℝ (𝒳 →₀ ℝ))

end KernelPreRKHS

/-! ### The `IsRKHSKernel` class

We bundle the two algebraic hypotheses on a kernel — symmetry and
positive semidefiniteness — into a single typeclass so that the
analytic instances on `KernelPreRKHS K` and `KernelRKHSQuotient K` can
resolve via typeclass synthesis. -/

/-- **Class of RKHS-admissible kernels.** A kernel `K : 𝒳 → 𝒳 → ℝ` is
*RKHS-admissible* if it is symmetric and positive semidefinite. The
Moore–Aronszajn construction produces a reproducing-kernel Hilbert
space from any such kernel; this class is the prerequisite that lets
the analytic structure on `KernelPreRKHS K` and `KernelRKHSQuotient K`
auto-resolve. -/
class IsRKHSKernel (K : 𝒳 → 𝒳 → ℝ) : Prop where
  /-- The kernel is symmetric: `K x y = K y x`. -/
  symm : IsSymmetricKernel K
  /-- The kernel is positive semidefinite: every Gram matrix is PSD. -/
  psd : IsPSDKernel K

/-- Recover the underlying symmetry witness from an `IsRKHSKernel`
hypothesis. -/
theorem IsRKHSKernel.isSymmetricKernel {K : 𝒳 → 𝒳 → ℝ} [h : IsRKHSKernel K] :
    IsSymmetricKernel K := h.symm

/-- Recover the underlying PSD witness from an `IsRKHSKernel`
hypothesis. -/
theorem IsRKHSKernel.isPSDKernel {K : 𝒳 → 𝒳 → ℝ} [h : IsRKHSKernel K] :
    IsPSDKernel K := h.psd

/-! ### Pre-RKHS core from a symmetric PSD kernel

We expose `preRKHSCore_of_psd_kernel` as an instance under the
`IsRKHSKernel` hypothesis. The definition is a pure rewrap of
`preRKHSCore_of_psd_kernel`; no new mathematics is introduced. -/

/-- The canonical pre-inner-product on `KernelPreRKHS K`, given that
`K` is an `IsRKHSKernel`. -/
noncomputable instance kernelPreRKHSCore
    {K : 𝒳 → 𝒳 → ℝ} [h : IsRKHSKernel K] :
    PreInnerProductSpace.Core ℝ (KernelPreRKHS K) :=
  preRKHSCore_of_psd_kernel h.symm h.psd

namespace KernelPreRKHS

variable {K : 𝒳 → 𝒳 → ℝ} [IsRKHSKernel K]

/-- **Inner product on the pre-RKHS.** The inner product attached to
`KernelPreRKHS K` via `kernelPreRKHSCore` is the kernel Gram form. -/
theorem kernelPreRKHSCore_inner_apply (c c' : KernelPreRKHS K) :
    @inner ℝ _ (kernelPreRKHSCore (K := K)).toInner c c'
      = kernelGramForm K (toFinsupp K c) (toFinsupp K c') := rfl

/-! ### Seminormed and inner-product-space structure on the pre-RKHS

Given an `IsRKHSKernel`, we expose the seminormed-group, normed
space, and pre-inner-product structures as **noncomputable
instances**. These are picked up automatically by typeclass synthesis
when the user has `[IsRKHSKernel K]` in scope. -/

/-- The seminormed-additive-commutative-group structure on
`KernelPreRKHS K` induced by the pre-inner product.

The name `InnerProductSpace.Core.toSeminormedAddCommGroup` is somewhat
misleading: although it lives under the `InnerProductSpace.Core`
namespace, it is defined inside a section about
`PreInnerProductSpace.Core` and accepts a `PreInnerProductSpace.Core`
instance. We use it here. -/
noncomputable instance instSeminormedAddCommGroup :
    SeminormedAddCommGroup (KernelPreRKHS K) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup
    ℝ (KernelPreRKHS K) _ _ _ kernelPreRKHSCore

/-- The normed-space structure on `KernelPreRKHS K` induced by the
pre-inner product. -/
noncomputable instance instNormedSpace :
    NormedSpace ℝ (KernelPreRKHS K) :=
  @InnerProductSpace.Core.toNormedSpace
    ℝ (KernelPreRKHS K) _ _ _ kernelPreRKHSCore

/-- The (pre-)inner-product-space structure on `KernelPreRKHS K`. This
is a `PreInnerProductSpace` in the sense that the seminorm is not yet
known to be a norm — separating "pre" from "post" is the job of the
quotient construction below. -/
noncomputable instance instInnerProductSpace :
    InnerProductSpace ℝ (KernelPreRKHS K) :=
  InnerProductSpace.ofCore (cd := kernelPreRKHSCore)

end KernelPreRKHS

/-! ### Separation quotient of the pre-RKHS

We now form `SeparationQuotient (KernelPreRKHS K)` under the
kernel-dependent seminorm. With `[IsRKHSKernel K]` in scope, Mathlib's
automatic instances supply both a `NormedAddCommGroup` and an
`InnerProductSpace ℝ` on the quotient (see
`Mathlib.Analysis.Normed.Group.Uniform` and
`Mathlib.Analysis.InnerProductSpace.Completion`). -/

/-- **The quotient pre-RKHS.** This is `SeparationQuotient` applied to
the pre-RKHS `KernelPreRKHS K` under the kernel-induced seminorm. The
Mathlib library equips it with both a `NormedAddCommGroup` and an
`InnerProductSpace ℝ` automatically, given `[IsRKHSKernel K]`. The
quotient identifies coefficient vectors `c, c'` whenever
`‖c - c'‖_K = √⟨c - c', c - c'⟩_K = 0`, i.e. whenever they represent
the same function in the eventual Hilbert RKHS.

We require `[IsRKHSKernel K]` at the type level so that
`KernelPreRKHS K` is equipped with the seminormed-group topology
needed for `SeparationQuotient` to make sense. We use `abbrev` rather
than `def` so the typeclass system can unfold the definition
transparently and locate the inherited
`NormedAddCommGroup`/`InnerProductSpace ℝ` instances on the underlying
`SeparationQuotient (KernelPreRKHS K)`. -/
abbrev KernelRKHSQuotient (K : 𝒳 → 𝒳 → ℝ) [IsRKHSKernel K] : Type _ :=
  SeparationQuotient (KernelPreRKHS K)

namespace KernelRKHSQuotient

variable {K : 𝒳 → 𝒳 → ℝ} [IsRKHSKernel K]

/-- **The quotient map.** Send a coefficient vector `c ∈ KernelPreRKHS K`
to its equivalence class in `KernelRKHSQuotient K`. This is just an
alias for `SeparationQuotient.mk` (via `abbrev` so the unfolding is
transparent for typeclass synthesis). -/
noncomputable abbrev mk (c : KernelPreRKHS K) : KernelRKHSQuotient K :=
  SeparationQuotient.mk c

/-- The quotient map is surjective. -/
theorem surjective_mk : Function.Surjective (mk : KernelPreRKHS K → _) :=
  SeparationQuotient.surjective_mk

/-! ### Quotient inner-product computation

We re-export the elementary `SeparationQuotient.inner_mk_mk` rewrite
under the kernel-specific name. This is the key bookkeeping lemma for
downstream theorems: inner products in the quotient compute by lifting
to representatives. -/

/-- **Quotient inner product equals representative inner product.** For
any two coefficient vectors `c, c' : KernelPreRKHS K`, the inner
product of their quotient classes is the original kernel Gram form. -/
theorem inner_mk_mk (c c' : KernelPreRKHS K) :
    inner ℝ (mk c) (mk c')
      = kernelGramForm K (KernelPreRKHS.toFinsupp K c)
          (KernelPreRKHS.toFinsupp K c') := by
  -- The SeparationQuotient inner product on representatives is the
  -- original inner product (Mathlib's `SeparationQuotient.inner_mk_mk`),
  -- which on `KernelPreRKHS K` is the kernel Gram form because
  -- `kernelPreRKHSCore.inner = kernelGramForm K` definitionally.
  rw [SeparationQuotient.inner_mk_mk]
  -- Now the goal is `⟪c, c'⟫_ℝ = kernelGramForm K c c'`. The instance
  -- of `Inner` on `KernelPreRKHS K` comes from `instInnerProductSpace`,
  -- which is `InnerProductSpace.ofCore kernelPreRKHSCore` — its inner
  -- field is `kernelPreRKHSCore.inner = kernelGramForm K` by the
  -- anonymous-constructor `{ cd with ... }` shape of `ofCore`.
  rfl

/-! ### Kernel feature map at the quotient level

The pre-RKHS feature map `preRKHSFeature : 𝒳 → (𝒳 →₀ ℝ)` sends `x`
to `δ_x`. Composing with the quotient map gives the
*Aronszajn feature map* into `KernelRKHSQuotient K`. We expose it and
verify the reproducing identity. -/

variable [DecidableEq 𝒳]

/-- **The Aronszajn feature map at the quotient level.** Sends a point
`x : 𝒳` to the quotient class of the spike `δ_x` in
`KernelRKHSQuotient K`. -/
noncomputable def feature (x : 𝒳) : KernelRKHSQuotient K :=
  mk (KernelPreRKHS.ofFinsupp K (preRKHSFeature x))

/-- **Reproducing identity at the quotient level.** The inner product
of two quotient feature vectors equals the original kernel value,
`K x y`. This is the algebraic Aronszajn reproducing identity, now
honestly typed against the separation-quotient inner product. -/
theorem inner_feature_feature (x y : 𝒳) :
    inner ℝ (feature (K := K) x) (feature (K := K) y) = K x y := by
  -- Unfold `feature` and reduce via `inner_mk_mk` to the basis-feature
  -- Gram-form identity `kernelGramForm_feature_eq_kernel`.
  unfold feature
  rw [inner_mk_mk]
  -- `toFinsupp K (ofFinsupp K (preRKHSFeature x)) = preRKHSFeature x`
  -- by definition; reduce the goal to the basis-feature identity.
  show kernelGramForm K (preRKHSFeature x) (preRKHSFeature y) = K x y
  exact kernelGramForm_feature_eq_kernel K x y

end KernelRKHSQuotient

/-! ### Stage 3 / Hilbert-completion handoff

The full Aronszajn theorem requires one more stage: applying
`UniformSpace.Completion` to `KernelRKHSQuotient K` to obtain a
`CompleteSpace` and hence a Hilbert space. That stage is left to the
companion module
`LTFP.MathlibExt.Analysis.InnerProductSpace.AronszajnHilbert` (Phase
3a-2). The infrastructure exposed here — type synonym,
`PreInnerProductSpace.Core`, separation quotient, inherited
`NormedAddCommGroup` and `InnerProductSpace`, quotient feature map,
and quotient reproducing identity — is everything that stage needs to
consume from Stage 2. -/

end LTFP.MathlibExt.Analysis
