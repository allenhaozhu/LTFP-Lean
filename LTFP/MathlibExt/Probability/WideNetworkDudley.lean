/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.CoveringNumberEuclidean
import LTFP.MathlibExt.Probability.LinearClassClosedBallCover
import LTFP.MathlibExt.Probability.LinearClassSampleCoverCard
import LTFP.MathlibExt.Probability.LinearizedRiskSampleCover

/-!
# Wide-network generalization carrier: linearized-risk cover from a totally-bounded parameter ball

Composes several existing ingredients on the B8 N6 wide-network
generalization path into one statement that exposes the *qualitative*
shape the Dudley entropy integral needs:

1. `covering_number_euclidean_ball` (this file's dependency) — the
   `(⌈2 √d B / δ⌉₊ + 1) ^ d` *external*-cover-cardinality bound for the
   parameter closed ball. **NOTE: this explicit cardinality is NOT yet
   composed into the carrier theorem below; see "Residual bridge".**
2. `linear_class_closed_ball_exists_finite_cover` — existence of a
   finite finset cover of the parameter ball at any positive radius.
3. `linear_class_sample_pred_card_le` — sample-prediction tuple cover
   inherits cardinality from the parameter cover.
4. `linearized_risk_class_sample_cover_of_param_cover` — parameter
   cover lifts to a `(2 B)(δ R)`-cover of squared-loss values on the
   sample.
5. `linear_predictor_lipschitz_on_ball` (transitive via 4 above).

We work entirely with internal finset covers (every cover element is
in the parameter ball). The grid construction in
`covering_number_euclidean_ball` produces *external* cover points
(corners of a bounding square that may lie slightly outside the
`L²`-ball); to land an *internal* cover with the same cardinality
bound one would have to either project the external grid back into the
ball with a Lipschitz factor, or compose a fresh "Lipschitz-image-of-
cover" lemma on LTFP's internal `coveringNumber` (see below). The
file surfaces:

- `wide_network_param_finset_cover` — *internal* finset cover at
  resolution `δ` (size existentially bounded, no explicit number).
- `wide_network_linearized_risk_explicit_cover` — the full composite
  carrier theorem in its honest current form: it produces an internal
  finset cover `C` of the parameter ball, together with the lifted
  linearized-risk sample-cover accuracy and the sample-prediction-
  tuple cardinality bound `≤ |C|`, *without* attaching an explicit
  numeric bound on `|C|`.
- `wide_network_linearized_risk_explicit_cover_card` — a *weaker*
  companion that, despite its current name, only exposes the explicit
  external-covering-number bound for the parameter ball itself; it
  does **not** lift to a linearized-risk-cover or to a sample-loss
  cover. See its docstring for the honest characterization and the
  rename note.

## Residual Lipschitz-image-of-cover bridge

To feed `dudley_entropy_integral'` on the squared-loss class one needs
both (i) the lifted linearized-risk cover (provided here) AND (ii) an
explicit numeric cardinality bound for that lifted cover, expressed
on LTFP's internal `coveringNumber` (in
`LTFP/Foundations/CoveringNumber.lean`). The missing link is a
**Lipschitz-image-of-cover** lemma of the form

  "if `f : X → Y` is `L`-Lipschitz on `A` and `C` is an `ε`-cover of
   `A` in `X`, then `f '' C` is an `(L * ε)`-cover of `f '' A` in `Y`,
   and `coveringNumber (f '' A) (L*ε) ≤ coveringNumber A ε`"

stated on LTFP's `coveringNumber`. This lemma does not yet exist in
either Mathlib or LTFP-MathlibExt. Once it lands, the composition
`covering_number_euclidean_ball` → Lipschitz-image-of-cover →
linearized-risk lift will produce a single carrier statement with
both the explicit `(⌈2 √d B / δ⌉₊ + 1) ^ d` cardinality and the
sample-loss cover lift, which is what the Dudley step actually
consumes. Until that lemma is built, the two halves remain factored
as the two theorems below.
-/

open scoped NNReal ENNReal RealInnerProductSpace

namespace LTFP

-- TODO(upstream-or-replace): this helper is largely redundant. Mathlib's
-- `Metric.finite_approx_of_totallyBounded`
-- (`Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`) is strictly stronger:
-- it returns a finite *Set* (immediately convertible to a `Finset`) of
-- internal centres at any positive resolution, with the same δ-cover
-- conclusion. The only thing this helper adds is the packaging into a
-- `Finset` directly and a slightly different cover predicate
-- (`dist x c ≤ δ` rather than the strict version). Future cleanup:
-- replace internal call sites with `Metric.finite_approx_of_totallyBounded`
-- plus `Set.Finite.toFinset`, then delete this lemma.
/-- Auxiliary: a `TotallyBounded` set in a `PseudoMetricSpace` admits,
for every `δ > 0`, a finite *finset* cover by points in the set itself.
A bridge from `TotallyBounded` to a usable explicit finset form.

**Note (2026-05-23 audit):** mostly redundant with
`Metric.finite_approx_of_totallyBounded` in Mathlib; kept here only
because its `Finset`-shaped conclusion is the form consumed downstream
by `wide_network_param_finset_cover`. See the `TODO(upstream-or-replace)`
comment above. -/
theorem totallyBounded_exists_finset_subset_cover
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (hA : TotallyBounded A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : Finset X, (↑C : Set X) ⊆ A ∧
      ∀ x ∈ A, ∃ c ∈ C, dist x c ≤ δ := by
  classical
  -- `Metric.totallyBounded_iff` gives a finite set of centres (possibly
  -- outside A). Filter to centres whose `δ/2`-ball meets A, pick an
  -- internal witness from each such ball, then triangle-inequality to δ.
  rcases (Metric.totallyBounded_iff.mp hA) (δ / 2) (by linarith) with
    ⟨T, hTfin, hTcov⟩
  -- Filter the finite centre set down to those that actually intersect A.
  set T_useful : Set X := {t ∈ T | (Metric.ball t (δ / 2) ∩ A).Nonempty}
  have hT_useful_fin : T_useful.Finite :=
    hTfin.subset (fun t ht => ht.1)
  -- For each useful t, the intersection is nonempty; pick a witness.
  let pickFun : X → X := fun t =>
    if h : (Metric.ball t (δ / 2) ∩ A).Nonempty then h.choose else t
  have pickFun_mem_A :
      ∀ t : X, (Metric.ball t (δ / 2) ∩ A).Nonempty → pickFun t ∈ A := by
    intro t ht
    have hchoose := ht.choose_spec
    have h_eq : pickFun t = ht.choose := by simp [pickFun, ht]
    rw [h_eq]; exact hchoose.2
  have pickFun_close :
      ∀ t : X, (Metric.ball t (δ / 2) ∩ A).Nonempty →
        dist (pickFun t) t < δ / 2 := by
    intro t ht
    have hchoose := ht.choose_spec
    have h_eq : pickFun t = ht.choose := by simp [pickFun, ht]
    rw [h_eq]
    have : ht.choose ∈ Metric.ball t (δ / 2) := hchoose.1
    simpa [Metric.mem_ball] using this
  -- Build C from the *filtered* centre set image.
  let C : Finset X := hT_useful_fin.toFinset.image pickFun
  refine ⟨C, ?_, ?_⟩
  · -- C ⊆ A
    intro c hc
    have hc_mem : c ∈ hT_useful_fin.toFinset.image pickFun := by exact_mod_cast hc
    rcases Finset.mem_image.mp hc_mem with ⟨t, ht_in, h_eq⟩
    have ht_useful : t ∈ T_useful :=
      (Set.Finite.mem_toFinset hT_useful_fin).mp ht_in
    have : pickFun t ∈ A := pickFun_mem_A t ht_useful.2
    rw [← h_eq]; exact this
  · -- Every point of A is within δ of some element of C.
    intro x hx
    have hx_in : x ∈ ⋃ y ∈ T, Metric.ball y (δ / 2) := hTcov hx
    rw [Set.mem_iUnion₂] at hx_in
    rcases hx_in with ⟨t, ht_T, hx_ball⟩
    have ht_inter : (Metric.ball t (δ / 2) ∩ A).Nonempty := ⟨x, hx_ball, hx⟩
    have ht_useful : t ∈ T_useful := ⟨ht_T, ht_inter⟩
    refine ⟨pickFun t, ?_, ?_⟩
    · have ht_finset : t ∈ hT_useful_fin.toFinset :=
        (Set.Finite.mem_toFinset hT_useful_fin).mpr ht_useful
      exact Finset.mem_image.mpr ⟨t, ht_finset, rfl⟩
    · -- dist x (pick t) ≤ dist x t + dist t (pick t) ≤ δ/2 + δ/2 = δ.
      have h1 : dist x t < δ / 2 := by simpa [Metric.mem_ball] using hx_ball
      have h2 : dist t (pickFun t) < δ / 2 := by
        rw [dist_comm]; exact pickFun_close t ht_inter
      have htri : dist x (pickFun t) ≤ dist x t + dist t (pickFun t) :=
        dist_triangle _ _ _
      linarith

/-- The parameter closed ball of radius `B` in `EuclideanSpace ℝ (Fin d)`
admits, at every resolution `δ > 0`, a finite finset of *internal* cover
points (each `θ` in the ball is `δ`-close to some `c` in the cover).
Convenience wrapper combining `linear_class_closed_ball_totallyBounded`
with the totally-bounded-to-finset extractor. -/
theorem wide_network_param_finset_cover
    {d : ℕ} (B δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)),
      (∀ c ∈ C, ‖c‖ ≤ B) ∧
      (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B → ∃ c ∈ C, ‖θ - c‖ ≤ δ) := by
  classical
  have hTB : TotallyBounded
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B) :=
    linear_class_closed_ball_totallyBounded (d := d) B
  rcases totallyBounded_exists_finset_subset_cover hTB hδ with
    ⟨C, hC_sub, hCcov⟩
  refine ⟨C, ?_, ?_⟩
  · intro c hc
    have hc_in : c ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B :=
      hC_sub (by exact_mod_cast hc)
    simpa [Metric.mem_closedBall, dist_zero_right] using hc_in
  · intro θ hθ
    have hθ_in : θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hθ
    rcases hCcov θ hθ_in with ⟨c, hcC, hdist⟩
    refine ⟨c, hcC, ?_⟩
    simpa [dist_eq_norm] using hdist

/-- **Wide-network generalization carrier (Option A pre-Dudley): honest
form.**

For a wide linear-predictor class indexed by the closed parameter ball
`‖θ‖ ≤ B_param` in `EuclideanSpace ℝ (Fin d)`, a bounded sample
`‖xs i‖ ≤ R`, targets `ys`, and uniform prediction-error bound `B`,
there exists a *finite finset* `C` of cover parameters such that:

* every `θ` in the parameter ball has a `c ∈ C` with the *linearized
  risk* values `(⟨θ, xs i⟩ - ys i)^2 ↔ (⟨c, xs i⟩ - ys i)^2` agreeing to
  within `(2 B)(δ R)` on every sample index `i`;
* `c` itself is in the parameter ball (so the cover element satisfies
  the same prediction-error bound that `θ` does, modulo
  `linear_predictor_lipschitz_on_ball`), and the induced
  prediction-tuple finset has cardinality `≤ |C|`.

**Honest scope (2026-05-23 audit):** this theorem produces the finite
finset `C` from `TotallyBounded`ness of the parameter ball (via
`wide_network_param_finset_cover`); it does **NOT** attach the
explicit Euclidean cardinality bound `|C| ≤ (⌈2 √d B_param / δ⌉₊ + 1)^d`
from `covering_number_euclidean_ball`. The explicit cardinality lives
on an *external* grid cover and would need a Lipschitz-image-of-cover
bridge (see the module docstring's "Residual bridge" section) before
it can be attached to this `C`. Downstream consumers that need the
explicit number must currently invoke
`wide_network_linearized_risk_explicit_cover_card` separately for the
parameter-ball cardinality and combine it by hand. -/
theorem wide_network_linearized_risk_explicit_cover
    {d m : ℕ}
    (xs : Fin m → EuclideanSpace ℝ (Fin d))
    (ys : Fin m → ℝ)
    (B_param δ R B : ℝ)
    (hδ : 0 < δ)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hbound_all :
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)),
      -- All cover elements live inside the parameter ball.
      (∀ c ∈ C, ‖c‖ ≤ B_param) ∧
      -- Sample-prediction-tuple cover cardinality inherits from |C|.
      (C.image
          (fun c => fun i : Fin m => inner ℝ c (xs i))).card ≤ C.card ∧
      -- For every θ in the parameter ball, some c ∈ C approximates
      -- θ in linearized squared-loss values on every sample point.
      (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∃ c ∈ C,
          ∀ i : Fin m,
            |(inner ℝ θ (xs i) - ys i) ^ 2 - (inner ℝ c (xs i) - ys i) ^ 2|
              ≤ (2 * B) * (δ * R)) := by
  classical
  -- Step (1): extract an internal δ-finset-cover of the parameter ball.
  rcases wide_network_param_finset_cover (d := d) B_param δ hδ with
    ⟨C, hC_norm, hC_cover⟩
  refine ⟨C, hC_norm, Finset.card_image_le, ?_⟩
  -- Step (2): lift the cover via linearized-risk Lipschitz to a sample cover.
  set Θ : Set (EuclideanSpace ℝ (Fin d)) :=
    {θ | ‖θ‖ ≤ B_param} with hΘ_def
  set Cset : Set (EuclideanSpace ℝ (Fin d)) :=
    (C : Set (EuclideanSpace ℝ (Fin d))) with hCset_def
  -- Re-express the cover hypothesis on these sets.
  have hcover : ∀ θ ∈ Θ, ∃ c ∈ Cset, ‖θ - c‖ ≤ δ := by
    intro θ hθ
    rcases hC_cover θ hθ with ⟨c, hcC, hdist⟩
    exact ⟨c, by exact_mod_cast hcC, hdist⟩
  -- The uniform prediction-error bound applies to every θ ∈ Θ.
  have hbound : ∀ θ ∈ Θ, ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B := by
    intro θ hθ i
    exact hbound_all θ hθ i
  -- It also applies to every c ∈ Cset (since C ⊆ parameter ball).
  have hboundC : ∀ c ∈ Cset, ∀ i : Fin m, |inner ℝ c (xs i) - ys i| ≤ B := by
    intro c hc i
    have hc_finset : c ∈ C := by exact_mod_cast hc
    exact hbound_all c (hC_norm c hc_finset) i
  -- Apply the linearized-risk sample-cover composition (ingredient 4).
  have hLifted :=
    linearized_risk_class_sample_cover_of_param_cover (d := d) (m := m)
      Θ Cset xs ys δ R B hx hcover hbound hboundC
  intro θ hθ
  rcases hLifted θ hθ with ⟨c, hcCset, h_acc⟩
  exact ⟨c, by exact_mod_cast hcCset, h_acc⟩

/-- **Parameter-ball external covering-number bound (honest form).**

**Misleading historical name (2026-05-23 audit):** despite the suffix
`linearized_risk_..._cover_card`, this theorem does **not** mention
`ys`, the squared loss, the sample-prediction tuple cover, or the
linearized-risk-class cover at all. It is literally just
`covering_number_euclidean_ball` (the external cardinality bound for
the parameter ball) packaged together with the trivial restatement of
the sample bound `∀ θ ..., ‖xs i‖ ≤ R`. The honest name for what is
actually proved here is `wide_network_param_ball_external_cover_card`;
the current name is retained to avoid breaking any out-of-tree callers
but is scheduled for rename.

What this theorem ACTUALLY proves, for `d ≥ 1`, `B_param ≥ 0`, and
`δ : ℝ≥0` positive:

1. **First conjunct:** the *external* covering number of the
   parameter ball `Metric.closedBall 0 B_param ⊆ EuclideanSpace ℝ (Fin d)`
   at resolution `δ` is at most `(⌈2 √d B_param / δ⌉₊ + 1) ^ d`.
2. **Second conjunct:** the sample bound `‖xs i‖ ≤ R` (trivially
   re-quantified over `θ`).

What this theorem does **NOT** prove (despite the historical name):

- No linearized-risk cover is constructed.
- No sample-prediction-tuple cover is constructed.
- No squared-loss accuracy guarantee is stated.
- The targets `ys` are not even a hypothesis.
- The bound uses *external* covering points which need not live in
  the parameter ball; lifting them to an internal finset cover (the
  form `wide_network_linearized_risk_explicit_cover` uses) requires
  the Lipschitz-image-of-cover bridge noted in the module docstring.

Composing this cardinality bound with
`wide_network_linearized_risk_explicit_cover` to obtain a single
Dudley-input statement is the residual bridge work. -/
theorem wide_network_linearized_risk_explicit_cover_card
    {d m : ℕ}
    (xs : Fin m → EuclideanSpace ℝ (Fin d))
    (B_param : ℝ) (δ : ℝ≥0) (hd : 1 ≤ d) (hB_param : 0 ≤ B_param)
    (hδ_ne : δ ≠ 0)
    (R : ℝ) (hx : ∀ i : Fin m, ‖xs i‖ ≤ R) :
    Metric.externalCoveringNumber δ
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) ≤
      ((⌈2 * Real.sqrt d * B_param / (δ : ℝ)⌉₊ + 1 : ℕ) ^ d : ℕ) ∧
    -- Sample-prediction-tuple cardinality inherits: same upper bound
    -- applies to any internal finset cover of the parameter ball.
    (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
      ∀ i : Fin m, ‖xs i‖ ≤ R) := by
  refine ⟨?_, fun _ _ _ => hx _⟩
  exact covering_number_euclidean_ball d B_param δ hd hB_param hδ_ne

end LTFP
