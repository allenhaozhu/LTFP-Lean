import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Classical
open scoped NNReal ENNReal

lemma coveringNumber_exists {X : Type*} {A : Set X} [PseudoMetricSpace X] (ha : TotallyBounded A) {ε : ℝ} (εpos: ε > 0):
  ∃ n : Nat, ∃ t : Finset X, t.card = n ∧ A ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  have hh : ∀ d ∈ uniformity X, ∃ (t : Set X), t.Finite ∧ A ⊆ ⋃ y ∈ t, {x : X | (x, y) ∈ d} := ha
  have hball := Metric.finite_approx_of_totallyBounded ha ε εpos
  have ⟨t, ⟨ht, tfin, tball⟩⟩  := hball
  have : Fintype t := tfin.fintype
  let n : Nat := this.card
  exists n
  exists t.toFinset
  constructor
  · exact Set.toFinset_card t
  · convert tball
    ext _
    simp only [Set.mem_toFinset]

noncomputable def coveringNumber {X : Type*} [PseudoMetricSpace X] {A : Set X} (ha : TotallyBounded A) (ε : ℝ): ℕ :=
  if h : ε > 0 then
    Nat.find (coveringNumber_exists ha h)
  else 0

theorem coveringNumber_eq {X : Type*} [PseudoMetricSpace X] {A : Set X} (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
  coveringNumber ha ε = Nat.find (coveringNumber_exists ha hε) := dif_pos hε

theorem converingNumber_antitone {X : Type*} [PseudoMetricSpace X] {A : Set X} (ha : TotallyBounded A) :
  AntitoneOn (coveringNumber ha) (Set.Ioi 0) := by
  intro ε₁ hε₁ ε₂ hε₂ hε₁ε₂
  rw [coveringNumber_eq ha hε₁, coveringNumber_eq ha hε₂]
  apply Nat.find_mono
  intro n ⟨t, ht₁, ht₂⟩
  exists t, ht₁
  apply ht₂.trans
  apply Set.iUnion_mono
  intro _
  apply Set.iUnion_mono
  intro _
  exact Metric.ball_subset_ball hε₁ε₂

theorem coveringNumber_nonzero {X : Type*} [PseudoMetricSpace X] {A : Set X} (hs : A.Nonempty) (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    0 < coveringNumber ha ε := by
  dsimp [coveringNumber]
  simp [hε]
  exact Set.nonempty_iff_ne_empty.mp hs

theorem converingNumber_aemeasurable {X : Type*} [PseudoMetricSpace X] {A : Set X} (ha : TotallyBounded A) :
  AEMeasurable (coveringNumber ha) MeasureTheory.volume := by
  have h₀ : AEMeasurable (coveringNumber ha) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (converingNumber_antitone ha)
  convert (aemeasurable_indicator_iff measurableSet_Ioi).mpr h₀
  ext ε
  if h : ε ∈ Set.Ioi 0 then
    rw [Set.indicator_of_mem h]
  else
    rw [Set.indicator_of_notMem h]
    rw [coveringNumber, dif_neg (by exact h)]

noncomputable def coveringFinset
  {X : Type*} [PseudoMetricSpace X] {A : Set X}
  (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) : Finset X :=
  Classical.choose (Nat.find_spec (coveringNumber_exists (X:=X) (A:=A) ha hε))

lemma coveringFinset_cover
  {X : Type*} [PseudoMetricSpace X] {A : Set X}
  (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
  A ⊆ ⋃ y ∈ coveringFinset ha hε, Metric.ball y ε := by
  simpa [coveringFinset, coveringNumber_exists] using
    (Classical.choose_spec (Nat.find_spec (coveringNumber_exists (X:=X) (A:=A) ha hε))).2

lemma coveringFinset_card
  {X : Type*} [PseudoMetricSpace X] {A : Set X}
  (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
  (coveringFinset ha hε).card = coveringNumber ha ε := by
  have h :=
    (Classical.choose_spec (Nat.find_spec (coveringNumber_exists (X:=X) (A:=A) ha hε))).1
  simpa [coveringFinset, coveringNumber_eq (X:=X) (A:=A) ha hε, coveringNumber_exists] using h

/-!
### Lipschitz-image-of-cover bridge

If `f : X → Y` is `L`-Lipschitz and a finset `C` covers `A` at scale `ε`,
then `f '' C` covers `f '' A` at scale `L * ε`. This bounds the covering
number of the image by the covering number of the source, which feeds the
Dudley entropy integral for the wide-network risk class (PROGRESS.md §35).
-/

/-- Pointwise image-of-cover step: if `f` is `L`-Lipschitz with `L ≠ 0` and
`C` covers `A` by open `ε`-balls, then `C.image f` covers `f '' A` by open
`(L * ε)`-balls. -/
private lemma image_cover_of_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {A : Set X} {C : Finset X} {f : X → Y} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : L ≠ 0) {ε : ℝ}
    (hcov : A ⊆ ⋃ y ∈ C, Metric.ball y ε) :
    f '' A ⊆ ⋃ y ∈ C.image f, Metric.ball y ((L : ℝ) * ε) := by
  classical
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hxC : x ∈ ⋃ c ∈ C, Metric.ball c ε := hcov hxA
  rcases Set.mem_iUnion₂.mp hxC with ⟨c, hcC, hxc⟩
  have hxc' : dist x c < ε := by simpa [Metric.mem_ball] using hxc
  have hLip : dist (f x) (f c) < (L : ℝ) * ε :=
    hf.dist_lt_mul_of_lt hL hxc'
  refine Set.mem_iUnion₂.mpr ⟨f c, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨c, hcC, rfl⟩
  · simpa [Metric.mem_ball] using hLip

/-- Lipschitz image of a cover: if `f` is `L`-Lipschitz, then the covering
number of `f '' A` at scale `L * ε` is at most the covering number of `A`
at scale `ε`. -/
theorem coveringNumber_image_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {A : Set X} (ha : TotallyBounded A)
    {f : X → Y} {L : ℝ≥0} (hf : LipschitzWith L f)
    {ε : ℝ} (hε : 0 < ε) :
    coveringNumber (ha.image hf.uniformContinuous) ((L : ℝ) * ε)
      ≤ coveringNumber ha ε := by
  classical
  by_cases hL : L = 0
  · -- Degenerate case: `L = 0`, hence `L * ε = 0`, and the LHS is `0`.
    have hLε : ¬ ((L : ℝ) * ε > 0) := by
      simp [hL]
    simp [coveringNumber, hLε]
  · -- Main case: `L > 0`, so `L * ε > 0` and the open-ball scaling
    -- is non-degenerate.
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      have hpos : (0 : ℝ≥0) < L := lt_of_le_of_ne (zero_le _) (Ne.symm hL)
      exact_mod_cast hpos
    have hLεpos : 0 < (L : ℝ) * ε := mul_pos hLpos hε
    -- Image of the optimal source cover is a cover of `f '' A` at scale `L * ε`.
    have hcov :
        f '' A ⊆ ⋃ y ∈ (coveringFinset ha hε).image f,
                   Metric.ball y ((L : ℝ) * ε) :=
      image_cover_of_lipschitz hf hL (coveringFinset_cover ha hε)
    -- Use `n := card of image finset` as the existential witness.
    set n : ℕ := ((coveringFinset ha hε).image f).card
    have hwitness :
        ∃ t : Finset Y, t.card = n ∧
          f '' A ⊆ ⋃ y ∈ t, Metric.ball y ((L : ℝ) * ε) :=
      ⟨(coveringFinset ha hε).image f, rfl, hcov⟩
    have hcard_le : n ≤ coveringNumber ha ε := by
      have h₁ : n ≤ (coveringFinset ha hε).card := Finset.card_image_le
      simpa [coveringFinset_card] using h₁
    have hfind :
        Nat.find (coveringNumber_exists (ha.image hf.uniformContinuous) hLεpos) ≤ n :=
      Nat.find_min'
        (coveringNumber_exists (ha.image hf.uniformContinuous) hLεpos) hwitness
    calc coveringNumber (ha.image hf.uniformContinuous) ((L : ℝ) * ε)
        = Nat.find (coveringNumber_exists (ha.image hf.uniformContinuous) hLεpos) :=
          coveringNumber_eq (ha.image hf.uniformContinuous) hLεpos
      _ ≤ n := hfind
      _ ≤ coveringNumber ha ε := hcard_le

/-!
### Doubling under negation-closure (and more generally, double covers)

If `B ⊆ Y` is covered by the images of two isometric embeddings
`e₀, e₁ : X → Y` of a totally-bounded `A ⊆ X`, then the covering number of
`B` at scale `ε` is at most `2 * coveringNumber ha ε`. The motivating use
case is `Y = EmpiricalFunctionSpace (negDoubleFamily F) S`,
`X = EmpiricalFunctionSpace F S`, with `e₀ q = ⟨(0, q.index)⟩` (the
positive copy) and `e₁ q = ⟨(1, q.index)⟩` (the negated copy); negation
is an isometry in the empirical-L² pseudometric since
`empiricalNorm S (-(f - g)) = empiricalNorm S (f - g)`. Combined with
`empiricalRademacherComplexity_eq_without_abs_negDoubleFamily`
(`Rademacher.lean`, commit `1d71e7e`) and `dudley_entropy_integral'`,
this delivers the with-abs Dudley analogue.
-/

/-- **Covering-number doubling under a two-fold isometric cover.**

If `B ⊆ e₀ '' A ∪ e₁ '' A` with both `e₀` and `e₁` isometries of `A`,
then the covering number of `B` at scale `ε` is at most twice the
covering number of `A` at scale `ε`. The cover is built by taking the
finset `C.image e₀ ∪ C.image e₁` where `C` is the optimal `A`-cover. -/
theorem coveringNumber_le_two_mul_of_isometric_double_cover
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {A : Set X} (ha : TotallyBounded A)
    {B : Set Y} (hb : TotallyBounded B)
    {e₀ e₁ : X → Y} (he₀ : Isometry e₀) (he₁ : Isometry e₁)
    (hcov : B ⊆ e₀ '' A ∪ e₁ '' A) {ε : ℝ} (hε : 0 < ε) :
    coveringNumber hb ε ≤ 2 * coveringNumber ha ε := by
  classical
  set C : Finset X := coveringFinset ha hε with hC_def
  -- The doubled cover in `Y`.
  set D : Finset Y := C.image e₀ ∪ C.image e₁ with hD_def
  -- Cardinality bound: `|D| ≤ 2 * coveringNumber ha ε`.
  have hcard : D.card ≤ 2 * coveringNumber ha ε := by
    have hunion : D.card ≤ (C.image e₀).card + (C.image e₁).card :=
      Finset.card_union_le _ _
    have h₀ : (C.image e₀).card ≤ C.card := Finset.card_image_le
    have h₁ : (C.image e₁).card ≤ C.card := Finset.card_image_le
    have hC_card : C.card = coveringNumber ha ε := coveringFinset_card ha hε
    calc
      D.card ≤ (C.image e₀).card + (C.image e₁).card := hunion
      _ ≤ C.card + C.card := Nat.add_le_add h₀ h₁
      _ = 2 * C.card := by ring
      _ = 2 * coveringNumber ha ε := by rw [hC_card]
  -- Cover property: every point of `B` is within `ε` of some `d ∈ D`.
  have hAcov : A ⊆ ⋃ c ∈ C, Metric.ball c ε := coveringFinset_cover ha hε
  have hDcov : B ⊆ ⋃ d ∈ D, Metric.ball d ε := by
    intro y hyB
    rcases hcov hyB with ⟨x, hxA, rfl⟩ | ⟨x, hxA, rfl⟩
    · -- `y = e₀ x`. Pick `c ∈ C` with `dist x c < ε`, then `e₀ c ∈ D`
      -- satisfies `dist (e₀ x) (e₀ c) = dist x c < ε`.
      rcases Set.mem_iUnion₂.mp (hAcov hxA) with ⟨c, hcC, hxc⟩
      have hxc' : dist x c < ε := by simpa [Metric.mem_ball] using hxc
      have hiso : dist (e₀ x) (e₀ c) = dist x c := he₀.dist_eq x c
      refine Set.mem_iUnion₂.mpr ⟨e₀ c, ?_, ?_⟩
      · -- `e₀ c ∈ D`
        have : e₀ c ∈ C.image e₀ := Finset.mem_image.mpr ⟨c, hcC, rfl⟩
        exact Finset.mem_union.mpr (Or.inl this)
      · simpa [Metric.mem_ball, hiso] using hxc'
    · -- Symmetric case for `e₁`.
      rcases Set.mem_iUnion₂.mp (hAcov hxA) with ⟨c, hcC, hxc⟩
      have hxc' : dist x c < ε := by simpa [Metric.mem_ball] using hxc
      have hiso : dist (e₁ x) (e₁ c) = dist x c := he₁.dist_eq x c
      refine Set.mem_iUnion₂.mpr ⟨e₁ c, ?_, ?_⟩
      · have : e₁ c ∈ C.image e₁ := Finset.mem_image.mpr ⟨c, hcC, rfl⟩
        exact Finset.mem_union.mpr (Or.inr this)
      · simpa [Metric.mem_ball, hiso] using hxc'
  -- Witness for `coveringNumber_exists` at scale `ε`.
  have hwitness :
      ∃ t : Finset Y, t.card = D.card ∧ B ⊆ ⋃ y ∈ t, Metric.ball y ε :=
    ⟨D, rfl, hDcov⟩
  have hfind :
      Nat.find (coveringNumber_exists hb hε) ≤ D.card :=
    Nat.find_min' (coveringNumber_exists hb hε) hwitness
  calc coveringNumber hb ε
      = Nat.find (coveringNumber_exists hb hε) := coveringNumber_eq hb hε
    _ ≤ D.card := hfind
    _ ≤ 2 * coveringNumber ha ε := hcard

/-!
### Internal-vs-external covering-number bridge

LTFP's internal `coveringNumber ha ε : ℕ` is defined via open `ε`-balls
with centers in the ambient pseudometric space (not required to lie in
`A`). Mathlib's `Metric.externalCoveringNumber ε A : ℕ∞` is the
infimum cardinality of a `closedBall ε`-cover of `A` with centers in
the ambient space. Since `closedBall x ε ⊆ ball x (2 * ε)` whenever
`ε > 0`, any finite external `ε`-cover (closed balls) is also a finite
open `(2 * ε)`-cover, hence:

  `(coveringNumber ha (2 * ε) : ℕ∞) ≤ Metric.externalCoveringNumber ε A`.

This bridge allows substituting the explicit Euclidean covering count
`(⌈2 * √d * B / δ⌉₊ + 1) ^ d` (proved for `externalCoveringNumber` in
`LTFP/MathlibExt/Probability/CoveringNumberEuclidean.lean`) into the
endpoint Dudley integrand (which uses LTFP's internal `coveringNumber`).
-/

/-- **Internal-vs-external covering-number bridge.**

LTFP's `coveringNumber` at scale `2 * ε` is bounded by Mathlib's
`externalCoveringNumber` at scale `ε`. The factor of two comes from
the `closedBall x ε ⊆ ball x (2 * ε)` inclusion (LTFP uses open balls;
Mathlib's `IsCover` uses closed balls). -/
theorem coveringNumber_le_externalCoveringNumber
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ≥0} (hε : 0 < ε) :
    (coveringNumber ha (2 * (ε : ℝ)) : ℕ∞)
      ≤ Metric.externalCoveringNumber ε A := by
  classical
  have hε_real : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have h2ε_pos : (0 : ℝ) < 2 * (ε : ℝ) := by linarith
  -- Reduce to: for every external cover `C`, LTFP.coveringNumber ≤ |C|.
  refine le_iInf₂ (fun C hC => ?_)
  -- Case on whether `C` is finite or infinite.
  by_cases hCfin : C.Finite
  · -- Finite case: build a `Finset` witness and apply `Nat.find_min'`.
    set t : Finset X := hCfin.toFinset with ht_def
    -- The external cover `C` is a `closedBall ε`-cover; inflate to open
    -- `(2 * ε)`-balls via `closedBall x ε ⊆ ball x (2 * ε)`.
    have hclosedSub :
        ∀ y : X, Metric.closedBall y (ε : ℝ) ⊆ Metric.ball y (2 * (ε : ℝ)) := by
      intro y
      apply Metric.closedBall_subset_ball
      linarith
    -- Extract the closed-ball-cover form of `IsCover`.
    have hC_cb : A ⊆ ⋃ y ∈ C, Metric.closedBall y (ε : ℝ) := by
      have := hC.subset_iUnion_closedBall
      simpa using this
    -- Translate to an open `(2 * ε)`-ball cover with centers in `t`.
    have hCover : A ⊆ ⋃ y ∈ t, Metric.ball y (2 * (ε : ℝ)) := by
      intro x hxA
      rcases Set.mem_iUnion₂.mp (hC_cb hxA) with ⟨y, hyC, hxy⟩
      refine Set.mem_iUnion₂.mpr ⟨y, ?_, ?_⟩
      · exact hCfin.mem_toFinset.mpr hyC
      · exact hclosedSub y hxy
    -- Witness for `coveringNumber_exists` at scale `2 * ε`.
    have hwitness :
        ∃ s : Finset X, s.card = t.card ∧
          A ⊆ ⋃ y ∈ s, Metric.ball y (2 * (ε : ℝ)) :=
      ⟨t, rfl, hCover⟩
    -- `coveringNumber ha (2 * ε)` is the `Nat.find` of the existential.
    have hfind :
        Nat.find (coveringNumber_exists ha h2ε_pos) ≤ t.card :=
      Nat.find_min' (coveringNumber_exists ha h2ε_pos) hwitness
    have hLTFP_le_card : coveringNumber ha (2 * (ε : ℝ)) ≤ t.card := by
      calc coveringNumber ha (2 * (ε : ℝ))
          = Nat.find (coveringNumber_exists ha h2ε_pos) :=
            coveringNumber_eq ha h2ε_pos
        _ ≤ t.card := hfind
    -- Convert the `ℕ`-bound to an `ℕ∞`-bound and identify `t.card` with `C.encard`.
    have ht_card : (t.card : ℕ∞) = C.encard := by
      have h₁ : C.encard = t.card := by
        simp [ht_def, hCfin.encard_eq_coe_toFinset_card]
      exact h₁.symm
    have : (coveringNumber ha (2 * (ε : ℝ)) : ℕ∞) ≤ (t.card : ℕ∞) := by
      exact_mod_cast hLTFP_le_card
    exact this.trans ht_card.le
  · -- Infinite case: `C.encard = ⊤`, so the bound is vacuous.
    have hCinf : C.Infinite := hCfin
    simp [hCinf.encard_eq]
