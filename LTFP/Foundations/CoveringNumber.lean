import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Classical
open scoped NNReal

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
