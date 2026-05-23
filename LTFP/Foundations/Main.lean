import LTFP.Foundations.Rademacher
import LTFP.Foundations.McDiarmid
import LTFP.Foundations.BoundedDifference
import LTFP.Foundations.SeparableSpaceSup
import LTFP.Foundations.LinearPredictorL2
import LTFP.Foundations.LinearPredictorL1
import LTFP.Foundations.DudleyEntropy

section

universe u v w

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type w}
variable {μ : Measure Ω} {f : ι → 𝒳 → ℝ}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/-- The expected empirical uniform deviation is bounded by twice the Rademacher complexity. -/
theorem uniform_deviation_expectation_le_two_smul_rademacher_complexity
    [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (hn : 0 < n) (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b) :
    μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤ 2 • rademacherComplexity n f μ X := by
  apply le_of_mul_le_mul_left _ (Nat.cast_pos.mpr hn)
  convert expectation_le_rademacher (μ := μ) (n := n) hf hb hf' using 1
  · rw [← integral_const_mul]
    apply integral_congr_ae (Filter.EventuallyEq.of_eq _)
    ext ω
    rw [uniformDeviation, Real.mul_iSup_of_nonneg (by norm_num)]
    apply congr_arg _ (funext (fun i ↦ ?_))
    rw [← show |(n : ℝ)| = n from abs_of_nonneg (by norm_num), ← abs_mul]
    apply congr_arg
    simp only [Nat.abs_cast, Function.comp_apply, nsmul_eq_mul]
    field_simp
  · ring

/-- McDiarmid tail bound for the centered empirical uniform deviation. -/
theorem uniform_deviation_mcdiarmid_tail
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    {X : Ω → 𝒳} (hX : Measurable X)
    (hf : ∀ i, Measurable (f i))
    {b : ℝ} (hb : 0 ≤ b) (hf': ∀ i x, |f i x| ≤ b)
    {t : ℝ} (ht' : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω) -
      μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≥ ε)).toReal ≤
        (- ε ^ 2 * t * n).exp := by
  by_cases hn : n = 0
  · simpa [hn] using measureReal_le_one
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let c : Fin n → ℝ := fun i ↦ (n : ℝ)⁻¹ * 2 * b
  have ht' : (n : ℝ) * t / 2 * ∑ i, (c i) ^ 2 ≤ 1 := by
    apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 1 / 2 from by linarith)
    calc
      _ = t * b ^ 2 := by
        simp only [c, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      _ ≤ _ := by linarith
  have hfX : ∀ i, Measurable (f i ∘ X) := fun i => (hf i).comp hX
  calc
    _ ≤ (-2 * ε ^ 2 * (n * t / 2)).exp :=
      mcdiarmid_inequality_pos' hX (uniformDeviation_bounded_difference hn X hfX hb hf')
        (uniformDeviation_measurable X hf) hε ht'
    _ = _ := congr_arg _ (by ring)

/-- (Main Theorem) Countable-class tail bound via symmetrization and McDiarmid's inequality. -/
theorem uniform_deviation_tail_bound_countable
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    {t : ℝ} (ht' : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * t * n).exp := by
  by_cases hn : n = 0
  · simpa [hn] using measureReal_le_one
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  apply le_trans _ (uniform_deviation_mcdiarmid_tail (μ := μ) hX hf hb hf' ht' hε)
  simp only [ge_iff_le, ne_eq, measure_ne_top, not_false_eq_true, ENNReal.toReal_le_toReal]
  apply measure_mono
  intro ω h
  have : 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω) := h
  have : μⁿ[fun ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤ 2 • rademacherComplexity n f μ X :=
    uniform_deviation_expectation_le_two_smul_rademacher_complexity hn X (fun i ↦ (hf i).comp hX) hb hf'
  show ε ≤ uniformDeviation n f μ X (X ∘ ω) - μⁿ[fun ω ↦ uniformDeviation n f μ X (X ∘ ω)]
  linarith

/-- (Main Theorem) Optimized countable-class tail bound with `t = 1 / (2 * b^2)`. -/
theorem uniform_deviation_tail_bound_countable_of_pos
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * n / (2 * b ^ 2)).exp := by
  let t := 1 / (2 * b ^ 2)
  have ht : 0 ≤ t := div_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg b))
  have ht' : t * b ^ 2 ≤ 1 / 2 := le_of_eq (by dsimp only [t]; field_simp)
  calc
    _ ≤ (- ε ^ 2 * t * n).exp :=
      uniform_deviation_tail_bound_countable (μ := μ) f hf X hX (le_of_lt hb) hf' ht' hε
    _ = _ := by dsimp only [t]; field_simp

open TopologicalSpace

lemma empiricalRademacherComplexity_eq
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι]
    (n : ℕ) {f : ι → (𝒳 → ℝ)} (hf : ∀ x : 𝒳, Continuous fun i ↦ f i x) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n f S = empiricalRademacherComplexity n (f ∘ denseSeq ι) S := by
  dsimp [empiricalRademacherComplexity]
  congr
  ext i
  apply separableSpaceSup_eq_real
  continuity

lemma RademacherComplexity_eq
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι]
    (n : ℕ) (f : ι → (𝒳 → ℝ)) (hf : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    (μ : Measure Ω) (X : Ω → 𝒳) :
    rademacherComplexity n f μ X = rademacherComplexity n (f ∘ denseSeq ι) μ X := by
  dsimp [rademacherComplexity]
  congr
  ext i
  exact empiricalRademacherComplexity_eq n hf (X ∘ i)

lemma uniformDeviation_eq
    [MeasurableSpace 𝒳]
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    (n : ℕ) (f : ι → 𝒳 → ℝ)
    (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    uniformDeviation n f μ X = uniformDeviation n (f ∘ denseSeq ι) μ X := by
  ext y
  dsimp [uniformDeviation]
  apply separableSpaceSup_eq_real
  apply Continuous.abs
  apply Continuous.sub
  · continuity
  · have : ∀ (x : ι), ∀ᵐ (a : Ω) ∂μ, ‖f x (X a)‖ ≤ b := by
      intro i
      filter_upwards with ω
      exact hf' i (X ω)
    apply MeasureTheory.continuous_of_dominated _ this
    · apply MeasureTheory.integrable_const
    · filter_upwards with ω
      continuity
    · intro i
      apply Measurable.aestronglyMeasurable
      measurability

/-- (Main Theorem) Separable-class tail bound obtained via reduction to a countable dense subclass. -/
theorem uniform_deviation_tail_bound_separable
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι]  [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    {t : ℝ} (ht' : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * t * n).exp := by
  let f' := f ∘ denseSeq ι
  calc
    _ = (μⁿ (fun ω ↦ 2 • rademacherComplexity n f' μ X + ε ≤ uniformDeviation n f' μ X (X ∘ ω))).toReal := by
      congr
      ext ω
      rw [RademacherComplexity_eq n f hf'' μ X]
      rw [uniformDeviation_eq n f hf X hX hf' hf'' μ]
    _ ≤ (- ε ^ 2 * t * n).exp := by
      apply uniform_deviation_tail_bound_countable f' _ X hX hb _ ht' hε
      · intro i
        measurability
      · exact fun i x ↦ hf' (denseSeq ι i) x

/-- (Main Theorem) Optimized separable-class tail bound with `t = 1 / (2 * b^2)`. -/
theorem uniform_deviation_tail_bound_separable_of_pos
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * n / (2 * b ^ 2)).exp := by
  let t := 1 / (2 * b ^ 2)
  have ht : 0 ≤ t := div_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg b))
  have ht' : t * b ^ 2 ≤ 1 / 2 := le_of_eq (by dsimp only [t]; field_simp)
  calc
    _ ≤ (- ε ^ 2 * t * n).exp :=
      uniform_deviation_tail_bound_separable (μ := μ) f hf X hX (le_of_lt hb) hf' hf'' ht' hε
    _ = _ := by dsimp only [t]; field_simp

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Example: L2 linear predictor bound for empirical Rademacher complexity. -/
theorem linear_predictor_l2_bound
    [Nonempty ι]
    (d : ℕ)
    (W X : ℝ)
    (hx : 0 ≤ X) (hw : 0 ≤ W)
    (Y' : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (w' : ι → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W):
    empiricalRademacherComplexity
      n (fun (i : ι) a ↦ ⟪((Subtype.val ∘ w') i), a⟫) (Subtype.val ∘ Y') ≤
    X * W / √(n : ℝ) := by
  exact linear_predictor_l2_bound' (d := d) (n := n) (W := W) (X := X) hx hw Y' w'

/-- Example: L1/L∞ linear predictor bound for empirical Rademacher complexity. -/
theorem linear_predictor_l1_bound
    [Nonempty ι]
    (d : ℕ)
    (Xinf W : ℝ)
    (hX : 0 ≤ Xinf) (hW : 0 ≤ W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Y' : Fin n → LinftyBall (d := d) Xinf)
    (w' : ι → L1Ball (d := d) W) :
    empiricalRademacherComplexity n
      (fun i a => (∑ j : Fin d, (w' i).1 j * a j))
      (Subtype.val ∘ Y') ≤
      (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
  exact linear_predictor_l1_bound' (d := d) (n := n) (Xinf := Xinf) (W := W) hX hW d_pos n_pos Y' w'

/-- Dudley entropy integral upper bound for empirical Rademacher complexity. -/
theorem dudley_entropy_integral_bound
  {𝒳 : Type v} {n : ℕ} {ι : Type u} [Nonempty ι] {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳} {c ε : ℝ}
  (ε_pos : 0 < ε) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (m_pos : 0 < n) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c)
  (ε_le_c_div_2 : ε < c/2) :
    empiricalRademacherComplexity_without_abs n F S ≤
    (4 * ε + (12 / Real.sqrt n) *
    (∫ (x : ℝ) in ε..(c/2),√(Real.log (coveringNumber h' x)))) := by
  exact dudley_entropy_integral' ε_pos h' m_pos cs ε_le_c_div_2

/-- **With-abs Dudley entropy integral upper bound.**

Composes `empiricalRademacherComplexity_eq_without_abs_negDoubleFamily`
(Bartlett–Mendelson with-abs ↔ without-abs bridge) with
`dudley_entropy_integral'` and the negation-closure covering inflation
`coveringNumber_negDoubleFamily_le` (factor of 2) to bound the
with-abs empirical Rademacher complexity by the same Dudley entropy
integral expressed in covering numbers of the original family `F`
(not the doubled `negDoubleFamily F`), at the cost of a `2 ·` factor
inside the log.

This closes the with-abs Dudley analogue gap flagged in the session
ledger: downstream chains via
`uniform_deviation_expectation_le_two_smul_rademacher_complexity`
which uses the with-abs definition. -/
theorem dudley_entropy_integral_bound_with_abs
    {𝒳 : Type v} {n : ℕ} {ι : Type u} [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳} {c ε : ℝ}
    {C : ℝ} (hC : ∀ i j, |F i (S j)| ≤ C)
    (ε_pos : 0 < ε)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (m_pos : 0 < n) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c)
    (ε_le_c_div_2 : ε < c/2) :
    empiricalRademacherComplexity n F S ≤
      (4 * ε + (12 / Real.sqrt n) *
      (∫ (x : ℝ) in ε..(c/2),
        √(Real.log (2 * (coveringNumber h' x : ℝ))))) := by
  classical
  -- Positive / negative isometric embeddings into the doubled space.
  set e₀ : EmpiricalFunctionSpace F S →
      EmpiricalFunctionSpace (negDoubleFamily F) S :=
    fun q => ⟨((0 : Fin 2), q.index)⟩ with he₀_def
  set e₁ : EmpiricalFunctionSpace F S →
      EmpiricalFunctionSpace (negDoubleFamily F) S :=
    fun q => ⟨((1 : Fin 2), q.index)⟩ with he₁_def
  have he₀ : Isometry e₀ := by
    refine Isometry.of_dist_eq (fun q q' => ?_)
    show empiricalDist S (negDoubleFamily F (e₀ q).index)
        (negDoubleFamily F (e₀ q').index)
      = empiricalDist S (F q.index) (F q'.index)
    have h₁ : negDoubleFamily F ((0 : Fin 2), q.index) = F q.index := by
      funext x; simp [negDoubleFamily]
    have h₂ : negDoubleFamily F ((0 : Fin 2), q'.index) = F q'.index := by
      funext x; simp [negDoubleFamily]
    simp only [he₀_def, h₁, h₂]
  have he₁ : Isometry e₁ := by
    refine Isometry.of_dist_eq (fun q q' => ?_)
    show empiricalDist S (negDoubleFamily F (e₁ q).index)
        (negDoubleFamily F (e₁ q').index)
      = empiricalDist S (F q.index) (F q'.index)
    have h₁ : negDoubleFamily F ((1 : Fin 2), q.index) = -(F q.index) := by
      funext x; simp [negDoubleFamily]
    have h₂ : negDoubleFamily F ((1 : Fin 2), q'.index) = -(F q'.index) := by
      funext x; simp [negDoubleFamily]
    simp only [he₁_def, h₁, h₂]
    dsimp [empiricalDist, empiricalNorm]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- Derive `TotallyBounded` of the doubled function space from the
  -- isometric union cover.
  have h'_neg : TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace (negDoubleFamily F) S)) := by
    -- `Set.univ ⊆ e₀ '' univ ∪ e₁ '' univ` (every index has first
    -- component `0` or `1`).
    have hcov_set :
        (Set.univ : Set (EmpiricalFunctionSpace (negDoubleFamily F) S))
        ⊆ e₀ '' (Set.univ : Set (EmpiricalFunctionSpace F S))
          ∪ e₁ '' (Set.univ : Set (EmpiricalFunctionSpace F S)) := by
      intro q _
      rcases q with ⟨⟨s, i⟩⟩
      have hs : s = 0 ∨ s = 1 := by
        fin_cases s
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hs with hs0 | hs1
      · left
        refine ⟨⟨i⟩, Set.mem_univ _, ?_⟩
        simp [he₀_def, hs0]
      · right
        refine ⟨⟨i⟩, Set.mem_univ _, ?_⟩
        simp [he₁_def, hs1]
    have htb_e₀ : TotallyBounded (e₀ '' (Set.univ : Set _)) :=
      h'.image he₀.uniformContinuous
    have htb_e₁ : TotallyBounded (e₁ '' (Set.univ : Set _)) :=
      h'.image he₁.uniformContinuous
    exact (htb_e₀.union htb_e₁).subset hcov_set
  -- `empiricalNorm` is invariant under pointwise negation (squares
  -- ignore signs).
  have cs_neg : ∀ f : Fin 2 × ι,
      empiricalNorm S (negDoubleFamily F f) ≤ c := by
    intro ⟨s, i⟩
    by_cases hs : (s = 0)
    · have h₁ : negDoubleFamily F (s, i) = F i := by
        funext x; simp [negDoubleFamily, hs]
      rw [h₁]; exact cs i
    · have hs1 : s = 1 := by
        fin_cases s
        · exact (hs rfl).elim
        · rfl
      have h₁ : negDoubleFamily F (s, i) = -(F i) := by
        funext x; simp [negDoubleFamily, hs1]
      rw [h₁]
      -- empiricalNorm S (-(F i)) = empiricalNorm S (F i)
      have heq : empiricalNorm S (-(F i)) = empiricalNorm S (F i) := by
        dsimp [empiricalNorm]
        congr 1
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact neg_sq (F i (S j))
      rw [heq]
      exact cs i
  -- Bartlett–Mendelson bridge.
  have h_bridge :
      empiricalRademacherComplexity n F S
        = empiricalRademacherComplexity_without_abs n
            (negDoubleFamily F) S :=
    empiricalRademacherComplexity_eq_without_abs_negDoubleFamily F S hC
  -- Without-abs Dudley applied to the negDoubleFamily.
  have h_dudley :
      empiricalRademacherComplexity_without_abs n (negDoubleFamily F) S
        ≤ 4 * ε + (12 / Real.sqrt n) *
            (∫ (x : ℝ) in ε..(c/2),
              √(Real.log (coveringNumber h'_neg x))) :=
    dudley_entropy_integral' ε_pos h'_neg m_pos cs_neg ε_le_c_div_2
  -- Covering-number doubling pointwise on `[ε, c/2]` ⇒ pointwise
  -- bound on the integrand ⇒ interval-integral monotonicity.
  -- First, both integrands are AntitoneOn `[ε, c/2]` (composition of
  -- monotone `√` with antitone `log ∘ coveringNumber`).
  have hε_le : ε ≤ c / 2 := le_of_lt ε_le_c_div_2
  -- Nonemptiness of the underlying function space (needed to invoke
  -- `coveringNumber_nonzero`).
  have hNE : (Set.univ : Set (EmpiricalFunctionSpace F S)).Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨⟨i⟩, by simp⟩
  have hNE_neg :
      (Set.univ : Set (EmpiricalFunctionSpace (negDoubleFamily F) S)).Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨⟨((0 : Fin 2), i)⟩, by simp⟩
  -- Pointwise integrand bound on `[ε, c/2]`.
  have h_integrand_bd :
      ∀ x ∈ Set.Icc ε (c/2),
        √(Real.log (coveringNumber h'_neg x))
          ≤ √(Real.log (2 * (coveringNumber h' x : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ε_pos hx.1
    have hcov_pos_orig : 0 < coveringNumber h' x :=
      coveringNumber_nonzero hNE h' hx_pos
    have hcov_pos_neg : 0 < coveringNumber h'_neg x :=
      coveringNumber_nonzero hNE_neg h'_neg hx_pos
    have hcov_doubling :
        coveringNumber h'_neg x ≤ 2 * coveringNumber h' x :=
      coveringNumber_negDoubleFamily_le F S h' h'_neg hx_pos
    have hcov_doubling_real :
        (coveringNumber h'_neg x : ℝ) ≤ 2 * (coveringNumber h' x : ℝ) := by
      exact_mod_cast hcov_doubling
    have hcov_pos_neg_real : (0 : ℝ) < (coveringNumber h'_neg x : ℝ) := by
      exact_mod_cast hcov_pos_neg
    have hlog_le :
        Real.log (coveringNumber h'_neg x)
          ≤ Real.log (2 * (coveringNumber h' x : ℝ)) :=
      Real.log_le_log hcov_pos_neg_real hcov_doubling_real
    exact Real.sqrt_le_sqrt hlog_le
  -- Integrability (AntitoneOn ⇒ IntervalIntegrable) for both
  -- integrands. Pattern reused from `dudley_entropy_integral'`.
  have h_int_neg :
      IntervalIntegrable
        (fun x => √(Real.log (coveringNumber h'_neg x)))
        MeasureTheory.volume ε (c/2) := by
    apply AntitoneOn.intervalIntegrable
    have f0 : Monotone (fun x ↦ √x) := fun _ _ h => Real.sqrt_le_sqrt h
    apply Monotone.comp_antitoneOn f0
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    dsimp [Set.uIcc, Set.Icc] at ha hb
    have hmin : min ε (c / 2) = ε := by simp; linarith
    rw [hmin] at ha hb
    -- AntitoneOn: `a < b → f b ≤ f a`. With `f x = log (cov h'_neg x)`.
    apply Real.log_le_log
    · -- Need `0 < (cov h'_neg b : ℝ)`.
      exact_mod_cast coveringNumber_nonzero hNE_neg h'_neg
        (lt_of_lt_of_le ε_pos hb.1)
    · -- Need `(cov h'_neg b : ℝ) ≤ (cov h'_neg a : ℝ)` from antitonicity.
      exact_mod_cast converingNumber_antitone h'_neg
        (lt_of_lt_of_le ε_pos ha.1) (lt_of_lt_of_le ε_pos hb.1)
        (le_of_lt hab)
  have h_int_pos :
      IntervalIntegrable
        (fun x => √(Real.log (2 * (coveringNumber h' x : ℝ))))
        MeasureTheory.volume ε (c/2) := by
    apply AntitoneOn.intervalIntegrable
    have f0 : Monotone (fun x ↦ √x) := fun _ _ h => Real.sqrt_le_sqrt h
    apply Monotone.comp_antitoneOn f0
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    dsimp [Set.uIcc, Set.Icc] at ha hb
    have hmin : min ε (c / 2) = ε := by simp; linarith
    rw [hmin] at ha hb
    -- AntitoneOn: `a < b → f b ≤ f a`. With `f x = log (2 * cov h' x)`.
    apply Real.log_le_log
    · -- Need `0 < 2 * (cov h' b : ℝ)`.
      have hb_pos : (0 : ℝ) < (coveringNumber h' b : ℝ) := by
        exact_mod_cast coveringNumber_nonzero hNE h'
          (lt_of_lt_of_le ε_pos hb.1)
      linarith
    · -- Need `2 * (cov h' b : ℝ) ≤ 2 * (cov h' a : ℝ)` from antitonicity.
      have hmono : coveringNumber h' b ≤ coveringNumber h' a :=
        converingNumber_antitone h' (lt_of_lt_of_le ε_pos ha.1)
          (lt_of_lt_of_le ε_pos hb.1) (le_of_lt hab)
      have : (coveringNumber h' b : ℝ) ≤ (coveringNumber h' a : ℝ) := by
        exact_mod_cast hmono
      linarith
  -- Apply interval-integral monotonicity.
  have h_int_mono :
      (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber h'_neg x)))
        ≤ ∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber h' x : ℝ))) :=
    intervalIntegral.integral_mono_on hε_le h_int_neg h_int_pos h_integrand_bd
  -- Multiplier `12 / √n` is nonnegative.
  have h_mul_nonneg : (0 : ℝ) ≤ 12 / Real.sqrt n :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  -- Chain everything.
  calc empiricalRademacherComplexity n F S
      = empiricalRademacherComplexity_without_abs n (negDoubleFamily F) S :=
        h_bridge
    _ ≤ 4 * ε + (12 / Real.sqrt n) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (coveringNumber h'_neg x))) := h_dudley
    _ ≤ 4 * ε + (12 / Real.sqrt n) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (2 * (coveringNumber h' x : ℝ)))) := by
        have hmul :
            (12 / Real.sqrt n) *
              (∫ (x : ℝ) in ε..(c/2),
                √(Real.log (coveringNumber h'_neg x)))
            ≤ (12 / Real.sqrt n) *
              (∫ (x : ℝ) in ε..(c/2),
                √(Real.log (2 * (coveringNumber h' x : ℝ)))) :=
          mul_le_mul_of_nonneg_left h_int_mono h_mul_nonneg
        linarith

end
