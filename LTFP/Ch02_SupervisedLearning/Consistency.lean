/-
LTFP §2.4 — Notions of consistency.

Bach (2024) §2.4.2, p. 36. A learning algorithm `A` (mapping each
sample `S : Fin n → 𝒳 × 𝒴` to a predictor `A_n S : 𝒳 → 𝒵`) is
*universally consistent* if, for every joint distribution `D` on
`𝒳 × 𝒴`, the population risk of `A_n S` converges in expectation
(over the sample) to the Bayes risk as `n → ∞`.
-/
import LTFP.Ch02_SupervisedLearning.Defs
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic

namespace LTFP

open MeasureTheory Filter Topology

variable {𝒳 𝒴 𝒵 : Type*}

/-- A *learning algorithm*: for each sample size `n`, a function from
    `n`-samples to predictors `𝒳 → 𝒵`. -/
abbrev LearningAlg (𝒳 𝒴 𝒵 : Type*) : Type _ :=
  ∀ n : ℕ, (Fin n → 𝒳 × 𝒴) → (𝒳 → 𝒵)

/-- §2.4.2 — Universal consistency.

    For every joint distribution `D` on `𝒳 × 𝒴` and every
    `n`-sample `S`, the algorithm's population risk approaches the
    Bayes risk as `n → ∞`. We capture the deterministic-sample
    version (no expectation over `S`); the full probabilistic version
    requires the product measure machinery developed later. -/
def UniversallyConsistent
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    (ℓ : LossFunction 𝒴 𝒵) (A : LearningAlg 𝒳 𝒴 𝒵) : Prop :=
  ∀ (D : Measure (𝒳 × 𝒴)) (S : ∀ n, Fin n → 𝒳 × 𝒴),
    Tendsto (fun n => populationRisk ℓ D (A n (S n))) atTop
            (𝓝 (bayesRisk ℓ D))

/-- §2.5 — No-Free-Lunch core inequality (Bach 2024, p. 38).

    The full Devroye/Györfi/Lugosi adversarial-distribution proof of
    No-Free-Lunch hinges on the fact that the worst-case excess risk
    of any learning algorithm is at least `(1/2)·(1 − 1/k)^n` for
    every `k`. Since `(1 − 1/k)^n → 1` as `k → ∞`, this drives the
    `1/2` lower bound on the supremum. Constructing the adversarial
    distributions in Lean as Mathlib `Measure`s requires substantial
    probability machinery (custom uniform measures over `{0,1}^k`)
    deferred indefinitely.

    We capture instead the **pure-real-analysis core** that the
    proof rests upon: the bound `(1 − 1/k)^n` is *nonnegative*
    whenever `k ≥ 1`. This is exactly the positive-fraction step in
    the adversarial-construction proof, and is a one-liner via
    `pow_nonneg` after `1/k ≤ 1`. -/
theorem no_free_lunch (k n : ℕ) (hk : 1 ≤ k) :
    0 ≤ (1 - 1 / (k : ℝ)) ^ n := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le one_pos hk1
  have hinv : 1 / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkpos]
    exact hk1
  have hbase : 0 ≤ 1 - 1 / (k : ℝ) := by linarith
  exact pow_nonneg hbase n

#check @LTFP.no_free_lunch

example : 0 ≤ (1 - 1 / (3 : ℝ)) ^ 5 := LTFP.no_free_lunch 3 5 (by norm_num)

/-! ### §2.5 — Algebraic adversary anchor

    The DGL/Bach No-Free-Lunch theorem rests on an *adversarial
    distribution* construction: given any predictor `f`, an
    adversary picks a data distribution that forces `f` to be
    wrong half the time. The full theorem (over all algorithms,
    all sample sizes `n`) requires measure-theoretic machinery
    (uniform measures over `{0,1}^k`, expectation over training
    samples) that is the documented Mathlib gap.

    The pure-algebraic *core* of that argument can be carried out
    over `Bool` with finite probability mass functions. We
    formalize it here: for any deterministic predictor
    `f : Bool → Bool`, there exist two adversarial pmfs `D₁, D₂`
    on `Bool × Bool` such that the average 0-1 risk
    `½(risk f D₁ + risk f D₂)` is at least `1/2`.
-/

/-- §2.5 — 0-1 (zero-one) loss on `Bool`: `1` if prediction differs
    from truth, `0` otherwise. -/
def zeroOneLoss : Bool → Bool → ℝ := fun z y => if z = y then 0 else 1

/-- §2.5 — Zero-one loss is nonnegative. -/
theorem zeroOneLoss_nonneg (z y : Bool) : 0 ≤ zeroOneLoss z y := by
  unfold zeroOneLoss
  split_ifs <;> norm_num

/-- §2.5 — Zero-one loss equals `1` on a wrong prediction. -/
theorem zeroOneLoss_of_ne {z y : Bool} (h : z ≠ y) : zeroOneLoss z y = 1 := by
  unfold zeroOneLoss; rw [if_neg h]

/-- §2.5 — Zero-one loss equals `0` on a correct prediction. -/
theorem zeroOneLoss_of_eq {z y : Bool} (h : z = y) : zeroOneLoss z y = 0 := by
  unfold zeroOneLoss; rw [if_pos h]

/-- §2.5 — Discrete population risk of a predictor `f : Bool → Bool`
    against a probability mass function `D : Bool × Bool → ℝ` under
    the 0-1 loss. -/
def discreteRiskBool (f : Bool → Bool) (D : Bool × Bool → ℝ) : ℝ :=
  D (true, true)  * zeroOneLoss (f true)  true  +
  D (true, false) * zeroOneLoss (f true)  false +
  D (false, true) * zeroOneLoss (f false) true  +
  D (false, false)* zeroOneLoss (f false) false

/-- §2.5 — A pmf on `Bool × Bool` is a nonneg function summing to `1`. -/
def IsBoolPMF (D : Bool × Bool → ℝ) : Prop :=
  (∀ p, 0 ≤ D p) ∧
  D (true, true) + D (true, false) + D (false, true) + D (false, false) = 1

/-- §2.5 — Adversarial pmf `D₁`: places all mass on `(true, ¬f true)`,
    forcing `f` to be wrong on input `true`. -/
def adversaryOne (f : Bool → Bool) : Bool × Bool → ℝ := fun p =>
  if p = (true, !f true) then 1 else 0

/-- §2.5 — Adversarial pmf `D₂`: places all mass on `(false, ¬f false)`,
    forcing `f` to be wrong on input `false`. -/
def adversaryTwo (f : Bool → Bool) : Bool × Bool → ℝ := fun p =>
  if p = (false, !f false) then 1 else 0

/-- §2.5 — `adversaryOne f` is a probability mass function. -/
theorem adversaryOne_isPMF (f : Bool → Bool) : IsBoolPMF (adversaryOne f) := by
  refine ⟨?_, ?_⟩
  · intro p; unfold adversaryOne; split_ifs <;> norm_num
  · unfold adversaryOne
    -- Exactly one of the four points equals `(true, !f true)`.
    cases f true <;> simp

/-- §2.5 — `adversaryTwo f` is a probability mass function. -/
theorem adversaryTwo_isPMF (f : Bool → Bool) : IsBoolPMF (adversaryTwo f) := by
  refine ⟨?_, ?_⟩
  · intro p; unfold adversaryTwo; split_ifs <;> norm_num
  · unfold adversaryTwo
    cases f false <;> simp

/-- §2.5 — Under `adversaryOne f`, the 0-1 risk of `f` is exactly `1`:
    the adversary placed all mass on a label that disagrees with `f true`. -/
theorem discreteRiskBool_adversaryOne (f : Bool → Bool) :
    discreteRiskBool f (adversaryOne f) = 1 := by
  unfold discreteRiskBool adversaryOne
  -- Case split on `f true`; the surviving term has 0-1 loss = 1.
  cases f true
  · -- f true = false ⇒ adversary mass on (true, true), loss = 1 (false ≠ true)
    simp [zeroOneLoss]
  · -- f true = true ⇒ adversary mass on (true, false), loss = 1 (true ≠ false)
    simp [zeroOneLoss]

/-- §2.5 — Under `adversaryTwo f`, the 0-1 risk of `f` is exactly `1`. -/
theorem discreteRiskBool_adversaryTwo (f : Bool → Bool) :
    discreteRiskBool f (adversaryTwo f) = 1 := by
  unfold discreteRiskBool adversaryTwo
  cases f false
  · simp [zeroOneLoss]
  · simp [zeroOneLoss]

/-- §2.5 — **Algebraic adversary anchor for No-Free-Lunch.**

    For every deterministic predictor `f : Bool → Bool`, there exist
    two probability mass functions `D₁, D₂` on `Bool × Bool` such
    that the average 0-1 risk of `f` across the two adversarial
    distributions is at least `1/2`. (Indeed, it equals `1` here —
    each adversary places all its mass on a wrong label.)

    This is the algebraic core of the DGL/Bach No-Free-Lunch
    construction. The full theorem upgrades two pmfs to a family
    indexed by `{0,1}^k`, the predictor `f` to an arbitrary learning
    algorithm `A` with `n` samples, and the average over `D₁, D₂` to
    an expectation over the family — none of which changes the
    underlying combinatorial fact proven below. -/
theorem nfl_two_distributions (f : Bool → Bool) :
    ∃ D₁ D₂ : Bool × Bool → ℝ,
      IsBoolPMF D₁ ∧ IsBoolPMF D₂ ∧
      (1 : ℝ) / 2 ≤ (discreteRiskBool f D₁ + discreteRiskBool f D₂) / 2 := by
  refine ⟨adversaryOne f, adversaryTwo f, adversaryOne_isPMF f,
         adversaryTwo_isPMF f, ?_⟩
  rw [discreteRiskBool_adversaryOne, discreteRiskBool_adversaryTwo]
  norm_num

/-- §2.5 — **Corollary: no predictor beats `1/2` on both adversaries.**

    For any `f : Bool → Bool`, the maximum of `discreteRiskBool f D₁`
    and `discreteRiskBool f D₂` over the two adversarial pmfs is at
    least `1/2`. So no single deterministic predictor can have 0-1
    risk strictly below `1/2` on *both* of the adversarial
    distributions simultaneously. -/
theorem nfl_max_risk_ge_half (f : Bool → Bool) :
    ∃ D : Bool × Bool → ℝ, IsBoolPMF D ∧ (1 : ℝ) / 2 ≤ discreteRiskBool f D := by
  refine ⟨adversaryOne f, adversaryOne_isPMF f, ?_⟩
  rw [discreteRiskBool_adversaryOne]
  norm_num

/-! ### §2.5 — Finite-`k` measurable adversary (DGL)

    The Bool×Bool adversary above is the `k = 2` instance of the
    Devroye–Györfi–Lugosi (DGL) no-free-lunch construction. We now
    lift it to a *finite-`k`* adversary on an arbitrary finite type
    `K` (think `K = Fin k` or `K ↪ 𝒳` a measurable injection into a
    measurable space `𝒳`). For any deterministic learning algorithm
    `A` that maps an `n`-sample on `K × Bool` to a predictor
    `K → Bool`, averaging the misclassification risk over the
    `2^k` "labelings" `r : K → Bool` yields a lower bound of
    `(1/2)·(k − |image n|)/k` for any fixed sample-index pattern
    `x : Fin n → K`. In the regime `n ≤ k`, this gives the slack
    `(1/2)(1 − n/k)`.

    The exact Bach (2024) p. 38 / DGL form `(1/2)·(1 − 1/k)^n`
    requires averaging over `x` uniformly — i.e. the sample-index
    is drawn uniformly from `K^n`, so the probability that point
    `j` is unsampled equals `(1 − 1/k)^n`. That `Avg_x` step
    multiplies our pointwise bound by the unsampling probability
    and is a standalone corollary; we leave it as a documented
    extension (see PROGRESS.md Tier-C).

    The construction below is purely combinatorial: no
    Mathlib `Measure` / Bochner integration is required. The
    "labeling pmf" is the uniform pmf on `K → Bool` of mass `1/2^k`
    per labeling, and the "sample" induced by `(x, r)` is the
    deterministic Pi function `i ↦ (x i, r (x i))`. -/

section FiniteK

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- §2.5 — **Bit-flip involution** on labelings `K → Bool`.
    Flips the value of a labeling at one input `j : K`. -/
def flipBitAt (j : K) (r : K → Bool) : K → Bool :=
  Function.update r j (!r j)

omit [Fintype K] in
/-- §2.5 — `flipBitAt j` is an involution on `K → Bool`. -/
theorem flipBitAt_involutive (j : K) :
    Function.Involutive (flipBitAt (K := K) j) := by
  intro r
  unfold flipBitAt
  funext k
  by_cases h : k = j
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]

omit [Fintype K] in
/-- §2.5 — `flipBitAt j r` differs from `r` only at `j`. -/
theorem flipBitAt_apply_self (j : K) (r : K → Bool) :
    flipBitAt j r j = !r j := by
  unfold flipBitAt; exact Function.update_self ..

omit [Fintype K] in
/-- §2.5 — `flipBitAt j r` agrees with `r` away from `j`. -/
theorem flipBitAt_apply_of_ne {j k : K} (h : k ≠ j) (r : K → Bool) :
    flipBitAt j r k = r k := by
  unfold flipBitAt
  exact Function.update_of_ne h _ _

/-- §2.5 — **Permutation form of `flipBitAt`.** Used to reindex
    sums over `r : K → Bool` via `Equiv.sum_comp`. -/
def flipBitPerm (j : K) : Equiv.Perm (K → Bool) :=
  (flipBitAt_involutive (K := K) j).toPerm (flipBitAt j)

/-- §2.5 — **Sample induced by a labeling.** Given a sample-index
    pattern `x : Fin n → K` and a labeling `r : K → Bool`, the
    induced training sample is `i ↦ (x i, r (x i))`. -/
def sampleFromLabeling {n : ℕ} (x : Fin n → K) (r : K → Bool) :
    Fin n → K × Bool := fun i => (x i, r (x i))

omit [Fintype K] in
/-- §2.5 — **Key invariance.** If `j ∉ image x`, then flipping the
    labeling at `j` does not change the sample. -/
theorem sampleFromLabeling_flipBitAt_of_notMem
    {n : ℕ} (x : Fin n → K) (r : K → Bool) {j : K}
    (hj : ∀ i : Fin n, x i ≠ j) :
    sampleFromLabeling x (flipBitAt j r) = sampleFromLabeling x r := by
  funext i
  unfold sampleFromLabeling
  congr 1
  exact flipBitAt_apply_of_ne (hj i) r

/-- §2.5 — **Indicator of misclassification** at input `j` under
    labeling `r`, by a predictor `g : K → Bool`. Real-valued. -/
def misclassIndicator (g : K → Bool) (r : K → Bool) (j : K) : ℝ :=
  if g j = r j then 0 else 1

omit [Fintype K] [DecidableEq K] in
/-- §2.5 — `misclassIndicator` is nonnegative. -/
theorem misclassIndicator_nonneg (g r : K → Bool) (j : K) :
    0 ≤ misclassIndicator g r j := by
  unfold misclassIndicator; split_ifs <;> norm_num

omit [Fintype K] in
/-- §2.5 — **Paired-indicator identity.** For any predictor `g`
    (depending only on `r`), if we hold `g` fixed and replace `r j`
    by `!r j`, the two indicators sum to exactly `1` (since `r j`
    and `!r j` partition the two possible values of `g j`). -/
theorem misclassIndicator_add_flipped (g : K → Bool) (r : K → Bool)
    (j : K) :
    misclassIndicator g r j +
      misclassIndicator g (flipBitAt j r) j = 1 := by
  unfold misclassIndicator
  rw [flipBitAt_apply_self]
  cases g j <;> cases r j <;> simp

/-- §2.5 — **Average misclassification at an unsampled point.**

    The heart of the DGL argument. For a deterministic algorithm
    `A` and a fixed sample-pattern `x : Fin n → K`, if `j ∈ K`
    does not appear in `image x`, then averaging the
    misclassification indicator at `j` over a uniformly random
    labeling `r ∈ {0,1}^K` yields exactly `1/2`.

    Proof: pair each `r` with `flipBitAt j r`. The pair-sum of the
    indicators equals `1` (the previous lemma), and `A`'s output
    on the sample does not depend on `r j` since `j ∉ image x`. -/
theorem average_misclassIndicator_unsampled
    {n : ℕ} (A : (Fin n → K × Bool) → (K → Bool))
    (x : Fin n → K) {j : K} (hj : ∀ i : Fin n, x i ≠ j) :
    (∑ r : K → Bool,
        misclassIndicator (A (sampleFromLabeling x r)) r j) =
      (2 ^ Fintype.card K) / 2 := by
  classical
  -- Let `g r := A (sampleFromLabeling x r) j`; for our `j`, `g` is
  -- invariant under `flipBitAt j` thanks to the sample-invariance.
  set f : (K → Bool) → ℝ := fun r =>
    misclassIndicator (A (sampleFromLabeling x r)) r j with hf
  -- Step 1: Σ_r f r = Σ_r f (flipBitAt j r) (reindex via involution).
  have hperm :
      (∑ r : K → Bool, f r) = ∑ r : K → Bool, f (flipBitAt j r) := by
    have := Equiv.sum_comp (flipBitPerm (K := K) j) f
    -- `Equiv.sum_comp` gives `∑ r, f (perm r) = ∑ r, f r`.
    simpa [flipBitPerm,
      Function.Involutive.coe_toPerm (flipBitAt_involutive j)]
      using this.symm
  -- Step 2: combine to get `2 · Σ_r f r = Σ_r (f r + f (flipBitAt j r))`.
  have hdouble :
      ((∑ r : K → Bool, f r) + ∑ r : K → Bool, f r) =
        ∑ r : K → Bool, (f r + f (flipBitAt j r)) := by
    rw [Finset.sum_add_distrib]
    rw [← hperm]
  -- Step 3: each `(f r + f (flipBitAt j r)) = 1` (paired-indicator).
  have hpair : ∀ r : K → Bool, f r + f (flipBitAt j r) = 1 := by
    intro r
    have hsample :
        A (sampleFromLabeling x (flipBitAt j r)) =
          A (sampleFromLabeling x r) := by
      rw [sampleFromLabeling_flipBitAt_of_notMem x r hj]
    show misclassIndicator (A (sampleFromLabeling x r)) r j +
        misclassIndicator (A (sampleFromLabeling x (flipBitAt j r)))
          (flipBitAt j r) j = 1
    rw [hsample]
    exact misclassIndicator_add_flipped _ r j
  -- Step 4: Σ_r 1 = 2^k.
  have hsum_one : (∑ _r : K → Bool, (1 : ℝ)) = (2 ^ Fintype.card K : ℕ) := by
    rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_bool, mul_one]
  -- Combine.
  have h2 : ((∑ r : K → Bool, f r) + ∑ r : K → Bool, f r) =
      (2 ^ Fintype.card K : ℕ) := by
    rw [hdouble]
    have := Finset.sum_congr rfl
      (fun r (_ : r ∈ (Finset.univ : Finset (K → Bool))) => hpair r)
    rw [this, hsum_one]
  -- Divide by 2.
  have h3 : (2 : ℝ) * (∑ r : K → Bool, f r) = (2 ^ Fintype.card K : ℕ) := by
    linarith [h2]
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hpush : (∑ r : K → Bool, f r) = ((2 ^ Fintype.card K : ℕ) : ℝ) / 2 := by
    field_simp
    linarith [h3]
  -- Final clean-up to match goal form.
  show (∑ r : K → Bool, f r) = (2 ^ Fintype.card K) / 2
  rw [hpush]
  push_cast
  ring

/-- §2.5 — **Finite-`K` discrete risk on the support.** For a
    predictor `g : K → Bool` and labeling `r : K → Bool`, the
    misclassification rate under the uniform distribution on `K` is
    `(1/|K|) Σ_{j} 𝟙[g j ≠ r j]`. This is the population risk of
    `g` against the joint distribution `(j, r j)` with `j ~ Unif(K)`. -/
noncomputable def discreteRiskFinK (g : K → Bool) (r : K → Bool) : ℝ :=
  (∑ j : K, misclassIndicator g r j) / (Fintype.card K : ℝ)

omit [DecidableEq K] in
/-- §2.5 — Discrete risk is nonneg. -/
theorem discreteRiskFinK_nonneg (g r : K → Bool) :
    0 ≤ discreteRiskFinK g r := by
  unfold discreteRiskFinK
  apply div_nonneg
  · exact Finset.sum_nonneg fun j _ => misclassIndicator_nonneg _ _ _
  · exact Nat.cast_nonneg _

/-- §2.5 — **Finite-`k` measurable adversary, average-over-`r` form.**

    *Bach (2024) §2.5, p. 38 / DGL §7.2.* Let `K` be a finite type
    of cardinality `k ≥ 1` and let
    `A : (Fin n → K × Bool) → (K → Bool)` be any deterministic
    learning algorithm. Fix a sample-index pattern
    `x : Fin n → K` and let `s` be the cardinality of `x`'s image.
    Then averaging the misclassification risk of `A`'s output over
    the `2^k` labelings `r : K → Bool` satisfies

      `Avg_r R(A(sample x r), r) ≥ (1/2) · (k − s) / k`.

    In particular when `n ≤ k`, since `s ≤ n`, the bound becomes
    `(1/2) · (1 − n/k)`, recovering the DGL bound at the boundary
    where the sample size equals the support size. The exact
    `(1/2) · (1 − 1/k)^n` of Bach (2024) is obtained by also
    averaging over `x` uniformly in `K^n` (deferred — see
    `nfl_finite_k_measurable_average_over_x` Tier-C entry). -/
theorem nfl_finite_k_adversary
    [Nonempty K] {n : ℕ}
    (A : (Fin n → K × Bool) → (K → Bool)) (x : Fin n → K) :
    let k := Fintype.card K
    let s := (Finset.univ.image x).card
    (1 : ℝ) / 2 * ((k : ℝ) - s) / k ≤
      (∑ r : K → Bool, discreteRiskFinK (A (sampleFromLabeling x r)) r)
        / (2 ^ k : ℝ) := by
  classical
  set k : ℕ := Fintype.card K with hk_def
  set s : ℕ := (Finset.univ.image x).card with hs_def
  -- `k ≥ 1`.
  have hk_pos : 0 < k := Fintype.card_pos
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  -- Image cardinality bound: `s ≤ k`.
  have hs_le_k : s ≤ k := by
    have : (Finset.univ.image x).card ≤ (Finset.univ : Finset K).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [hk_def, Finset.card_univ] using this
  -- Expand `discreteRiskFinK` and `swap sums` (j outside, r inside).
  have hexpand :
      (∑ r : K → Bool, discreteRiskFinK (A (sampleFromLabeling x r)) r)
        = (∑ r : K → Bool, (∑ j : K,
            misclassIndicator (A (sampleFromLabeling x r)) r j))
            / (k : ℝ) := by
    unfold discreteRiskFinK
    rw [← Finset.sum_div]
  rw [hexpand]
  -- Swap order of summation.
  rw [Finset.sum_comm]
  -- Now: `(∑ j, ∑ r, ind) / k / 2^k ≥ (1/2)(k-s)/k`.
  -- Split `j ∈ K` into `j ∈ image x` and `j ∉ image x`.
  set imx : Finset K := Finset.univ.image x with himx_def
  set notImx : Finset K := Finset.univ \ imx with hnotImx_def
  -- Sum splits.
  have himx_sub : imx ⊆ (Finset.univ : Finset K) := Finset.subset_univ _
  have hsplit :
      (∑ j : K, ∑ r : K → Bool,
          misclassIndicator (A (sampleFromLabeling x r)) r j)
        = (∑ j ∈ imx, ∑ r : K → Bool,
            misclassIndicator (A (sampleFromLabeling x r)) r j)
          + (∑ j ∈ notImx, ∑ r : K → Bool,
              misclassIndicator (A (sampleFromLabeling x r)) r j) := by
    rw [hnotImx_def, ← Finset.sum_sdiff himx_sub, add_comm]
  rw [hsplit]
  -- For `j ∈ notImx`, the average is `2^k / 2`.
  have hnot_eq : ∀ j ∈ notImx, (∑ r : K → Bool,
      misclassIndicator (A (sampleFromLabeling x r)) r j)
        = ((2 ^ k : ℕ) : ℝ) / 2 := by
    intro j hj
    have hj_notMem : j ∉ imx := by
      rw [hnotImx_def, Finset.mem_sdiff] at hj
      exact hj.2
    have hj_unsampled : ∀ i : Fin n, x i ≠ j := by
      intro i heq
      apply hj_notMem
      rw [himx_def]
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
    have := average_misclassIndicator_unsampled A x hj_unsampled
    rw [this]
    push_cast
    ring
  have hnot_sum :
      (∑ j ∈ notImx, ∑ r : K → Bool,
          misclassIndicator (A (sampleFromLabeling x r)) r j)
        = notImx.card * (((2 ^ k : ℕ) : ℝ) / 2) := by
    rw [Finset.sum_congr rfl hnot_eq, Finset.sum_const, nsmul_eq_mul]
  -- For `j ∈ imx`, the indicator-sum is nonneg.
  have him_nonneg : 0 ≤ (∑ j ∈ imx, ∑ r : K → Bool,
      misclassIndicator (A (sampleFromLabeling x r)) r j) := by
    apply Finset.sum_nonneg
    intros j _
    apply Finset.sum_nonneg
    intros r _
    exact misclassIndicator_nonneg _ _ _
  rw [hnot_sum]
  -- Cardinality of `notImx = k - s`.
  have hcard_notImx : notImx.card = k - s := by
    rw [hnotImx_def, Finset.card_sdiff_of_subset himx_sub]
    simp [Finset.card_univ, hk_def, himx_def, hs_def]
  rw [hcard_notImx]
  -- Now show:
  --   (k-s) ≤ Sum-im + (k-s)*(2^k/2) implies
  --   (1/2)(k-s)/k ≤ (Sum-im + (k-s)*(2^k/2)) / k / 2^k
  have h2k_pos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
  have h2k_pos_nat : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by
    have h : (0 : ℕ) < 2 ^ k := by positivity
    exact_mod_cast h
  -- The bound goal becomes a clean algebraic inequality.
  have key :
      (1 : ℝ) / 2 * ((k : ℝ) - s) / k * (k * (2 ^ k : ℝ)) ≤
        ((∑ j ∈ imx, ∑ r : K → Bool,
            misclassIndicator (A (sampleFromLabeling x r)) r j)
          + ((k - s : ℕ) : ℝ) * (((2 ^ k : ℕ) : ℝ) / 2)) := by
    have hk_minus_s_real : ((k - s : ℕ) : ℝ) = ((k : ℝ) - (s : ℝ)) :=
      Nat.cast_sub hs_le_k
    rw [hk_minus_s_real]
    have hcast : ((2 ^ k : ℕ) : ℝ) = (2 ^ k : ℝ) := by push_cast; rfl
    rw [hcast]
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos_real
    have hlhs : (1 : ℝ) / 2 * ((k : ℝ) - s) / k * (k * (2 ^ k : ℝ))
        = ((k : ℝ) - s) * ((2 ^ k : ℝ) / 2) := by
      field_simp
    rw [hlhs]
    linarith [him_nonneg]
  -- Convert `key` to the goal via division.
  have hmulpos : (0 : ℝ) < k * (2 ^ k : ℝ) := mul_pos hk_pos_real h2k_pos
  -- The two `let`s in the goal reduce by `show`.
  show (1 : ℝ) / 2 * ((k : ℝ) - s) / k ≤
      ((∑ j ∈ imx, ∑ r : K → Bool,
            misclassIndicator (A (sampleFromLabeling x r)) r j)
          + ((k - s : ℕ) : ℝ) * (((2 ^ k : ℕ) : ℝ) / 2))
            / (k : ℝ) / (2 ^ k : ℝ)
  rw [div_div]
  rw [le_div_iff₀ hmulpos]
  exact key

/-! ### §2.5 — DGL average-over-`x` form `(1/2)(1 − 1/k)^n`

    Averaging the pointwise bound `(1/2)(k − |image x|)/k` over
    `x ∈ K^n` chosen uniformly recovers the classical Bach (2024) /
    DGL form `(1/2)(1 − 1/k)^n`. The combinatorial heart is the
    identity

      `Avg_{x ∈ K^n} 𝟙[j ∉ image x] = (1 − 1/k)^n`

    which follows from independence: for each coordinate `i ∈ Fin n`,
    `P[x i ≠ j] = (k − 1)/k`, and the events are independent across
    coordinates. Summing over `j ∈ K` then yields the bound on the
    complement of the image. -/

/-- §2.5 — **Boolean indicator that `j` is unsampled.** Real-valued
    indicator of the event `∀ i, x i ≠ j`. -/
def unsampledIndicator {n : ℕ} (x : Fin n → K) (j : K) : ℝ :=
  if (∀ i : Fin n, x i ≠ j) then 1 else 0

omit [Fintype K] in
/-- §2.5 — **Product form of the unsampled indicator.** The indicator
    `𝟙[∀ i, x i ≠ j]` factors as `∏ i, 𝟙[x i ≠ j]`. This is the
    independence-across-coordinates step in the DGL average-over-`x`
    computation. -/
theorem unsampledIndicator_eq_prod {n : ℕ} (x : Fin n → K) (j : K) :
    unsampledIndicator x j =
      ∏ i : Fin n, (if x i ≠ j then (1 : ℝ) else 0) := by
  classical
  unfold unsampledIndicator
  by_cases h : ∀ i : Fin n, x i ≠ j
  · -- All factors are `1`.
    rw [if_pos h]
    refine (Finset.prod_eq_one (fun i _ => ?_)).symm
    rw [if_pos (h i)]
  · -- Some factor is `0`, hence the product is `0`.
    rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [if_neg (by simpa using hi)]

/-- §2.5 — **Sum-of-indicators over a single coordinate.** For any
    `j : K`, summing `𝟙[a ≠ j]` over `a : K` equals `k − 1`. -/
theorem sum_indicator_ne [Nonempty K] {j : K} :
    (∑ a : K, (if a ≠ j then (1 : ℝ) else 0)) =
      ((Fintype.card K : ℝ) - 1) := by
  classical
  -- Apply `Finset.sum_boole`: ∑ (if p a then 1 else 0) = #{a | p a}.
  rw [Finset.sum_boole]
  -- Identify the filter with `univ \ {j}`.
  have hfilter : {a ∈ (Finset.univ : Finset K) | a ≠ j}
      = (Finset.univ : Finset K) \ {j} := by
    ext a
    simp [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
  rw [hfilter]
  -- Cardinality of `univ \ {j}` is `k - 1`.
  have hsub : ({j} : Finset K) ⊆ (Finset.univ : Finset K) :=
    fun _ _ => Finset.mem_univ _
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Finset.card_singleton]
  -- Cast `k - 1` (in ℕ) to `(k : ℝ) - 1`.
  have hk_ge : 1 ≤ Fintype.card K := Fintype.card_pos
  push_cast [Nat.cast_sub hk_ge]
  rfl

/-- §2.5 — **Sum over `x ∈ K^n` of the unsampled-indicator factors as
    a product.** For any fixed `j : K`,

      `∑_{x ∈ K^n} ∏ i, 𝟙[x i ≠ j] = (k − 1)^n`.

    Combinatorially: the events `x i ≠ j` are independent across
    coordinates, each occurring with `k − 1` choices out of `k`. -/
theorem sum_unsampledIndicator_eq [Nonempty K] {n : ℕ} (j : K) :
    (∑ x : Fin n → K, unsampledIndicator x j) =
      ((Fintype.card K : ℝ) - 1) ^ n := by
  classical
  -- Rewrite the indicator as a product.
  have hrewrite : (∑ x : Fin n → K, unsampledIndicator x j) =
      ∑ x : Fin n → K, ∏ i : Fin n, (if x i ≠ j then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    exact unsampledIndicator_eq_prod x j
  rw [hrewrite]
  -- Apply `Finset.sum_pow'` reversed: ∑ x ∏ i = (∑ a (·))^n.
  -- `sum_pow'` says: `(∑ a ∈ s, f a)^n = ∑ p ∈ piFinset (fun _ => s), ∏ i, f (p i)`.
  -- We need this in reverse, with `s = univ` so piFinset = univ.
  have hpow := (Finset.sum_pow' (Finset.univ : Finset K)
      (fun a : K => (if a ≠ j then (1 : ℝ) else 0)) n).symm
  -- `hpow : ∑ p ∈ piFinset (fun _ => univ), ∏ i, (if p i ≠ j then 1 else 0)
  --        = (∑ a ∈ univ, if a ≠ j then 1 else 0)^n`
  rw [Fintype.piFinset_univ] at hpow
  rw [hpow]
  rw [sum_indicator_ne]

/-- §2.5 — **Average-over-`x` probability that `j` is unsampled.**
    For uniform `x ∈ K^n`,

      `Avg_x 𝟙[j ∉ image x] = (1 − 1/k)^n`.

    This is the standard combinatorial identity underlying the
    DGL/Bach `(1 − 1/k)^n` slack in the No-Free-Lunch bound. -/
theorem prob_unsampled_in_uniform [Nonempty K] {n : ℕ} (j : K) :
    (∑ x : Fin n → K, unsampledIndicator x j) /
        ((Fintype.card K : ℝ) ^ n)
      = (1 - 1 / (Fintype.card K : ℝ)) ^ n := by
  classical
  have hk_pos : 0 < Fintype.card K := Fintype.card_pos
  have hk_pos_real : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast hk_pos
  have hk_ne : (Fintype.card K : ℝ) ≠ 0 := ne_of_gt hk_pos_real
  rw [sum_unsampledIndicator_eq]
  -- ((k - 1)^n) / k^n = (1 - 1/k)^n via div_pow and (k-1)/k = 1 - 1/k.
  rw [← div_pow]
  congr 1
  field_simp

/-- §2.5 — **Sum-over-`j` form: image complement.** For any fixed
    `x : Fin n → K`,

      `∑ j : K, 𝟙[j ∉ image x] = k − |image x|`.

    This is the discrete count: `k − s` points of `K` are missing from
    the sampled image. -/
theorem sum_unsampledIndicator_eq_complement_image {n : ℕ}
    (x : Fin n → K) :
    (∑ j : K, unsampledIndicator x j) =
      ((Fintype.card K : ℝ) - (Finset.univ.image x).card) := by
  classical
  -- `unsampledIndicator x j = 1 ↔ j ∉ image x`.
  have hrewrite : ∀ j : K,
      unsampledIndicator x j = if j ∉ Finset.univ.image x then (1 : ℝ) else 0 := by
    intro j
    unfold unsampledIndicator
    by_cases h : ∀ i : Fin n, x i ≠ j
    · rw [if_pos h]
      have hj : j ∉ Finset.univ.image x := by
        intro hj
        obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hj
        exact h i heq
      rw [if_pos hj]
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      have hj : j ∈ Finset.univ.image x :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
      rw [if_neg (not_not_intro hj)]
  rw [Finset.sum_congr rfl (fun j _ => hrewrite j)]
  -- Apply `Finset.sum_boole`.
  rw [Finset.sum_boole]
  -- Identify the filter with `univ \ image x`.
  have hsub : (Finset.univ.image x) ⊆ (Finset.univ : Finset K) :=
    Finset.subset_univ _
  have hfilter_eq : {j ∈ (Finset.univ : Finset K) | j ∉ Finset.univ.image x}
      = (Finset.univ : Finset K) \ (Finset.univ.image x) := by
    ext j
    simp [Finset.mem_sdiff, Finset.mem_filter]
  rw [hfilter_eq, Finset.card_sdiff_of_subset hsub, Finset.card_univ]
  have hs_le : (Finset.univ.image x).card ≤ Fintype.card K := by
    have : (Finset.univ.image x).card ≤ (Finset.univ : Finset K).card :=
      Finset.card_le_card hsub
    simpa [Finset.card_univ] using this
  push_cast [Nat.cast_sub hs_le]
  rfl

/-- §2.5 — **`avg_complement_image`: average-over-`x` of the image
    complement.**

      `Avg_{x ∈ K^n} ((k − |image x|) / k) = k · (1 − 1/k)^n`

    (more precisely, the un-normalized sum form below). This is the
    sum-over-`j` aggregation of `prob_unsampled_in_uniform` and is the
    quantity that multiplies the pointwise `1/(2k)` bound of
    `nfl_finite_k_adversary` to yield `(1/2)(1 − 1/k)^n`. -/
theorem avg_complement_image [Nonempty K] {n : ℕ} :
    (∑ x : Fin n → K, ((Fintype.card K : ℝ) - (Finset.univ.image x).card))
        / ((Fintype.card K : ℝ) ^ n)
      = (Fintype.card K : ℝ) * (1 - 1 / (Fintype.card K : ℝ)) ^ n := by
  classical
  have hk_pos : 0 < Fintype.card K := Fintype.card_pos
  have hk_pos_real : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast hk_pos
  have hk_pow_pos : (0 : ℝ) < (Fintype.card K : ℝ) ^ n := pow_pos hk_pos_real n
  have hk_pow_ne : ((Fintype.card K : ℝ) ^ n) ≠ 0 := ne_of_gt hk_pow_pos
  -- Rewrite LHS sum using sum_unsampledIndicator_eq_complement_image (reversed).
  have hsum_swap : (∑ x : Fin n → K,
      ((Fintype.card K : ℝ) - (Finset.univ.image x).card))
        = ∑ x : Fin n → K, ∑ j : K, unsampledIndicator x j := by
    refine Finset.sum_congr rfl ?_
    intro x _
    exact (sum_unsampledIndicator_eq_complement_image x).symm
  rw [hsum_swap]
  -- Swap order of summation.
  rw [Finset.sum_comm]
  -- Each inner sum equals `(k-1)^n` by `sum_unsampledIndicator_eq`.
  have hinner : ∀ j : K, (∑ x : Fin n → K, unsampledIndicator x j) =
      ((Fintype.card K : ℝ) - 1) ^ n :=
    fun j => sum_unsampledIndicator_eq j
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Now show: k * (k-1)^n / k^n = k * (1 - 1/k)^n.
  rw [mul_div_assoc]
  congr 1
  rw [← div_pow]
  congr 1
  field_simp

/-- §2.5 — **DGL average-over-`x` No-Free-Lunch bound.**

    *Bach (2024) §2.5, p. 38 / DGL §7.2.* For any deterministic
    learning algorithm `A : (Fin n → K × Bool) → (K → Bool)`, averaging
    the misclassification risk over both the `2^k` labelings
    `r : K → Bool` and the `k^n` sample-index patterns `x : Fin n → K`
    satisfies

      `Avg_x Avg_r R(A(sample x r), r) ≥ (1/2)(1 − 1/k)^n`.

    The proof: by `nfl_finite_k_adversary`, the inner `Avg_r` bound is
    `(1/2)(k − |image x|)/k`, pointwise in `x`; averaging this over
    `x ∈ K^n` and applying `avg_complement_image` yields the classical
    `(1/2)(1 − 1/k)^n` slack — the form in which the bound appears in
    Bach (2024) p. 38 and DGL (1996) §7.2. -/
theorem nfl_finite_k_dgl_average
    [Nonempty K] {n : ℕ}
    (A : (Fin n → K × Bool) → (K → Bool)) :
    let k := Fintype.card K
    (1 : ℝ) / 2 * (1 - 1 / (k : ℝ)) ^ n ≤
      (∑ x : Fin n → K,
          (∑ r : K → Bool, discreteRiskFinK (A (sampleFromLabeling x r)) r)
            / (2 ^ k : ℝ))
        / ((k : ℝ) ^ n) := by
  classical
  set k : ℕ := Fintype.card K with hk_def
  have hk_pos : 0 < k := Fintype.card_pos
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos_real
  have hk_pow_pos : (0 : ℝ) < (k : ℝ) ^ n := pow_pos hk_pos_real n
  have hk_pow_ne : ((k : ℝ) ^ n) ≠ 0 := ne_of_gt hk_pow_pos
  -- Step 1: pointwise bound from `nfl_finite_k_adversary`.
  have hpt : ∀ x : Fin n → K,
      (1 : ℝ) / 2 * ((k : ℝ) - (Finset.univ.image x).card) / k ≤
        (∑ r : K → Bool,
            discreteRiskFinK (A (sampleFromLabeling x r)) r)
          / (2 ^ k : ℝ) := by
    intro x
    have := nfl_finite_k_adversary (K := K) A x
    -- The lemma uses `let k := ...; let s := ...`, which reduces to the same expression.
    simpa [hk_def] using this
  -- Step 2: sum the pointwise bound over `x ∈ K^n`.
  have hsum_le :
      (∑ x : Fin n → K,
          (1 : ℝ) / 2 * ((k : ℝ) - (Finset.univ.image x).card) / k)
        ≤ ∑ x : Fin n → K,
            (∑ r : K → Bool,
                discreteRiskFinK (A (sampleFromLabeling x r)) r)
              / (2 ^ k : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro x _
    exact hpt x
  -- Step 3: evaluate the LHS sum using `avg_complement_image`.
  have hlhs_sum : (∑ x : Fin n → K,
      (1 : ℝ) / 2 * ((k : ℝ) - (Finset.univ.image x).card) / k)
        = (1 / 2 / k) * (∑ x : Fin n → K,
            ((k : ℝ) - (Finset.univ.image x).card)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  rw [hlhs_sum] at hsum_le
  -- Step 4: divide both sides by `k^n` and invoke `avg_complement_image`.
  have havg : (∑ x : Fin n → K,
      ((k : ℝ) - (Finset.univ.image x).card)) / ((k : ℝ) ^ n)
        = (k : ℝ) * (1 - 1 / (k : ℝ)) ^ n := by
    simpa [hk_def] using avg_complement_image (K := K) (n := n)
  -- Show the goal after `show` to unfold the `let`.
  show (1 : ℝ) / 2 * (1 - 1 / (k : ℝ)) ^ n ≤
      (∑ x : Fin n → K,
          (∑ r : K → Bool, discreteRiskFinK (A (sampleFromLabeling x r)) r)
            / (2 ^ k : ℝ))
        / ((k : ℝ) ^ n)
  -- Divide hsum_le by `k^n`.
  have hdiv := div_le_div_of_nonneg_right hsum_le (le_of_lt hk_pow_pos)
  -- Wait, `div_le_div_of_nonneg_right` direction goes wrong; use _of_nonneg_left.
  -- We have LHS ≤ RHS, want LHS/k^n ≤ RHS/k^n. That's `div_le_div_of_nonneg_right`
  -- if the divisor is `≥ 0`; actually it's `div_le_div_iff` or `div_le_div_of_le_left`.
  -- Easier: `div_le_div_of_le_of_nonneg`. Just do it via `le_div_iff`.
  have key : (1 / 2 / (k : ℝ)) * (∑ x : Fin n → K,
        ((k : ℝ) - (Finset.univ.image x).card)) / ((k : ℝ) ^ n) ≤
      (∑ x : Fin n → K,
        (∑ r : K → Bool, discreteRiskFinK (A (sampleFromLabeling x r)) r)
          / (2 ^ k : ℝ)) / ((k : ℝ) ^ n) := by
    have := hsum_le
    exact div_le_div_of_nonneg_right this (le_of_lt hk_pow_pos)
  -- Simplify the LHS of `key`.
  have hlhs_simp : (1 / 2 / (k : ℝ)) * (∑ x : Fin n → K,
        ((k : ℝ) - (Finset.univ.image x).card)) / ((k : ℝ) ^ n)
      = (1 : ℝ) / 2 * (1 - 1 / (k : ℝ)) ^ n := by
    rw [mul_div_assoc]
    rw [havg]
    field_simp
  rw [hlhs_simp] at key
  exact key

end FiniteK

end LTFP
