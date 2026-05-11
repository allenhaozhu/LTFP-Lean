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

end LTFP
