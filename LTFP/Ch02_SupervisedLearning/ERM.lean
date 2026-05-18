/-
LTFP §2.3.2 — Empirical risk and the empirical risk minimizer (ERM).

Bach (2024) §2.3.2, p. 32-33.

Given an i.i.d. sample of size `n`, the empirical risk averages the loss
over the sample. ERM is any element of the hypothesis class that achieves
the empirical-risk minimum on that sample.
-/
import LTFP.Ch02_SupervisedLearning.Defs

namespace LTFP

variable {𝒳 𝒴 𝒵 : Type*}

/-- §2.3.2 — Empirical risk `R̂_n(f) = (1/n) ∑ᵢ ℓ(f(xᵢ), yᵢ)` over a
    finite sample `S : Fin n → 𝒳 × 𝒴`. -/
noncomputable def empiricalRisk
    (ℓ : LossFunction 𝒴 𝒵) (n : ℕ) (S : Fin n → 𝒳 × 𝒴) (f : 𝒳 → 𝒵) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ℓ (f (S i).1) (S i).2

/-- §2.3.2 — `ERM ℓ H n S fhat` says `fhat` is a member of the hypothesis
    class `H` that minimizes the empirical risk on `S`. -/
def ERM
    (ℓ : LossFunction 𝒴 𝒵) (H : Set (𝒳 → 𝒵))
    (n : ℕ) (S : Fin n → 𝒳 × 𝒴) (fhat : 𝒳 → 𝒵) : Prop :=
  fhat ∈ H ∧ ∀ f ∈ H, empiricalRisk ℓ n S fhat ≤ empiricalRisk ℓ n S f

/-- §2.3.2 — Empirical risk on an empty sample is zero. -/
theorem empiricalRisk_zero_sample (ℓ : LossFunction 𝒴 𝒵)
    (S : Fin 0 → 𝒳 × 𝒴) (f : 𝒳 → 𝒵) :
    empiricalRisk ℓ 0 S f = 0 := by
  unfold empiricalRisk
  simp

/-- §2.3.2 — ERM membership: an ERM is a member of the hypothesis class. -/
theorem ERM.mem {ℓ : LossFunction 𝒴 𝒵} {H : Set (𝒳 → 𝒵)} {n : ℕ}
    {S : Fin n → 𝒳 × 𝒴} {fhat : 𝒳 → 𝒵} (h : ERM ℓ H n S fhat) :
    fhat ∈ H := h.1

/-- §2.3.2 — ERM optimality: empirical risk of fhat is ≤ that of any
    other f in H. -/
theorem ERM.optimal {ℓ : LossFunction 𝒴 𝒵} {H : Set (𝒳 → 𝒵)} {n : ℕ}
    {S : Fin n → 𝒳 × 𝒴} {fhat : 𝒳 → 𝒵} (h : ERM ℓ H n S fhat)
    {f : 𝒳 → 𝒵} (hf : f ∈ H) :
    empiricalRisk ℓ n S fhat ≤ empiricalRisk ℓ n S f := h.2 f hf

/-- §2.3.2 — Empirical risk of a nonneg loss is nonneg. -/
theorem empiricalRisk_nonneg {ℓ : LossFunction 𝒴 𝒵}
    (hℓ : ∀ z y, 0 ≤ ℓ z y) (n : ℕ) (S : Fin n → 𝒳 × 𝒴) (f : 𝒳 → 𝒵)
    (hn : 0 ≤ (n : ℝ)) :
    0 ≤ empiricalRisk ℓ n S f := by
  unfold empiricalRisk
  apply mul_nonneg (inv_nonneg.mpr hn)
  exact Finset.sum_nonneg (fun i _ => hℓ _ _)

/-- §2.3.2 — Empirical risk on a sample where every prediction is
    correct (zero loss) equals zero. -/
theorem empiricalRisk_zero_loss {ℓ : LossFunction 𝒴 𝒵} (n : ℕ)
    (S : Fin n → 𝒳 × 𝒴) (f : 𝒳 → 𝒵)
    (hzero : ∀ i, ℓ (f (S i).1) (S i).2 = 0) :
    empiricalRisk ℓ n S f = 0 := by
  unfold empiricalRisk
  rw [show (∑ i, ℓ (f (S i).1) (S i).2) = 0 from by
    refine Finset.sum_eq_zero (fun i _ => hzero i)]
  ring

/-- §2.3.2 — If `f₁` pointwise has higher loss than `f₂` on every
    sample point, then `f₁` has higher empirical risk than `f₂`. -/
theorem empiricalRisk_mono_pointwise {ℓ : LossFunction 𝒴 𝒵} (n : ℕ)
    (S : Fin n → 𝒳 × 𝒴) (f₁ f₂ : 𝒳 → 𝒵) (hn : 0 ≤ (n : ℝ))
    (h : ∀ i, ℓ (f₁ (S i).1) (S i).2 ≤ ℓ (f₂ (S i).1) (S i).2) :
    empiricalRisk ℓ n S f₁ ≤ empiricalRisk ℓ n S f₂ := by
  unfold empiricalRisk
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn)
  exact Finset.sum_le_sum (fun i _ => h i)

/-- §2.3.2 — **Empirical risk is bounded by the pointwise loss
    supremum.** If `ℓ(f(xᵢ), yᵢ) ≤ M` on every sample point and the
    sample is nonempty, then `R̂_n(f) ≤ M`. This is the empirical
    counterpart of "bounded loss ⇒ bounded risk" and is the workhorse
    of Hoeffding-style concentration arguments (Bach 2024, §2.3.2 and
    §3.1 build on this directly). -/
theorem empiricalRisk_le_of_loss_le {ℓ : LossFunction 𝒴 𝒵} {n : ℕ}
    (hn : 0 < n) (S : Fin n → 𝒳 × 𝒴) (f : 𝒳 → 𝒵) {M : ℝ}
    (h : ∀ i, ℓ (f (S i).1) (S i).2 ≤ M) :
    empiricalRisk ℓ n S f ≤ M := by
  unfold empiricalRisk
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsum : ∑ i, ℓ (f (S i).1) (S i).2 ≤ ∑ _i : Fin n, M :=
    Finset.sum_le_sum (fun i _ => h i)
  have hsum_const : (∑ _i : Fin n, M) = (n : ℝ) * M := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [hsum_const] at hsum
  calc (n : ℝ)⁻¹ * ∑ i, ℓ (f (S i).1) (S i).2
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (le_of_lt hn_pos))
    _ = M := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hn_pos), one_mul]

/-- §2.3.2 — **ERMs are unique up to empirical risk.** If `fhat₁` and
    `fhat₂` are both empirical-risk minimizers over the same `H` and
    sample `S`, they realize the same empirical risk. The ERM
    *minimum value* is well-defined even when the *argmin* is not
    (Bach 2024, §2.3.2 — analogous to `bayesPredictor_unique_risk`). -/
theorem ERM.unique_risk
    {ℓ : LossFunction 𝒴 𝒵} {H : Set (𝒳 → 𝒵)} {n : ℕ}
    {S : Fin n → 𝒳 × 𝒴} {fhat₁ fhat₂ : 𝒳 → 𝒵}
    (h₁ : ERM ℓ H n S fhat₁) (h₂ : ERM ℓ H n S fhat₂) :
    empiricalRisk ℓ n S fhat₁ = empiricalRisk ℓ n S fhat₂ :=
  le_antisymm (h₁.2 fhat₂ h₂.1) (h₂.2 fhat₁ h₁.1)

end LTFP
