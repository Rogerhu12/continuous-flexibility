module

public import ContinuousFlexibility.Radial.InnerBufferLocalizedConstruction
public import ContinuousFlexibility.Radial.InnerLocalizedWeights

/-!
# Actual weighted Poisson columns from compression

The inverse and all the column data in this file are those of one
InnerBufferLocalizedData. The localized leading term sees the constant
cut weight, whereas the inverse applied to its commutator only pays the
weight ratio inside its own retained model interval. The scalar estimate
uses that same inverse, so the temporary central border is included.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped InnerProductSpace

variable {B : BufferData} {C K : ℝ} (M : InnerBufferLocalizedData B C K)

/-- The actual remainder before taking its function and scalar coordinates. -/
def InnerBufferLocalizedData.remainder (i : Fin 2) : RadialL2 × ℝ :=
  M.dirichlet ((M.column i).forcing, 0)

theorem InnerBufferLocalizedData.remainder_norm_bound (i : Fin 2) :
    ‖M.remainder i‖ ≤
      (B.B₀ + C * ∑ k, (B.mass k)⁻¹ ^ 2) *
        (K * (1 + B.layerBound) * B.mass i ^ (3 / 2 : ℝ) * exp (-B.action i)) := by
  have hG : 0 ≤ B.B₀ + C * ∑ k, (B.mass k)⁻¹ ^ 2 :=
    (norm_nonneg M.dirichlet).trans M.dirichlet_bound
  calc
    ‖M.remainder i‖ ≤ ‖M.dirichlet‖ * ‖((M.column i).forcing, (0 : ℝ))‖ :=
      M.dirichlet.le_opNorm _
    _ = ‖M.dirichlet‖ * ‖(M.column i).forcing‖ := by
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
    _ ≤ _ := mul_le_mul M.dirichlet_bound (M.column i).forcing_bound (norm_nonneg _) hG

theorem InnerBufferLocalizedData.column_decomposition (i : Fin 2) :
    (M.column i).field = (M.column i).leading - (M.remainder i).1 ∧
      (M.column i).scalar = -(M.remainder i).2 := by
  have hf := congrArg Prod.fst (M.column i).decomposition
  have hs := congrArg Prod.snd (M.column i).decomposition
  exact ⟨hf, by simpa only [InnerBufferLocalizedData.remainder, Prod.snd_sub, zero_sub] using hs⟩

theorem InnerBufferLocalizedData.remainder_supported (i : Fin 2) :
    ∀ᵐ x ∂volume, x ∉ Ioo B.l B.h → (M.remainder i).1 x = 0 := by
  have heq : (M.remainder i).1 = (M.column i).leading - (M.column i).field := by
    rw [(M.column_decomposition i).1]
    abel
  rw [heq]
  filter_upwards [Lp.coeFn_sub (M.column i).leading (M.column i).field,
    (M.column i).leading_ae, (M.column i).field_ae] with x hsub hL hp
  intro hx
  rw [hsub, Pi.sub_apply, hL, hp, indicator_of_notMem hx,
    indicator_of_notMem hx, sub_self]

/-- The same exponential remainder controls the scalar coordinate. -/
theorem InnerBufferLocalizedData.scalar_bound (i : Fin 2) :
    |(M.column i).scalar| ≤
      (B.B₀ + C * ∑ k, (B.mass k)⁻¹ ^ 2) *
        (K * (1 + B.layerBound) * B.mass i ^ (3 / 2 : ℝ) * exp (-B.action i)) := by
  rw [(M.column_decomposition i).2, abs_neg, ← Real.norm_eq_abs]
  apply le_trans _ (M.remainder_norm_bound i)
  rw [Prod.norm_def]
  exact le_max_right _ _

/-- This is a norm bound for the actual compressed Poisson column after
multiplication by an actual measurable model-coordinate weight. -/
theorem InnerBufferLocalizedData.weighted_column_bound
    (hB : BufferHypotheses B) (i : Fin 2)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ x, |W x| ≤ CW)
    {R w : ℝ} (hR : 0 ≤ R) (hw : 0 < w)
    (hbuffer : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i), W x = w)
    (hcell : ∀ x ∈ Ioo B.l B.h, |W x| ≤ R * w) :
    ‖innerWeightMultiplier volume W hW CW hWC (M.column i).field‖ ≤
      w * (sqrt (M.column i).inwardEnergy / B.mass i) +
        (R * w) * ((B.B₀ + C * ∑ k, (B.mass k)⁻¹ ^ 2) *
          (K * (1 + B.layerBound) * B.mass i ^ (3 / 2 : ℝ) * exp (-B.action i))) := by
  have hsupport := (innerBufferLeading_point_support hB i (M.column i).pin
    (M.column i).leading (M.column i).leading_ae).2
  have hlocal := innerWeightMultiplier_local_decomposition_bound volume W hW CW hWC
    (Ioo B.l B.h) (uIcc (bufferCut B i) (bufferInnerWall B i))
    (M.column i).field (M.column i).leading (M.remainder i).1
    (M.column_decomposition i).1 hsupport (M.remainder_supported i) w hbuffer hcell
  rw [abs_of_pos hw] at hlocal
  apply hlocal.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (M.column i).leading_bound hw.le
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hR hw.le)
    apply le_trans _ (M.remainder_norm_bound i)
    rw [Prod.norm_def]
    exact le_max_left _ _

end ContinuousFlexibility.Radial
