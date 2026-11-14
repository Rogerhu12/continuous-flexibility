module

public import ContinuousFlexibility.Analysis.N04RealizationEnvelopeDifferential
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
public import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets
public import ContinuousFlexibility.Analysis.N07aCoordinateJetNorms
public import ContinuousFlexibility.Analysis.N07bNormalizedSourceMaterial
public import ContinuousFlexibility.Scalar.WeightedMaterialRadiusJets

/-!
# Actual material scalar jets for primitive geometry

The radius has bounded positive planar jets. The material scale has
bounded jets, and its reciprocal retains an actual pointwise E0 power.
Every jet of a positive power of the material height ratio retains that
same ratio power. The sample height is never estimated separately.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A scalar lift by the first projection does not increase a jet norm. -/
theorem n04Realization_norm_iteratedFDeriv_radialLift_le
    {f : ℝ → ℝ} {y : PolarPoint} (hf : ContDiffAt ℝ ∞ f y.1) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v : PolarPoint => f v.1) y‖ ≤
      |iteratedDeriv n f y.1| := by
  let L : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have h := norm_iteratedFDeriv_comp_linear_le_at L hf n
  have hL : ‖L‖ ^ n ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  have hb := h.trans (mul_le_mul_of_nonneg_left hL
    (norm_nonneg (iteratedFDeriv ℝ n f (L y))))
  simpa only [L, Function.comp_def, ContinuousLinearMap.coe_fst', mul_one,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb

variable {D : ReferenceData} {T : MaterialData}

private theorem n04Realization_materialScalar_contDiff
    (hT : IsMaterialData D T) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b)) :
    ContDiff ℝ ∞ (fun t => f (T.radius t)) := by
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  exact hf.comp_contDiff hr (fun t => (hT.2.2.2.2.2.2.2.1 t).1)

/-- Only positive jets of the unwrapped radius/angle chart are bounded. -/
theorem n04Realization_materialRadius_positive_jets
    (hT : IsMaterialData D T) (n : ℕ) (hn : 0 < n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : PolarPoint,
      ‖iteratedFDeriv ℝ n (n07bMaterialRadiusChart T) y‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := iteratedDeriv_materialRadius_bounded hT n
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  refine ⟨max B 1, hB.trans (le_max_left _ _), fun y => ?_⟩
  have hf : ContDiffAt ℝ n (fun v : PolarPoint => T.radius v.1) y :=
    (hr.contDiffAt.comp y contDiffAt_fst).of_le (by simp)
  have hrad : ‖iteratedFDeriv ℝ n (fun v : PolarPoint => T.radius v.1) y‖ ≤ B :=
    (n04Realization_norm_iteratedFDeriv_radialLift_le hr.contDiffAt n).trans (hb y.1)
  have hang : ‖iteratedFDeriv ℝ n (fun v : PolarPoint => v.2) y‖ ≤ 1 :=
    (n07a_iteratedFDeriv_linear_norm_le (ContinuousLinearMap.snd ℝ ℝ ℝ) hn y).trans
      (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  change ‖iteratedFDeriv ℝ n (fun v : PolarPoint => (T.radius v.1, v.2)) y‖ ≤ _
  rw [iteratedFDeriv_prodMk hf contDiffAt_snd le_rfl, ContinuousMultilinearMap.opNorm_prod]
  exact max_le (hrad.trans (le_max_left _ _)) (hang.trans (le_max_right _ _))

theorem n04Realization_materialEll_jets
    (hT : IsMaterialData D T) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : PolarPoint,
      ‖iteratedFDeriv ℝ n (fun v : PolarPoint => T.ell (T.radius v.1)) y‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := iteratedDeriv_materialEll_bounded hT n
  have hf := n04Realization_materialScalar_contDiff hT (hT.1 T.ell (by simp))
  exact ⟨B, hB, fun y =>
    (n04Realization_norm_iteratedFDeriv_radialLift_le hf.contDiffAt n).trans (hb y.1)⟩

/-- The reciprocal scale uses the given coefficient envelope at the
actual physical point, before any reference sample comparison. -/
theorem n04Realization_materialEllInverse_jets
    (hT : IsMaterialData D T) (n : ℕ) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ y : PolarPoint,
      ‖iteratedFDeriv ℝ n (fun v : PolarPoint => (T.ell (T.radius v.1))⁻¹) y‖ ≤
        B * T.E0 (T.radius y.1) ^ A := by
  obtain ⟨B, hB, hb⟩ := iteratedDeriv_materialEll_inv_bound hT n
  obtain ⟨C, A, hC, hA, hc⟩ := materialEll_inv_le_E0 hT
  have hf : ContDiff ℝ ∞ (fun t => (T.ell (T.radius t))⁻¹) :=
    (n04Realization_materialScalar_contDiff hT (hT.1 T.ell (by simp))).inv
      (fun t => (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 t).1).1.ne')
  refine ⟨B * C, A, mul_nonneg hB hC, hA, fun y => ?_⟩
  calc
    _ ≤ |iteratedDeriv n (fun t => (T.ell (T.radius t))⁻¹) y.1| :=
      n04Realization_norm_iteratedFDeriv_radialLift_le hf.contDiffAt n
    _ ≤ B * (T.ell (T.radius y.1))⁻¹ := hb y.1
    _ ≤ B * (C * T.E0 (T.radius y.1) ^ A) :=
      mul_le_mul_of_nonneg_left (hc _ (hT.2.2.2.2.2.2.2.1 y.1).1) hB
    _ = _ := by ring

/-- All constants precede the sample and the material point. The same
height-ratio power survives differentiation at every finite order. -/
theorem n04Realization_materialHeightRatio_rpow_jets
    (hT : IsMaterialData D T) (γ : ℝ) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 0 < T.H s → ∀ y : PolarPoint,
      ‖iteratedFDeriv ℝ n
        (fun v : PolarPoint => (T.H (T.radius v.1) / T.H s) ^ γ) y‖ ≤
          B * (T.H (T.radius y.1) / T.H s) ^ γ := by
  obtain ⟨B, hB, hb⟩ := iteratedDeriv_materialH_rpow_bound hT γ n
  have hp (t : ℝ) : 0 < T.H (T.radius t) :=
    (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 t).1).2.1
  have hH := n04Realization_materialScalar_contDiff hT (hT.1 T.H (by simp))
  refine ⟨B, hB, fun s hs y => ?_⟩
  have hf : ContDiff ℝ ∞ (fun t => (T.H (T.radius t) / T.H s) ^ γ) :=
    (hH.div contDiff_const (fun _ => hs.ne')).rpow_const_of_ne
      (fun t => (div_pos (hp t) hs).ne')
  have heq : (fun t => (T.H (T.radius t) / T.H s) ^ γ) =
      (fun t => T.H (T.radius t) ^ γ * (T.H s ^ γ)⁻¹) := by
    funext t
    rw [Real.div_rpow (hp t).le hs.le, div_eq_mul_inv]
  have hscalar : |iteratedDeriv n (fun t => (T.H (T.radius t) / T.H s) ^ γ) y.1| ≤
      B * (T.H (T.radius y.1) / T.H s) ^ γ := by
    rw [heq, iteratedDeriv_mul_const_field, abs_mul,
      abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos hs γ))]
    calc
      _ ≤ (B * T.H (T.radius y.1) ^ γ) * (T.H s ^ γ)⁻¹ :=
        mul_le_mul_of_nonneg_right (hb y.1)
          (inv_nonneg.mpr (Real.rpow_nonneg hs.le γ))
      _ = _ := by
        rw [Real.div_rpow (hp y.1).le hs.le, div_eq_mul_inv]
        ring
  exact (n04Realization_norm_iteratedFDeriv_radialLift_le hf.contDiffAt n).trans hscalar

/-- Positive real powers preserve the existing scalar envelope. -/
theorem n04Realization_envelope_rpow
    {X : Type*} {W F : X → ℝ} (hW : ∀ x, 1 ≤ W x)
    (hF : HasPositiveEnvelope W F) (hF₀ : ∀ x, 0 ≤ F x)
    {γ : ℝ} (hγ : 0 < γ) : HasPositiveEnvelope W (fun x => F x ^ γ) := by
  obtain ⟨C, A, hC, hA, hb⟩ := hF
  refine ⟨C ^ γ, A * γ, Real.rpow_pos_of_pos hC _, mul_pos hA hγ, fun x => ?_⟩
  have h := Real.rpow_le_rpow (hF₀ x) (hb x) hγ.le
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg (zero_le_one.trans (hW x)) _),
    ← Real.rpow_mul (zero_le_one.trans (hW x))] at h
  exact h

/-- The actual pointwise E0 input can be enlarged to any chosen common
coefficient/state base. No material cell is reassigned. -/
theorem n04Realization_materialEllInverse_envelope
    {X : Type*} (hT : IsMaterialData D T) {W : X → ℝ}
    (hW : ∀ x, 1 ≤ W x) (p : X → PolarPoint)
    (hE : ∀ x, T.E0 (T.radius (p x).1) ≤ W x) (n : ℕ) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n
        (fun v : PolarPoint => (T.ell (T.radius v.1))⁻¹) (p x)‖) := by
  obtain ⟨B, A, hB, hA, hb⟩ := n04Realization_materialEllInverse_jets hT n
  obtain ⟨C, hC, hpack⟩ := coefficientEnvelope_pack B A
  refine ⟨C, C, hC, hC, fun x => (hb (p x)).trans ?_⟩
  have he : 0 ≤ T.E0 (T.radius (p x).1) :=
    (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 (p x).1).1).2.2.1.le
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow he (hE x) hA) hB).trans
    (hpack (W x) (hW x))

/-- A value envelope for the actual height ratio controls all of its
positive-power jets, with the original sample kept fixed in each field. -/
theorem n04Realization_materialHeightRatio_envelope
    {X : Type*} (hT : IsMaterialData D T) {W : X → ℝ}
    (hW : ∀ x, 1 ≤ W x) (p : X → PolarPoint) (sample : X → ℝ)
    (hsample : ∀ x, 0 < T.H (sample x))
    (hRatio : HasPositiveEnvelope W
      (fun x => T.H (T.radius (p x).1) / T.H (sample x)))
    {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n
        (fun v : PolarPoint => (T.H (T.radius v.1) / T.H (sample x)) ^ γ) (p x)‖) := by
  obtain ⟨B, _, hb⟩ := n04Realization_materialHeightRatio_rpow_jets hT γ n
  have hratio₀ (x : X) : 0 ≤ T.H (T.radius (p x).1) / T.H (sample x) :=
    (div_pos (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 (p x).1).1).2.1 (hsample x)).le
  have hp := n04Realization_envelope_rpow hW hRatio hratio₀ hγ
  exact ((hasPositiveEnvelope_const W hW B).mul hW hp
    (fun x => Real.rpow_nonneg (hratio₀ x) γ)).mono
      (fun x => hb (sample x) (hsample x) (p x))

end ContinuousFlexibility.Analysis
