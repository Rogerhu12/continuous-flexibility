module

public import ContinuousFlexibility.Analysis.N01aOpticalPeak
public import ContinuousFlexibility.Analysis.N01aOpticalJetBounds

/-!
# Normalization of the actual optical travel control

The normalization is a scalar multiplication of the constructed control.
Its derivative is proved for the original logarithmically perturbed
profile by the one-variable chain rule, without replacing the travel map
by its linearization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_opticalTravel_const_mul_control {w χ : ℝ → ℝ} {l h d : ℝ}
    (hd : HasDerivAt (fun t => opticalTravel (opticalLogPerturbation w χ t) l h) d 0)
    (c : ℝ) :
    HasDerivAt
      (fun t => opticalTravel (opticalLogPerturbation w (fun r => c * χ r) t) l h)
      (d * c) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => t * c) c 0 := by
    simpa only [one_mul, id_eq] using (hasDerivAt_id (0 : ℝ)).mul_const c
  have heq :
      (fun t => opticalTravel (opticalLogPerturbation w (fun r => c * χ r) t) l h) =
      (fun t => opticalTravel (opticalLogPerturbation w χ t) l h) ∘ (fun t => t * c) := by
    funext t
    change opticalTravel (opticalLogPerturbation w (fun r => c * χ r) t) l h =
      opticalTravel (opticalLogPerturbation w χ (t * c)) l h
    apply congrArg (fun v => opticalTravel v l h)
    funext r
    simp only [opticalLogPerturbation, mul_assoc]
  rw [heq]
  exact hd.comp_of_eq 0 hlin (by simp only [zero_mul])

def n01aOpticalNormalizer (w : ℝ → ℝ) (l h δ : ℝ) : ℝ :=
  -2 / (∫ r in l..h, n01aOpticalKernel w δ r)

def n01aOpticalControl (w : ℝ → ℝ) (l h δ r : ℝ) : ℝ :=
  n01aOpticalNormalizer w l h δ * n01aOpticalRawControl w l h δ r

theorem contDiff_n01aOpticalControl {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) :
    ContDiff ℝ ∞ (n01aOpticalControl w l h δ) := by
  change ContDiff ℝ ∞ (fun r =>
    n01aOpticalNormalizer w l h δ * n01aOpticalRawControl w l h δ r)
  exact contDiff_const.mul
    (contDiff_n01aOpticalRawControl hl hδ hw hpos hrootL hrootR)

theorem tsupport_n01aOpticalControl_subset {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) :
    tsupport (n01aOpticalControl w l h δ) ⊆ Ioo l h :=
  tsupport_mul_subset_right.trans
    (tsupport_n01aOpticalRawControl_subset hl hδ hw hpos hrootL hrootR)

theorem hasCompactSupport_n01aOpticalControl {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) :
    HasCompactSupport (n01aOpticalControl w l h δ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_n01aOpticalControl_subset hl hδ hw hpos hrootL hrootR).trans
      Ioo_subset_Icc_self)

theorem hasDerivAt_n01aOpticalControl_travel {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hlh : l < h) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0)
    (hkernel : 0 < ∫ r in l..h, n01aOpticalKernel w δ r) :
    HasDerivAt (fun t => opticalTravel
      (opticalLogPerturbation w (n01aOpticalControl w l h δ) t) l h) 1 0 := by
  have hd := hasDerivAt_opticalTravel_const_mul_control
    (hasDerivAt_n01aOpticalRawControl_travel hl hlh hδ hw hpos hneg hrootL hrootR)
    (n01aOpticalNormalizer w l h δ)
  have hnormalize :
      (-(1 / 2 : ℝ) * ∫ r in l..h, n01aOpticalKernel w δ r) *
        n01aOpticalNormalizer w l h δ = 1 := by
    dsimp only [n01aOpticalNormalizer]
    field_simp [hkernel.ne']
    <;> ring
  change HasDerivAt (fun t => opticalTravel
    (opticalLogPerturbation w
      (fun r => n01aOpticalNormalizer w l h δ * n01aOpticalRawControl w l h δ r) t)
    l h) 1 0
  simpa only [hnormalize] using hd

/-- Positivity and a reciprocal bound follow from the actual peak interval. -/
theorem n01aOpticalNormalizer_bound {w : ℝ → ℝ} {l h δ K β p : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hK : 0 < K) (hhβ : h ≤ β)
    (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0)
    (hbound : ∀ r ∈ Icc l h, |deriv (n01aOpticalRadicand w) r| ≤ K)
    (hupper : ∀ r ∈ Icc l h, n01aOpticalRadicand w r ≤ K ^ 2)
    (hp : p ∈ Icc l h) (hpeak : 4 * δ ≤ n01aOpticalRadicand w p) :
    0 < (∫ r in l..h, n01aOpticalKernel w δ r) ∧
      |n01aOpticalNormalizer w l h δ| ≤ β * K ^ 2 / δ := by
  have hlo := n01aOpticalRawControl_variation_lower hl hδ hK hhβ hw hpos
    hrootL hrootR hbound hupper hp hpeak
  have hβ : 0 < β := (hl.trans_le (hp.1.trans hp.2)).trans_le hhβ
  have hsmall : 0 < δ / (β * K ^ 2) := div_pos hδ (mul_pos hβ (sq_pos_of_pos hK))
  have hkernel : 0 < ∫ r in l..h, n01aOpticalKernel w δ r := by
    have hhalf := hsmall.trans_le hlo
    linarith
  refine ⟨hkernel, ?_⟩
  have hinv := one_div_le_one_div_of_le hsmall hlo
  have hleft :
      1 / ((1 / 2 : ℝ) * ∫ r in l..h, n01aOpticalKernel w δ r) =
        |n01aOpticalNormalizer w l h δ| := by
    rw [n01aOpticalNormalizer, abs_div, abs_of_pos hkernel]
    rw [show |(-2 : ℝ)| = 2 by norm_num]
    field_simp [hkernel.ne']
  have hright : 1 / (δ / (β * K ^ 2)) = β * K ^ 2 / δ := by
    field_simp [hβ.ne', hK.ne', hδ.ne']
  simpa only [hleft, hright] using hinv

theorem iteratedDeriv_n01aOpticalControl (w : ℝ → ℝ) (l h δ : ℝ) (s : ℕ) (r : ℝ) :
    iteratedDeriv s (n01aOpticalControl w l h δ) r =
      n01aOpticalNormalizer w l h δ * iteratedDeriv s (n01aOpticalRawControl w l h δ) r :=
  iteratedDeriv_const_mul_field _ _

end ContinuousFlexibility.Statements
