import ContinuousFlexibility.Analysis.N07aSmoothLocalCoordinates

/-!
# The tubular coordinate map has the actual inverse-chart differential

The angular curve contributes the angular column. The fixed transverse
vector contributes the radial column, so their sum is the original
derivative at the chosen point of the cut.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

theorem n07a_tubularMap_hasFDerivAt
    {G : PolarPoint → PolarPoint} {R θ₀ : ℝ}
    (hG : DifferentiableAt ℝ G (R, θ₀)) :
    HasFDerivAt
      (fun p : PolarPoint => G (R, p.2) +
        (p.1 - R) • fderiv ℝ G (R, θ₀) (1, 0))
      (fderiv ℝ G (R, θ₀)) (R, θ₀) := by
  let A : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ G (R, θ₀)
  let Q : PolarPoint →L[ℝ] PolarPoint :=
    (0 : PolarPoint →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hQ : HasFDerivAt (fun p : PolarPoint => (R, p.2)) Q (R, θ₀) :=
    (hasFDerivAt_const R (R, θ₀)).prodMk hasFDerivAt_snd
  have hR : HasFDerivAt (fun p : PolarPoint => (p.1 - R) • A (1, 0))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (A (1, 0))) (R, θ₀) :=
    (hasFDerivAt_fst.sub_const R).smul_const (A (1, 0))
  have hder : A.comp Q + (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (A (1, 0)) = A := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [Q, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst']
    rw [← map_smul, ← map_add]
    congr 1
    ext <;> simp
  exact ((hG.hasFDerivAt.comp (R, θ₀) hQ).add hR).congr_fderiv hder

end ContinuousFlexibility.Analysis
