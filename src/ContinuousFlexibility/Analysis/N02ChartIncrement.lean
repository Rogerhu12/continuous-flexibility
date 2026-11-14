module

public import ContinuousFlexibility.Analysis.CircleCompositionModel
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# The actual chart increment in the physical circle model

Composition with the decoded left chart defines the linear increment
required by N02 at every state. It retains the odd sector whenever the
state chart is odd, and its fixed-chart operator has one level of loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def actualChartIncrement (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (z : AnnularState S × ℝ) : CircleSpace S →ₗ[ℝ] CircleSpace S :=
  circleChartComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hD
    (by norm_num : (0 : ℝ) < 3 / 4) z.1.2.2.2

theorem actualChartIncrement_decode (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (z : AnnularState S × ℝ) (v : CircleSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (actualChartIncrement hS hT hD z v) m θ =
      (S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m θ) :=
  circleChartComposeLinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hD
    (by norm_num : (0 : ℝ) < 3 / 4) z.1.2.2.2 v m θ

theorem actualChartIncrement_isOdd (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (z : AnnularState S × ℝ) (hz : stateSector S z.1)
    (v : CircleSpace S) (hv : IsOddCircle S v) :
    IsOddCircle S (actualChartIncrement hS hT hD z v) := by
  intro m θ
  have hodd : stateLeftChart S z.1 m (-θ) = -stateLeftChart S z.1 m θ := by
    simp only [stateLeftChart, hz.2 m θ]
    ring
  simp only [actualChartIncrement_decode, hodd]
  exact hv m (stateLeftChart S z.1 m θ)

theorem actualChartIncrement_isTame (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (z : AnnularState S × ℝ) :
    IsTameLinear (S.circle (3 / 4 : ℝ)).grading
      (S.circle (3 / 4 : ℝ)).grading (actualChartIncrement hS hT hD z) 1 0 :=
  circleChartComposeLinear_isTame (hS.2.1 (3 / 4 : ℝ)) hT hD
    (by norm_num : (0 : ℝ) < 3 / 4) z.1.2.2.2

end ContinuousFlexibility.Statements
