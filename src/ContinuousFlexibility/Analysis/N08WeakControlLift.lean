import ContinuousFlexibility.Analysis.N08WeakControlHeightBounds
import ContinuousFlexibility.Analysis.N08RadialFamilyLift

/-!
# The actual smoothing map from weak controls to weighted heights

The constructed continuous linear map realizes the literal optical-control
series. Every output grading is bounded by the same weak input norm, and
restricting a physical circle control recovers its original profile sum.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n08WeakControlRadialCLM (T : MaterialData)
    (hC : controlGeometryConditions D S C) : ControlBanach →L[ℝ] (ℝ → ℝ) :=
  ContinuousLinearMap.pi (fun r => n08WeakControlEvalCLM T hC r)

theorem n08WeakControlRadialCLM_apply (hC : controlGeometryConditions D S C)
    (u : ControlBanach) :
    n08WeakControlRadialCLM T hC u = n08WeakControlProfile T C u :=
  funext fun r => n08WeakControlEvalCLM_apply hC u r

private theorem n08_weakRadialCLM_smooth (hC : controlGeometryConditions D S C)
    (u : ControlBanach) :
    ContDiffOn ℝ ∞ (n08WeakControlRadialCLM T hC u) (Ioo D.a D.b) := by
  rw [n08WeakControlRadialCLM_apply]
  exact n08WeakControlProfile_contDiffOn hC u

private theorem n08_weakRadialCLM_zero (hC : controlGeometryConditions D S C)
    (u : ControlBanach) (r : ℝ) (hr : r ∉ Ioo D.a D.b) :
    n08WeakControlRadialCLM T hC u r = 0 := by
  rw [n08WeakControlRadialCLM_apply]
  exact n08ControlSeries_zero_off_core hC _ hr

private theorem n08_weakRadialCLM_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ControlBanach, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (n08WeakControlRadialCLM T hN.2.2.2.1 u) r| ≤
        K * ‖u‖ * T.H r ^ (3 / 128 : ℝ) * T.M r := by
  simpa only [n08WeakControlRadialCLM_apply] using n08WeakControlProfile_jet_bound hT hS hN s

def n08WeakControlLift
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ControlBanach →L[ℝ] (S.height n08WeakControlWeight).Space :=
  n08RadialFamilyLift hT (hS.1 n08WeakControlWeight)
    (n08WeakControlRadialCLM T hN.2.2.2.1)
    (n08_weakRadialCLM_smooth hN.2.2.2.1)
    (n08_weakRadialCLM_zero hN.2.2.2.1) (n08_weakRadialCLM_bound hT hS hN)

theorem n08WeakControlLift_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (u : ControlBanach) (p : PolarPoint) :
    (S.height n08WeakControlWeight).decode (n08WeakControlLift hT hS hN u) p =
      n08WeakControlProfile T C u p.1 := by
  rw [n08WeakControlLift, n08RadialFamilyLift_decode, n08WeakControlRadialCLM_apply]

theorem n08WeakControlLift_grading_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ControlBanach,
      (S.height n08WeakControlWeight).grading s (n08WeakControlLift hT hS hN u) ≤ K * ‖u‖ :=
  n08RadialFamilyLift_grading_bound hT (hS.1 n08WeakControlWeight)
    (n08WeakControlRadialCLM T hN.2.2.2.1)
    (n08_weakRadialCLM_smooth hN.2.2.2.1)
    (n08_weakRadialCLM_zero hN.2.2.2.1) (n08_weakRadialCLM_bound hT hS hN) s

theorem n08WeakControlLift_isTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    IsTameLinear (fun _ : ℕ => normSeminorm ℝ ControlBanach)
      (S.height n08WeakControlWeight).grading (n08WeakControlLift hT hS hN).toLinearMap 0 0 :=
  n08RadialFamilyLift_isTame hT (hS.1 n08WeakControlWeight)
    (n08WeakControlRadialCLM T hN.2.2.2.1)
    (n08_weakRadialCLM_smooth hN.2.2.2.1)
    (n08_weakRadialCLM_zero hN.2.2.2.1) (n08_weakRadialCLM_bound hT hS hN)

theorem n08WeakControlLift_restriction_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) (p : PolarPoint) :
    (S.height n08WeakControlWeight).decode
      (n08WeakControlLift hT hS hN (n08ControlRestriction S x.2.2.1)) p =
        stateControlSum C x p.1 := by
  rw [n08WeakControlLift_decode, n08WeakControlProfile_restriction hN.1.1 hT hS]

end ContinuousFlexibility.Statements
