module

public import ContinuousFlexibility.Analysis.N08NuProfileBounds
public import ContinuousFlexibility.Analysis.N08RadialFamilyLift

/-! # Actual weighted realization of the scalar logarithmic direction -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n08ChiRadialCLM (D : ReferenceData) : ℝ →L[ℝ] (ℝ → ℝ) :=
  ContinuousLinearMap.pi (fun r => (ContinuousLinearMap.id ℝ ℝ).smulRight (D.chi r))

theorem n08ChiRadialCLM_apply (D : ReferenceData) (a r : ℝ) :
    n08ChiRadialCLM D a r = a * D.chi r := rfl

private theorem n08_chiRadialCLM_smooth
    (hN : N01Properties D T S C base loss ε) (a : ℝ) :
    ContDiffOn ℝ ∞ (n08ChiRadialCLM D a) (Ioo D.a D.b) :=
  (contDiff_const.mul hN.1.2.2.2.1.1).contDiffOn

private theorem n08_chiRadialCLM_zero
    (hN : N01Properties D T S C base loss ε)
    (a r : ℝ) (hr : r ∉ Ioo D.a D.b) : n08ChiRadialCLM D a r = 0 := by
  rw [n08ChiRadialCLM_apply]
  have hchi : D.chi r = 0 := by
    by_contra h
    exact hr ((hN.1.2.2.2.1.support_subset h).1)
  rw [hchi, mul_zero]

private theorem n08_chiRadialCLM_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℝ, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (n08ChiRadialCLM D a) r| ≤
        K * ‖a‖ * T.H r ^ (3 / 128 : ℝ) * T.M r :=
  n08_chi_decay_jet_bound hT hS hN s

def n08NuProfileLift
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ℝ →L[ℝ] (S.height n08WeakControlWeight).Space :=
  n08RadialFamilyLift hT (hS.1 n08WeakControlWeight) (n08ChiRadialCLM D)
    (n08_chiRadialCLM_smooth hN) (n08_chiRadialCLM_zero hN)
    (n08_chiRadialCLM_bound hT hS hN)

theorem n08NuProfileLift_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (a : ℝ) (p : PolarPoint) :
    (S.height n08WeakControlWeight).decode (n08NuProfileLift hT hS hN a) p =
      a * D.chi p.1 :=
  n08RadialFamilyLift_decode hT (hS.1 n08WeakControlWeight) (n08ChiRadialCLM D)
    (n08_chiRadialCLM_smooth hN) (n08_chiRadialCLM_zero hN)
    (n08_chiRadialCLM_bound hT hS hN) a p

theorem n08NuProfileLift_grading_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℝ,
      (S.height n08WeakControlWeight).grading s (n08NuProfileLift hT hS hN a) ≤ K * ‖a‖ :=
  n08RadialFamilyLift_grading_bound hT (hS.1 n08WeakControlWeight) (n08ChiRadialCLM D)
    (n08_chiRadialCLM_smooth hN) (n08_chiRadialCLM_zero hN)
    (n08_chiRadialCLM_bound hT hS hN) s

end ContinuousFlexibility.Statements
