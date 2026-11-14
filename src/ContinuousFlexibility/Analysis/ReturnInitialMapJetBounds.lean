module

public import ContinuousFlexibility.Analysis.ReturnChartUniformBounds
public import ContinuousFlexibility.Analysis.ReturnCorrectionSmallness

/-!
# All angular jets of the actual initial displacement

The zeroth N01 flow tower bounds the actual flow difference uniformly,
including the return radii by continuity. Together with the decoded left
chart this bounds `K-id`. Thus adding its zeroth order to the positive
chart jets requires no N02 realization or additional boundedness premise.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance returnInitialMapJetBoundsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

theorem N01Properties.minusFlow_reference_difference_uniform_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      |C.minusFlow z m r θ - C.minusFlow (C.referenceState, 0) m r θ| ≤ A := by
  obtain ⟨A, hA, hbound⟩ := hN.ordinaryFlowFamily_angular_uniform_bound hT hz 0
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hz₀ : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · have hzero : stateGrading S base (C.referenceState - C.referenceState) = 0 :=
        (congrArg (fun v : AnnularState S => stateGrading S base v)
          (sub_self C.referenceState)).trans (stateGrading S base).map_zero'
      exact hzero.trans_lt hN.2.1
    · simpa only [abs_zero] using hN.2.1
  refine ⟨A, hA, ?_⟩
  intro m r hr θ
  have hi : ∀ s ∈ Ioo (C.left m) (C.right m),
      |C.minusFlow z m s θ - C.minusFlow (C.referenceState, 0) m s θ| ≤ A := by
    intro s hs
    simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero] using
      hbound m s hs θ
  have hc : ContinuousOn (fun s => |C.minusFlow z m s θ -
      C.minusFlow (C.referenceState, 0) m s θ|) (Icc (C.left m) (C.right m)) :=
    ((hflow z hz m θ).2.1.sub (hflow _ hz₀ m θ).2.1).abs
  have hclosure : closure (Ioo (C.left m) (C.right m)) = Icc (C.left m) (C.right m) :=
    closure_Ioo (hC.1 m).2.1.ne
  exact le_on_closure hi (by simpa only [hclosure] using hc) continuousOn_const
    (by simpa only [hclosure] using hr)

theorem N01Properties.returnCorrectionInitialMap_sub_id_uniform_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ, |returnCorrectionInitialMap S C z m θ - θ| ≤ A := by
  obtain ⟨A, hA, hflow⟩ := hN.minusFlow_reference_difference_uniform_bound hT hz
  obtain ⟨K, hK, hweight⟩ := materialSample_H_E0_envelope hT hN.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) (0 : ℝ)
  let L : ℝ := 2 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 z.1.2.2.2
  have hL : 0 ≤ L := mul_nonneg
    (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) (apply_nonneg _ _)
  have hleft (m : ℕ) (θ : ℝ) : |stateLeftChart S z.1 m θ - θ| ≤ L * K := by
    have hH := (material_circle_sample_weights_pos hT hN.1.1).2
    have hp := circleModel_iteratedDeriv_abs_le (hS.2.1 (3 / 4 : ℝ)) hH
      z.1.2.2.2 m 0 θ
    have hw : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ K := by
      simpa only [Real.rpow_zero, mul_one] using hweight m
    have hp' : |stateLeftChart S z.1 m θ - θ| ≤ L * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
      simpa only [stateLeftChart, add_sub_cancel_left, iteratedDeriv_zero, zero_add] using hp
    exact hp'.trans (mul_le_mul_of_nonneg_left hw hL)
  refine ⟨2 * (A + L * K), mul_nonneg (by norm_num)
    (add_nonneg hA (mul_nonneg hL hK.le)), fun m θ => ?_⟩
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hr : C.right m ∈ Icc (C.left m) (C.right m) := ⟨(hC.1 m).2.1.le, le_rfl⟩
  have hf (t : ℝ) : |C.minusFlow z m (C.right m) t - (t - C.travel m)| ≤ A := by
    rw [controlGeometry_travel_eq_radialTravel hC m]
    simpa only [hN.minusFlow_reference_eq hS hT m hr t,
      radialTravel, opticalTravel, opticalSpeed] using hflow m (C.right m) hr t
  exact (hN.returnCorrectionInitialMap_and_residual_bound hz hsector m hf (hleft m) θ).1

theorem N01Properties.returnCorrectionInitialMap_sub_id_angular_jets_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1)
    (hpositive : ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv n (returnCorrectionInitialMap S C z m) θ| ≤ A)
    (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv n (fun t => returnCorrectionInitialMap S C z m t - t) θ| ≤ A := by
  by_cases hn : n = 0
  · simpa only [hn, iteratedDeriv_zero] using
      hN.returnCorrectionInitialMap_sub_id_uniform_bound hS hT hz hsector
  obtain ⟨A, hA, hb⟩ := hpositive n (by omega)
  refine ⟨A + 1, add_nonneg hA zero_le_one, fun m θ => ?_⟩
  have hs := iteratedDeriv_fun_sub
    ((hN.returnCorrectionInitialMap_contDiff hS hT hz hsector m).contDiffAt.of_le
      (show (n : ℕ∞ω) ≤ ∞ by simp))
    (contDiffAt_id : ContDiffAt ℝ (n : ℕ∞ω) (fun t : ℝ => t) θ)
  simp only [id_eq] at hs
  rw [hs]
  have hid : |iteratedDeriv n (fun t : ℝ => t) θ| ≤ 1 := by
    rw [iteratedDeriv_fun_id, if_neg hn]
    split <;> norm_num
  exact (abs_sub _ _).trans (add_le_add (hb m θ) hid)

end ContinuousFlexibility.Statements
