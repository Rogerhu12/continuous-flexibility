import ContinuousFlexibility.Analysis.N01FlowSmallness
import ContinuousFlexibility.Analysis.ReturnCorrectedFlow
import ContinuousFlexibility.Analysis.N01ReturnMargins
import ContinuousFlexibility.Analysis.CircleSobolevPointwise

/-!
# Small actual inverse-chart correction

An inverse of a map uniformly close to a translation has the same
translation-error bound. Odd and even projection preserve the error
bound after the identity is removed. Applying these elementary facts to
the specified N01 return charts controls the actual K-id and the actual
return residual by the ordinary-flow error and the decoded left chart.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

theorem inverse_translation_error_bound
    (f g : ℝ → ℝ) (T A : ℝ)
    (hfg : ∀ y, f (g y) = y)
    (hf : ∀ x, |f x - (x - T)| ≤ A) (y : ℝ) :
    |g y - (y + T)| ≤ A := by
  have h := hf (g y)
  rw [hfg y] at h
  calc
    _ = |-(y - (g y - T))| := by congr 1; ring
    _ = |y - (g y - T)| := abs_neg _
    _ ≤ A := h

theorem oddPart_sub_id_bound
    {F : ℝ → ℝ} {A : ℝ} (hF : ∀ θ, |F θ - θ| ≤ A) (θ : ℝ) :
    |oddPart F θ - θ| ≤ A := by
  have heq : oddPart F θ - θ =
      ((F θ - θ) - (F (-θ) - (-θ))) / 2 := by
    unfold oddPart
    ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  exact (abs_sub _ _).trans ((add_le_add (hF θ) (hF (-θ))).trans_eq (by ring))

theorem evenPart_bound_of_sub_id_bound
    {F : ℝ → ℝ} {A : ℝ} (hF : ∀ θ, |F θ - θ| ≤ A) (θ : ℝ) :
    |evenPart F θ| ≤ A := by
  have heq : evenPart F θ = ((F θ - θ) + (F (-θ) - (-θ))) / 2 := by
    unfold evenPart
    ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  exact (abs_add_le _ _).trans ((add_le_add (hF θ) (hF (-θ))).trans_eq (by ring))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

local instance returnCorrectionSmallnessStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem stateChartGrading_le_stateGrading (S : PhysicalSpacesData)
    (n : ℕ) (x : AnnularState S) :
    (S.circle (3 / 4 : ℝ)).grading n x.2.2.2 ≤ stateGrading S n x := by
  simp only [stateGrading, pairGrading_apply]
  linarith only [apply_nonneg (heightPairGrading S n) x.1,
    apply_nonneg (realGrading n) x.2.1,
    apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.1]

theorem N01Properties.stateLeftChart_sub_id_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {base' : ℕ} {η : ℝ} (hbase : 1 ≤ base')
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base' η)
    (m : ℕ) (θ : ℝ) :
    |stateLeftChart S z.1 m θ - θ| ≤
      (2 * circleSobolevConstant * η) * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have href : referenceStateConditions D S C := hN.2.2.1
  have hτ : (z.1 - C.referenceState).2.2.2 = z.1.2.2.2 := by
    change z.1.2.2.2 - C.referenceState.2.2.2 = z.1.2.2.2
    exact (congrArg (fun u : CircleSpace S => z.1.2.2.2 - u)
      href.2.2.2.2.1).trans (sub_zero _)
  have hgrade : (S.circle (3 / 4 : ℝ)).grading 1 z.1.2.2.2 ≤
      stateGrading S 1 (z.1 - C.referenceState) :=
    (congrArg (fun u : CircleSpace S => (S.circle (3 / 4 : ℝ)).grading 1 u)
      hτ).symm.le.trans (stateChartGrading_le_stateGrading S 1 (z.1 - C.referenceState))
  have hsmall : (S.circle (3 / 4 : ℝ)).grading 1 z.1.2.2.2 ≤ η :=
    (hgrade.trans ((solve_stateGrading_monotone S hbase _))).trans hz.1.le
  obtain ⟨_, hRef⟩ := hN.1.1
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hRef.2.1 i)).2.1
  have hb := circleModel_iteratedDeriv_abs_le (hS.2.1 (3 / 4 : ℝ)) hH
    z.1.2.2.2 m 0 θ
  simp only [iteratedDeriv_zero, zero_add] at hb
  simp only [stateLeftChart, add_sub_cancel_left]
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num) circleSobolevConstant_nonneg))
    (Real.rpow_nonneg (hH m).le _))

theorem N01Properties.returnCorrectionInitialMap_and_residual_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {A B : ℝ}
    (hf : ∀ θ, |C.minusFlow z m (C.right m) θ - (θ - C.travel m)| ≤ A)
    (hL : ∀ θ, |stateLeftChart S z.1 m θ - θ| ≤ B) (θ : ℝ) :
    |returnCorrectionInitialMap S C z m θ - θ| ≤ 2 * (A + B) ∧
      |returnResidualField S C z m θ| ≤ A + B := by
  have hI := N01Properties.return_inverse_and_positive S C z m hN hz hsector
  let G : ℝ → ℝ := fun t =>
    stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m
  have hfinv (t : ℝ) : |C.minusReturnInverse z m t - (t + C.travel m)| ≤ A :=
    inverse_translation_error_bound _ _ _ _ (fun y => (hI y).1) hf t
  have hG (t : ℝ) : |G t - t| ≤ A + B := by
    have heq : G t - t =
        (C.minusReturnInverse z m t - (t + C.travel m)) +
          (stateLeftChart S z.1 m (C.minusReturnInverse z m t) -
            C.minusReturnInverse z m t) := by
      dsimp only [G]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (hfinv t) (hL _))
  have hR (t : ℝ) : |rightChartCandidate S C z m t - t| ≤ A + B := by
    exact oddPart_sub_id_bound hG t
  have hRinv (t : ℝ) : |C.rightChartInverse z m t - t| ≤ A + B := by
    have h := inverse_translation_error_bound
      (rightChartCandidate S C z m) (C.rightChartInverse z m) 0 (A + B)
      (fun y => (hI y).2.2.1) (by simpa only [sub_zero] using hR) t
    simpa only [add_zero] using h
  constructor
  · let y := stateLeftChart S z.1 m θ - C.travel m
    have heq : returnCorrectionInitialMap S C z m θ - θ =
        (C.minusReturnInverse z m (C.rightChartInverse z m y) -
          (C.rightChartInverse z m y + C.travel m)) +
        (C.rightChartInverse z m y - y) +
        (stateLeftChart S z.1 m θ - θ) := by
      simp only [returnCorrectionInitialMap_apply, y]
      ring
    rw [heq]
    calc
      _ ≤ |(C.minusReturnInverse z m (C.rightChartInverse z m y) -
            (C.rightChartInverse z m y + C.travel m)) +
            (C.rightChartInverse z m y - y)| + |stateLeftChart S z.1 m θ - θ| :=
        abs_add_le _ _
      _ ≤ (|C.minusReturnInverse z m (C.rightChartInverse z m y) -
            (C.rightChartInverse z m y + C.travel m)| +
            |C.rightChartInverse z m y - y|) + |stateLeftChart S z.1 m θ - θ| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (A + (A + B)) + B := add_le_add
        (add_le_add (hfinv _) (hRinv y)) (hL θ)
      _ = _ := by ring
  · exact evenPart_bound_of_sub_id_bound hG (C.rightChartInverse z m θ)

theorem N01Properties.returnCorrectionInitialMap_and_residual_small
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧ ∀ base' : ℕ, base ≤ base' → 1 + hN.ordinaryFlowLoss 1 ≤ base' →
      ∀ η : ℝ, η ≤ ε → η ≤ 1 / 2 →
      ∀ z ∈ stateNeighborhood S C base' η, stateSector S z.1 →
      ∀ m θ,
      let F := 6 * B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B * η
      let L := (2 * circleSobolevConstant * η) * T.H (T.sample m) ^ (3 / 4 : ℝ)
      |returnCorrectionInitialMap S C z m θ - θ| ≤ 2 * (F + L) ∧
        |returnResidualField S C z m θ| ≤ F + L := by
  obtain ⟨B, hB, hb⟩ := hN.minusFlow_near_reference_weighted hS hT
  refine ⟨B, hB, fun base' hbase hhigh η hηε hη₁ z hz hsector m θ => ?_⟩
  have hzold := stateNeighborhood_mono S C hbase hηε hz
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hr : C.right m ∈ Icc (C.left m) (C.right m) := ⟨(hC.1 m).2.1.le, le_rfl⟩
  have htravel : C.travel m = opticalTravel D.w (C.left m) (C.right m) :=
    controlGeometry_travel_eq_radialTravel hC m
  apply hN.returnCorrectionInitialMap_and_residual_bound hzold hsector m
  · intro t
    rw [htravel]
    exact (hb base' hbase hhigh η hηε hη₁ z hz hsector m (C.right m) hr t).1
  · exact fun t => hN.stateLeftChart_sub_id_bound hS hT (by omega) hz m t

end ContinuousFlexibility.Statements

