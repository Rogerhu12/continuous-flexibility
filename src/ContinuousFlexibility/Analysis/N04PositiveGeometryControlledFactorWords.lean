import ContinuousFlexibility.Analysis.N04PositiveGeometryActualFactorDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledAngleWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRadialWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledAngularLower
import ContinuousFlexibility.Analysis.N04PositiveGeometryPlaneSavedComposition
import ContinuousFlexibility.Analysis.N04PositiveGeometryActualFactorPrefixData

/-!
# One material power for the four actual scalar factors

The endpoint packets have the same reserve and the same normalized
power. Both radial kernels and the angular inverse retain their saved
positive order. All constants are chosen before the component and state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_controlledFactors_saved_prefix
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (G : N04PositiveGeometryControlledFamily W X order) (N : ℕ) (A RH : ℝ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (base : ℕ) (ε : ℝ), G.base ≤ base → ε ≤ G.ε →
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      ∀ F : N04PositiveGeometryFactorData G base ε i,
      ∀ JA : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × ℝ =>
          G.toN04PositiveGeometryControlData.angularCoefficients
            (liftSectorParameter W.S W.C z.1) i z.2),
      ∀ JR : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × ℝ => fun side (j : Fin (order + 1)) =>
          G.toN04PositiveGeometryControlData.coefficients
            (liftSectorParameter W.S W.C z.1) i side (j + 1) z.2),
      ∀ (p q : Seminorm ℝ (StateDirections W.S × ℝ)) (R H t : ℝ),
        0 ≤ R → 0 ≤ H → H ≤ RH → 1 ≤ t →
      ∀ K s shift : ℕ, N ≤ K + s + 1 →
      ∀ x ∈ sectorNeighborhood W.S base ε ε,
      (∀ θ, N04BoundaryWordBounds JA K (s + K) 1 x θ
        (fun a => p a ≤ 1 ∧ q a ≤ R) (A * W.U.E0 (W.U.sample (X.cell i)) ^ A) H t shift) →
      (∀ θ, N04BoundaryWordBounds JR K (s + K) 1 x θ
        (fun a => p a ≤ 1 ∧ q a ≤ R) (A * W.U.E0 (W.U.sample (X.cell i)) ^ A) H t shift) →
      let Ω : Set PolarPoint := Icc (n04PositiveLeft i) (n04PositiveRight i) ×ˢ univ
      let M : ℝ := B * W.U.E0 (W.U.sample (X.cell i)) ^ B
      N04PlaneSavedWordBounds F.angle N K (shift + 1) x Ω p q R M H t ∧
      N04PlaneSavedWordBounds F.angleInverse N K (shift + 1) x Ω p q R M H t ∧
      N04PlaneSavedWordBounds F.radial N K (shift + 1) x Ω p q R M H t ∧
      N04PlaneSavedWordBounds F.radialInverse N K (shift + 1) x Ω p q R M H t := by
  let V := StateDirections W.S × ℝ
  haveI : IsTopologicalAddGroup V := inferInstance
  haveI : ContinuousSMul ℝ V := inferInstance
  let I := N04PositiveComponent W.D.a W.D.b (deriv W.D.w)
  let E : I → ℝ := fun i => W.U.E0 (W.U.sample (X.cell i))
  have hE (i : I) : 1 ≤ E i := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  let angleData := n04PositiveGeometry_actualAnglePrefixData G N A RH hA
  let Bφ : ℝ := angleData.choose
  let hφ := angleData.choose_spec.2
  let radialData := n04PositiveGeometry_actualRadialPrefixData G false N A RH hA
  let BY : ℝ := radialData.choose
  let hY := radialData.choose_spec.2
  let radialInverseData := n04PositiveGeometry_actualRadialPrefixData G true N A RH hA
  let Bρ : ℝ := radialInverseData.choose
  let hρ := radialInverseData.choose_spec.2
  let D : ℝ := max 1 (max Bφ (max BY (max Bρ (max RH (2 * G.Cinput)))))
  have hD : 1 ≤ D := le_max_left _ _
  have hφD : Bφ ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hYD : BY ≤ D := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hρD : Bρ ≤ D := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hRHD : RH ≤ D := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have hCD : 2 * G.Cinput ≤ D := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  let inverseData := n04PositiveGeometry_actualInversePrefixData W N
  let Ainv : ℝ := inverseData.choose
  let dinv : ℕ := inverseData.choose_spec.2.choose
  let hinv := inverseData.choose_spec.2.choose_spec
  let packData := n04PositiveGeometry_polynomial_sample_pack Ainv D dinv
  let B₁ : ℝ := packData.choose
  let hpack := packData.choose_spec.2
  let B : ℝ := max D B₁
  have hDB : D ≤ B := le_max_left _ _
  have hB : 1 ≤ B := hD.trans hDB
  refine ⟨B, hB, ?_⟩
  intro base ε hGb hGε i F JA JR p q R H t hR hH hHR ht K s shift hN x hx hJA hJR
  let U := sectorNeighborhood W.S base ε ε
  let state := liftSectorParameter W.S W.C
  let Ω : Set PolarPoint := Icc (n04PositiveLeft i) (n04PositiveRight i) ×ˢ univ
  let M : ℝ := D * E i ^ D
  let Mout : ℝ := B * E i ^ B
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S base ε ε
  have hz (z : V) (hz : z ∈ U) : state z ∈ stateNeighborhood W.S W.C G.base G.ε :=
    stateNeighborhood_mono W.S W.C hGb hGε
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl)
  have hs (z : V) : stateSector W.S (state z).1 :=
    W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hD
    (Real.one_le_rpow (hE i) (zero_le_one.trans hD))
  have hDM : D ≤ M := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_rpow (hE i) (zero_le_one.trans hD)) (zero_le_one.trans hD)
  have hraise {a b : ℝ} (hab : a ≤ b) (hb : 0 ≤ b) :
      a * E i ^ a ≤ b * E i ^ b :=
    mul_le_mul hab (Real.rpow_le_rpow_of_exponent_le (hE i) hab)
      (Real.rpow_nonneg (zero_le_one.trans (hE i)) _) hb
  have hMM : M ≤ Mout := hraise hDB (zero_le_one.trans hB)
  have hφraw : N04PlaneSavedWordBounds F.angle N K (shift + 1) x Ω p q R M H t := by
    apply N04PlaneSavedWordBounds.enlarge (M := Bφ * E i ^ Bφ) ?_ hH ht
      (hraise hφD (zero_le_one.trans hD))
    intro y hy j hj hjN w hw v hpure hbox
    have hf : Continuous (deriv W.D.w) :=
      (n04b_profileGeometry_of_through03 W.through03).2.2.1.1.continuous_deriv (by simp)
    have hi := n04PositiveComponent_bounds hf i
    have hyD : y.1 ∈ Icc W.D.a W.D.b :=
      ⟨hi.1.trans hy.1.1, hy.1.2.trans hi.2.2⟩
    exact hφ U hU state i JA F.angle p q R H t hR hH hHR ht K s shift x hx y hyD
      (hJA y.2) j hj hjN (hjN.trans hN) w hw v hpure hbox
  have hYraw : N04PlaneSavedWordBounds F.radial N K (shift + 1) x Ω p q R M H t := by
    apply N04PlaneSavedWordBounds.enlarge (M := BY * E i ^ BY) ?_ hH ht
      (hraise hYD (zero_le_one.trans hD))
    intro y hy j hj hjN w hw v hpure hbox
    exact hY U hU state hz (fun z _ => hs z) i JR F.radial p q R H t hR hH hHR ht
      K s shift x hx y hy.1 (hJR y.2) j hj hjN (hjN.trans hN) w hw v hpure hbox
  have hρraw : N04PlaneSavedWordBounds F.radialInverse N K (shift + 1) x Ω p q R M H t := by
    apply N04PlaneSavedWordBounds.enlarge (M := Bρ * E i ^ Bρ) ?_ hH ht
      (hraise hρD (zero_le_one.trans hD))
    intro y hy j hj hjN w hw v hpure hbox
    exact hρ U hU state hz (fun z _ => hs z) i JR F.radialInverse p q R H t hR hH hHR ht
      K s shift x hx y hy.1 (hJR y.2) j hj hjN (hjN.trans hN) w hw v hpure hbox
  let Jr := n04PositiveGeometry_spatialLinearDirections hU (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jφ := smoothDirectionsProd Jr F.angle
  let Jα := smoothDirectionsProd Jr F.angleInverse
  have hr : N04PlaneSavedWordBounds Jr N K (shift + 1) x Ω p q R M H t :=
    N04PlaneSavedWordBounds.spatialLinear hU _ Jr hx hM
      ((ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ).trans hM) hH ht
  have hgraph := hr.pair F.angle Jφ hx hφraw
  have hslope (y : PolarPoint) (hy : y ∈ Ω) :
      |(deriv (fun θ => G.toN04PositiveGeometryControlData.angle (state x) i (y.1, θ))
        (parameterizedCircleInverse (G.toN04PositiveGeometryControlData.angle (state x) i) y))⁻¹| ≤ M := by
    apply (n04PositiveGeometry_controlled_angle_inverse_slope_bound G (hz x hx) (hs x)
      i y.1 _).trans
    have hci : G.Cinput ≤ D := (by linarith only [G.input_constant] : G.Cinput ≤ 2 * G.Cinput).trans hCD
    calc
      2 * G.M i ≤ (2 * G.Cinput) * E i ^ G.Cinput := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (G.input_cost i) (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ D * E i ^ D := mul_le_mul hCD
        (Real.rpow_le_rpow_of_exponent_le (hE i) hci)
        (Real.rpow_nonneg (zero_le_one.trans (hE i)) _) (zero_le_one.trans hD)
  have hαgraph := hinv U (fun z => G.toN04PositiveGeometryControlData.angle (state z) i)
    Jφ Jα
    (fun z hz' => n04PositiveGeometry_controlled_angle_contDiff G (hz z hz') (hs z) i)
    (fun z hz' y => n04PositiveGeometry_controlled_angle_positive G (hz z hz') (hs z) i y.1 y.2)
    (fun z hz' => n04PositiveGeometry_controlled_angle_period G (hz z hz') (hs z) i)
    x hx Ω (fun y hy => ⟨hy.1, mem_univ _⟩) p q R M H t hR hM hH
    (hHR.trans (hRHD.trans hDM)) ht hslope K (shift + 1) (Nat.succ_pos shift) hgraph
  have hα : N04PlaneSavedWordBounds F.angleInverse N K (shift + 1) x Ω p q R
      (Ainv * M ^ dinv) H t :=
    (hαgraph.postcompCLM (ContinuousLinearMap.snd ℝ ℝ ℝ)
      (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)).congr hx F.angleInverse (fun _ _ => rfl)
  have hαcost : Ainv * M ^ dinv ≤ Mout := (hpack (E i) (hE i)).trans
    (hraise (le_max_right D B₁) (zero_le_one.trans hB))
  exact ⟨hφraw.enlarge hH ht hMM, hα.enlarge hH ht hαcost,
    hYraw.enlarge hH ht hMM, hρraw.enlarge hH ht hMM⟩

end ContinuousFlexibility.Analysis
