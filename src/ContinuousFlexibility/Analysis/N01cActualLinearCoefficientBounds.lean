import ContinuousFlexibility.Analysis.N01cActualFlowForcingComposition

/-!
# The actual low linear-coefficient integral

Circle composition applies to the all-angle singleton head. Fixed low
geometry and a uniform third Sobolev norm of this actual outer speed
therefore bound the coefficient's first norm. Integrating its continuous
norm on the unit time interval gives the constant used in every positive
parameter variational equation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

private theorem n01c_coefficientNorm_one_le_of_head
    (V : CircleLinearVariationData Real.pi 0 1)
    (O Q : ℕ → C(AddCircle Real.pi, ℝ)) (head : C(AddCircle Real.pi, ℝ)) (t : ℝ)
    (hO : ∀ (b : ℕ) (θ : ℝ), HasDerivAt
      (fun η : ℝ => O b (η : AddCircle Real.pi)) (O (b + 1) (θ : AddCircle Real.pi)) θ)
    (hQ : ∀ (b : ℕ) (θ : ℝ), HasDerivAt
      (fun η : ℝ => Q b (η : AddCircle Real.pi)) (Q (b + 1) (θ : AddCircle Real.pi)) θ)
    {K M B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hlow : circleRealSobolevNorm 3 (Q 0) ≤ M)
    (houter : circleRealSobolevNorm 3 (O 0) ≤ B)
    (hhead : circleRealSobolevNorm 1 head ≤ K *
      (circleRealSobolevNorm 1 (O 0) +
        circleRealSobolevNorm 3 (O 0) * circleRealSobolevNorm 0 (Q 0)))
    (hcoefficient : V.coefficient t 0 = head) :
    V.coefficientNorm 1 t ≤ K * (B + B * M) := by
  have hO₁ : circleRealSobolevNorm 1 (O 0) ≤ circleRealSobolevNorm 3 (O 0) :=
    circle_sobolevNorm_mono_of_derivatives
      (fun b => circleComplexify (O b)) (circleComplexify_hasDerivAt O hO)
      (by decide : (1 : ℕ) ≤ 3)
  have hQ₀ : circleRealSobolevNorm 0 (Q 0) ≤ M :=
    (circle_sobolevNorm_mono_of_derivatives
      (fun b => circleComplexify (Q b)) (circleComplexify_hasDerivAt Q hQ)
      (by decide : (0 : ℕ) ≤ 3)).trans hlow
  have hproduct : circleRealSobolevNorm 3 (O 0) *
      circleRealSobolevNorm 0 (Q 0) ≤ B * M :=
    mul_le_mul houter hQ₀ (circle_real_sobolevNorm_nonneg _ _) hB
  change circleRealSobolevNorm 1 (V.coefficient t 0) ≤ _
  rw [hcoefficient]
  exact hhead.trans (mul_le_mul_of_nonneg_left
    (add_le_add (hO₁.trans houter) hproduct) hK)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
  (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
    r ∈ Icc (C.left i) (C.right i) →
      0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
  (m : ℕ)
  (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
    (componentCosineSpeed D S C m))
  {d : ℕ} (x : AnnularState S × ℝ) (hx : x ∈ stateNeighborhood S C base ε)
  (L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ))

theorem ordinaryFlowCircleVariationData_coefficientNorm_one_le
    (n : ℕ) (v : Fin (n + 1) → (Fin d → ℝ))
    (t : ℝ) {c M B : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hB₀ : 0 ≤ B)
    (hlower : ∀ θ, c ≤ deriv (ordinaryFlowFiniteAngle m x hx L t) θ)
    (hlow : circleRealSobolevNorm 3
      (ordinaryFlowFiniteDefectJet hS hT hA hB hpos m J x hx L t 0) ≤ M)
    (houter : circleRealSobolevNorm 3
      (ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L
        (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice 0) ≤ B) :
    (ordinaryFlowCircleVariationData hS hT hA hB hpos m J x hx L n v).coefficientNorm 1 t ≤ circleLiftCompositionConstant Real.pi c M 1 * (B + B * M) := by
  let O : ℕ → C(AddCircle Real.pi, ℝ) :=
    ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L
      (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice
  let Q : ℕ → C(AddCircle Real.pi, ℝ) :=
    ordinaryFlowFiniteDefectJet hS hT hA hB hpos m J x hx L t
  have hO : ∀ (b : ℕ) (θ : ℝ), HasDerivAt (fun η : ℝ => O b (η : AddCircle Real.pi))
      (O (b + 1) (θ : AddCircle Real.pi)) θ :=
    periodicCircleJet_hasDerivAt _ _ _
  have hQ : ∀ (b : ℕ) (θ : ℝ), HasDerivAt (fun η : ℝ => Q b (η : AddCircle Real.pi))
      (Q (b + 1) (θ : AddCircle Real.pi)) θ :=
    circleLiftDefectJet_hasDerivAt _ _ _
  exact n01c_coefficientNorm_one_le_of_head
    (ordinaryFlowCircleVariationData hS hT hA hB hpos m J x hx L n v) O Q
    (ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L
      (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice 0 0) t hO hQ
    (zero_le_one.trans (circleLiftCompositionConstant_one_le Real.pi c M 1))
    hB₀ hlow houter
    (ordinaryFlowForcingFactorJet_head_sobolev_le hS hT hA hB hpos m J x hx L
      (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice 1 hc hM hlower hlow)
    (ordinaryFlowCircleVariationData_coefficient_eq_head hS hT hA hB hpos m J x hx L n v t)

theorem ordinaryFlowCircleVariationData_coefficientSize_one_le
    (n : ℕ) (v : Fin (n + 1) → (Fin d → ℝ))
    {c M B : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hB₀ : 0 ≤ B)
    (hlower : ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
      c ≤ deriv (ordinaryFlowFiniteAngle m x hx L t) θ)
    (hlow : ∀ t ∈ Icc (0 : ℝ) 1, circleRealSobolevNorm 3
      (ordinaryFlowFiniteDefectJet hS hT hA hB hpos m J x hx L t 0) ≤ M)
    (houter : ∀ t ∈ Icc (0 : ℝ) 1, circleRealSobolevNorm 3
      (ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L
        (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice 0) ≤ B) :
    (ordinaryFlowCircleVariationData hS hT hA hB hpos m J x hx L n v).coefficientSize 1 ≤ circleLiftCompositionConstant Real.pi c M 1 * (B + B * M) := by
  let V := ordinaryFlowCircleVariationData hS hT hA hB hpos m J x hx L n v
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      V.coefficientNorm 1 t ≤ circleLiftCompositionConstant Real.pi c M 1 * (B + B * M) :=
    ordinaryFlowCircleVariationData_coefficientNorm_one_le
      hS hT hA hB hpos m J x hx L n v t hc hM hB₀
      (hlower t ht) (hlow t ht) (houter t ht)
  have hbound := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    ((V.coefficientNorm_continuous 1).intervalIntegrable_of_Icc (by norm_num))
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => circleLiftCompositionConstant Real.pi c M 1 * (B + B * M))
      volume 0 1) hpoint
  simpa only [CircleLinearVariationData.coefficientSize,
    intervalIntegral.integral_const, sub_zero, one_smul] using hbound

end ContinuousFlexibility.Statements
