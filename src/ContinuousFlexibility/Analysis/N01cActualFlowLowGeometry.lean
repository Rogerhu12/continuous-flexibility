import ContinuousFlexibility.Analysis.N01cCommonCosineGeometry
import ContinuousFlexibility.Analysis.N01cActualFlowForcingComposition
import ContinuousFlexibility.Analysis.N01cFlowNumericConstants

/-!
# Stable low geometry of the actual finite-plot flow

The original cosine trajectory gives both the Jacobian lower bound and
the low derivative-defect norm. Its finite plot has exactly the same
value at parameter zero. The numerical constants are chosen once from
the common integrated fourth speed norm, before any parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

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

theorem ordinaryFlowFiniteAngle_lowGeometry_le
    (hGx : ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (x, p)))
    {M K : ℝ}
    (hΛ : circleFlowLambda (fun p => componentCosineSpeed D S C m (x, p)) hGx
      (componentCosineSpeed_periodic hS x m) 4 0 Real.pi ≤ M)
    (hK : ∀ R ∈ Icc (0 : ℝ) M, circleFlowLowGeometryBound Real.pi R ≤ K)
    (t : ℝ) (θ : ℝ) :
    Real.exp (-(circleFlowEmbeddingConstant Real.pi * M)) ≤
        deriv (ordinaryFlowFiniteAngle m x hx L t) θ ∧
      circleRealSobolevNorm 3
        (ordinaryFlowFiniteDefectJet hS hT hA hB hpos m J x hx L t 0) ≤ K := by
  let Θ : PolarPoint → ℝ := fun p =>
    C.minusFlow x m (rootCosinePath (C.left m) (C.right m) p.1) p.2
  have hΘ : ∀ α : ℝ, ContinuousOn (fun r => Θ (r, α)) (Icc (0 : ℝ) Real.pi) :=
    continuousOn_componentCosineFlow hA hB hx m
  have hinit : ∀ α : ℝ, Θ (0, α) = α := componentCosineFlow_initial hB hx m
  have hflow : ∀ r ∈ Ioo (0 : ℝ) Real.pi, ∀ α : ℝ,
      HasDerivAt (fun u => Θ (u, α))
        (componentCosineSpeed D S C m (x, (r, Θ (r, α)))) r :=
    fun r hr α => hasDerivAt_componentCosineFlow hS hT hA hB hx m α hr
  have ht := circleFlowCompactTime_mem Real.pi_pos.le t
  have hderiv := (circleFlow_deriv_bounds_lowSobolev hGx
    (componentCosineSpeed_periodic hS x m) hΘ hinit hflow ht θ).1
  have hbound : Real.exp (-(circleFlowEmbeddingConstant Real.pi * M)) ≤
      Real.exp (-(circleFlowEmbeddingConstant Real.pi *
        circleFlowLambda (fun p => componentCosineSpeed D S C m (x, p)) hGx
          (componentCosineSpeed_periodic hS x m) 4 0 Real.pi)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hΛ
      (circleFlowEmbeddingConstant_pos Real.pi).le))
  have hdefect := circleFlow_defect_h3_le hGx
    (componentCosineSpeed_periodic hS x m) hΘ hinit hflow ht
  have hnonneg := circleFlowLambda_nonneg
    (fun p => componentCosineSpeed D S C m (x, p)) hGx
    (componentCosineSpeed_periodic hS x m) 4 Real.pi_pos.le
  refine ⟨?_, ?_⟩
  · simpa only [ordinaryFlowFiniteAngle, ordinaryFlowFiniteTrajectory_zero,
      ordinaryFlowInCosineTime, Θ] using hbound.trans hderiv
  · simpa only [ordinaryFlowFiniteDefectJet, ordinaryFlowFiniteAngle,
      ordinaryFlowFiniteTrajectory_zero, ordinaryFlowInCosineTime, Θ] using
        hdefect.trans (hK _ ⟨hnonneg, hΛ⟩)

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The same two constants work for every stronger base, smaller positive
radius, genuine speed tower, and finite parameter plot. -/
theorem n01_exists_stable_actualFlow_lowGeometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ, base ≤ base₀ ∧ 0 < ε₀ ∧
      ε₀ ≤ min ε (1 / 2) ∧ ∃ c M : ℝ, 0 < c ∧ 0 < M ∧
      ∀ base' : ℕ, base₀ ≤ base' → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
      ∀ hB' : N01PartB D S C base' ε',
      ∀ hpos : (∀ z ∈ stateNeighborhood S C base' ε', ∀ i r,
        r ∈ Icc (C.left i) (C.right i) →
          0 < twoRootDivided (componentOpticalSquare D S C i z)
            (C.left i) (C.right i) r),
      ∀ m, ∀ J : ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
        (componentCosineSpeed D S C m),
      ∀ d : ℕ, ∀ x : AnnularState S × ℝ,
      ∀ hx : x ∈ stateNeighborhood S C base' ε',
      ∀ L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ), ∀ t : ℝ,
        (∀ θ, c ≤ deriv (ordinaryFlowFiniteAngle m x hx L t) θ) ∧
        circleRealSobolevNorm 3
          (ordinaryFlowFiniteDefectJet hS hT hA hB' hpos m J x hx L t 0) ≤ M := by
  obtain ⟨bg, eg, hbg, heg, hege, hposg, hGs, MΛ, hMΛ, hΛ⟩ :=
    n01_exists_common_cosineLowGeometry hS hT hA hε hB hG hSpeed
  obtain ⟨M, hM, hMbound⟩ := exists_circleFlowLowGeometryBound_uniform Real.pi MΛ
  refine ⟨bg, min eg (1 / 2), hbg, lt_min heg (by norm_num),
    min_le_min hege le_rfl,
    Real.exp (-(circleFlowEmbeddingConstant Real.pi * MΛ)), M,
    Real.exp_pos _, hM, ?_⟩
  intro base' hb ε' hε' he hB' hpos m J d x hx L t
  have hxg : x ∈ stateNeighborhood S C bg eg :=
    stateNeighborhood_subset hb (he.trans (min_le_left _ _)) hx
  have hGx := hGs x hxg m
  have hlow (θ : ℝ) := ordinaryFlowFiniteAngle_lowGeometry_le
    hS hT hA hB' hpos m J x hx L hGx (hΛ x hxg m hGx).1 hMbound t θ
  exact ⟨fun θ => (hlow θ).1, (hlow 0).2⟩

end ContinuousFlexibility.Blueprint
