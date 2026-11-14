module

public import ContinuousFlexibility.Analysis.N01cPhysicalFlowFixedBounds
public import ContinuousFlexibility.Analysis.N01cCommonWholeSpeedBounds
public import ContinuousFlexibility.Analysis.N01cCommonCosineTowers
public import ContinuousFlexibility.Analysis.N01cActualFlowSmoothDirections

/-!
# Fixed-order bounds for the actual positive-radial ordinary flow

The generic physical graph estimate is applied to the original speed
and supplied ordinary trajectories. Their spatial regularity follows
from the actual smooth cosine speed. The component distance, material
height bound and genuine state-angle towers are supplied without adding
an estimate or regularity assumption on the flow.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

private theorem n01c_componentDistance_le_totalWidth
    {a b l h r : ℝ} (hal : a < l) (hrh : r < h) (hhb : h < b) :
    min (r - l) (h - r) ≤ b - a := by
  linarith [min_le_left (r - l) (h - r)]

/-- The scalar material bound is eliminated before entering the actual
state-valued continuation. -/
private theorem n01c_with_componentHeightBound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (cell : ℕ → ℕ) (P : Prop)
    (hP : ∀ RH : ℝ,
      (∀ m, 0 ≤ T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ∧
        T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ RH) → P) : P := by
  obtain ⟨RH, hRH, hb⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  apply hP RH
  intro m
  have hs := materialSample_mem_radialCore hT hRef.choose_spec.2.1 (cell m)
  refine ⟨Real.rpow_nonneg (hT.2.1 _ hs).2.1.le _, ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hb _ hs

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- Fixed-order positive-radial bounds for every genuine tower of the
actual ordinary-flow family, on the unchanged common neighbourhood. -/
theorem ordinaryFlow_positiveMixed_fixed_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    {base lossRaw lossIz lossIp o₀ : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z)
          (C.left m) (C.right m) r)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hε2 : ε ≤ 1 / 2)
    (W : WholeCharacteristicSpeedPowerControl D T S C base lossRaw ε)
    (JT : ∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m))
    (JR : OrdinarySpeedRadialTowers D S C (stateNeighborhood S C base ε))
    (hIz : SpatialPowerInterpolation (pairGrading (stateGrading S) realGrading)
      base lossIz o₀)
    (hIp : SpatialPowerInterpolation (pairGrading (stateGrading S) realGrading)
      base lossIp 0)
    (K offset n b k s : ℕ) (hk : 0 < k) (hkK : k ≤ K)
    (hNS : (b + k) + offset ≤ s)
    (horder : n + b + (offset + 1) * k ≤ s)
    (hzero : ∀ β : ℕ, 1 ≤ β → ∃ B : ℝ, 0 < B ∧
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ z,
      z ∈ stateNeighborhood S C base ε →
        |iteratedDeriv β (fun η => C.minusFlow z m r η) θ| ≤
          B * (1 + pairGrading (stateGrading S) realGrading (β - 1 + o₀)
            (z - (C.referenceState, 0))))
    (hpositive : ∀ β : ℕ, ∃ B A : ℝ, 1 ≤ B ∧ 0 ≤ A ∧
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ : ℝ,
      ∀ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => iteratedDeriv β (fun η => C.minusFlow z m r η) θ),
      ∀ j : ℕ, j ≤ K → 0 < j →
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin j → (AnnularState S × ℝ),
        |J.D j z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ A *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (β + offset) (z - (C.referenceState, 0)) v) :
    ∃ B A : ℝ, 1 ≤ B ∧ 0 ≤ A ∧
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ : ℝ,
      ∀ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => mixedDerivative (n + 1) b (fun q => C.minusFlow z m q.1 q.2) (r, θ)),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        min (r - C.left m) (C.right m - r) ^ (n + 1) * |J.D k z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ A *
            oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
              base (s + max lossRaw (max lossIz lossIp)) (z - (C.referenceState, 0)) v := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  exact n01c_with_componentHeightBound hT hA.1.1 C.cell _
    (fun RH hH => physicalFlow_positiveMixed_fixed_bound
      (X := AnnularState S × ℝ) (ι := ℕ)
      (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
      (C.referenceState, 0) base lossRaw lossIz lossIp o₀
      (stateNeighborhood S C base ε)
      (fun m => Ioo (C.left m) (C.right m))
      (isOpen_stateNeighborhood S C base ε) (fun _ => isOpen_Ioo)
      (fun m r => min (r - C.left m) (C.right m - r))
      (fun m => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
      (fun m => T.E0 (T.sample (C.cell m)))
      (fun _ z => minusCharacteristicSpeed (originalCoefficients D S C z))
      (fun m z q => C.minusFlow z m q.1 q.2)
      W.regular W.bounds
      (fun m z hz => contDiffOn_minusFlow_of_cosineSpeed hS hT hA hB hz m
        (contDiff_componentCosineSpeed hS hT hA hB hpos hz m))
      (fun m z hz r hr θ => (hB.1 z hz m θ).2.2.1 r hr)
      JR
      (fun m r hr => ordinaryFlowJointSmoothDirections hS hT hA hB hpos m
        (JT m) ⟨hr.1.le, hr.2.le⟩)
      (fun m r hr => (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)).le)
      (width := D.b - D.a)
      (fun m r hr => n01c_componentDistance_le_totalWidth
        (hA.2.2.1.1 m).1 hr.2 (hA.2.2.1.1 m).2.2)
      (fun m => hE _
        (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)))
      hH
      (fun z hz => (jointStateGrading_displacement_lt_one hε2 hz).le)
      hIz hIp K offset n b k s hk hkK hNS horder hzero hpositive)

end ContinuousFlexibility.Statements
