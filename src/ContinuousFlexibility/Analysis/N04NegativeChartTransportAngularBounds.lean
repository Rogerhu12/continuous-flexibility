module

public import ContinuousFlexibility.Analysis.N04NegativeChartCircleStateBudget
public import ContinuousFlexibility.Analysis.N04NegativeChartTransportCircleBounds
public import ContinuousFlexibility.Analysis.N04NegativeChartFirstIntegralCircleBounds
public import ContinuousFlexibility.Analysis.N04NegativeChartInteriorTowers
public import ContinuousFlexibility.Analysis.N01TransportAngularInterpolation

/-!
# The actual angular inputs with a common state-order budget

The original full-component towers are identified with the same closed
radius selector families. Each low order is chosen before every state
prefix. The slope has its constant reference value; the correction and
first-integral defect keep the positive circle sample height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E I : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def N04NegativeChartAngularStateBudget
    (p : ℕ → Seminorm ℝ E) (weight : ℕ → ℝ) (U : Set E) (l h : ℕ → ℝ)
    {f : ℕ → E × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (f m)) : Prop :=
  ∃ B : ℕ, ∀ K : ℕ, ∃ D : ℕ,
    ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ K → ∀ b : ℕ, b ≤ N →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m x, x ∈ U → ∀ w : E,
      p B x ≤ R → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
      |jointMixedDiagonal (J m) k 0 b x w y| ≤
        C * weight m * (1 + p (N + K * D + B + 1) x +
          p (N + K * D + B + 1) w) ^
            (((b + k * D : ℕ) : ℝ) / ((N + K * D : ℕ) + 1 : ℝ))

private theorem circle_angular_stateBudget_add_const
    {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    {p : ℕ → Seminorm ℝ E} {U : Set E} {g : I → E → H.Space}
    (hg : N04FixedBaseSmoothFamilyOn p H.grading U g)
    (hp : Monotone p) (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m))
    (hheightBound : ∃ KH : ℝ, 0 ≤ KH ∧ ∀ m, T.H (T.sample m) ^ γ ≤ KH)
    (l h : ℕ → ℝ) (rsel : I → ℕ → ℝ)
    (hcover : ∀ m r, r ∈ Ioo (l m) (h m) → ∃ i, rsel i m = r)
    {f : ℕ → E × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (f m))
    (c : ℝ)
    (heq : ∀ i m, rsel i m ∈ Ioo (l m) (h m) → ∀ x ∈ U, ∀ θ,
      f m (x, (rsel i m, θ)) = c + H.decode (g i x) m θ) :
    N04NegativeChartAngularStateBudget p (fun _ => 1) U l h J := by
  obtain ⟨KH, hKH, hheight⟩ := hheightBound
  obtain ⟨B, hb⟩ := hg.circle_diagonal_stateBudget hp hIp hH hpos hg.choose
  refine ⟨B, fun K => ?_⟩
  obtain ⟨D, hD⟩ := hb K
  refine ⟨D, fun R hR N k hk b hbN => ?_⟩
  obtain ⟨C, hC, hc⟩ := hD R hR N k hk b hbN
  refine ⟨|c| + C * KH, add_nonneg (abs_nonneg _) (mul_nonneg hC hKH),
    fun m x hx w hxlow hwlow y hy => ?_⟩
  obtain ⟨i, hi⟩ := hcover m y.1 hy
  have hr : rsel i m ∈ Ioo (l m) (h m) := hi.symm ▸ hy
  have hid := jointMixedDiagonal_eq_circleAngularJet_add_const (J m) hH (hg.choose i) m hr c
    (heq i m hr) k b x w hx y.2
  have hyeta : (rsel i m, y.2) = y := Prod.ext hi rfl
  have hid' := (congrArg
    (fun q : PolarPoint => jointMixedDiagonal (J m) k 0 b x w q) hyeta).symm.trans hid
  let Q : ℝ := (1 + p (N + K * D + B + 1) x + p (N + K * D + B + 1) w) ^
    (((b + k * D : ℕ) : ℝ) / ((N + K * D : ℕ) + 1 : ℝ))
  have hQ : 1 ≤ Q := by
    apply Real.one_le_rpow
    · linarith only [apply_nonneg (p (N + K * D + B + 1)) x,
        apply_nonneg (p (N + K * D + B + 1)) w]
    · positivity
  have hc0 : |(if k = 0 ∧ b = 0 then c else 0)| ≤ |c| := by
    split_ifs <;> simp only [abs_zero, abs_nonneg, le_refl]
  have hbnd := hc i x hx w hxlow hwlow m y.2
  calc
    _ ≤ |(if k = 0 ∧ b = 0 then c else 0)| +
        |iteratedDeriv b (H.decode ((hg.choose i).D k x (fun _ => w)) m) y.2| :=
      (congrArg abs hid').trans_le (abs_add_le _ _)
    _ ≤ |c| * Q + (C * KH) * Q := add_le_add
      (hc0.trans (by nlinarith only [hQ, abs_nonneg c]))
      (hbnd.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hheight m) hC) (zero_le_one.trans hQ)))
    _ = _ := by dsimp only [Q]; ring

private theorem circle_sample_height_bounded {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ KH : ℝ, 0 ≤ KH ∧ ∀ m, T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH := by
  refine (materialSample_H_M_envelope hT hRef (γ := (3 / 4 : ℝ)) (by norm_num) 0).elim ?_
  intro KH hKH
  exact ⟨KH, hKH.1.le, fun m => by
    simpa only [Real.rpow_zero, mul_one] using hKH.2 m⟩

namespace N04RealizationStart

variable (W : N04RealizationStart)

private theorem sector_parameter_interpolation :
    HasInterpolation (pairGrading (sectorGrading W.S) realGrading) :=
  hasInterpolation_of_hasSmoothing (sectorPairGrading_monotone W.S)
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing W.hS) hasSmoothing_realGrading)

private abbrev ClosedRadiusSelector : Type :=
  {r : ℕ → ℝ // ∀ m, r m ∈ Icc (W.C.left m) (W.C.right m)}

private theorem closedRadius_cover (m : ℕ) (r : ℝ)
    (hr : r ∈ Ioo (W.C.left m) (W.C.right m)) :
    ∃ i : W.ClosedRadiusSelector, i.val m = r :=
  W.through03.1.1.closedRadiusSelector_cover m r ⟨hr.1.le, hr.2.le⟩

private theorem closedInverseSlope_family :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading W.S) realGrading)
      (W.S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood W.S W.base W.ε W.ε)
      (fun i : W.ClosedRadiusSelector =>
        W.through03.1.1.selectorInverseSlopeCircle W.hS W.hT i.val i.property) :=
  W.through03.1.1.n04FixedBase_selectorInverseSlopeCircle W.hS W.hT
    (W.cutoff.sector_flow_slope W.through03.1.1)
    (fun i : W.ClosedRadiusSelector => i.val) (fun i => i.property)

private theorem closedInverseSlope_decode (i : W.ClosedRadiusSelector) (m : ℕ)
    (x : StateDirections W.S × ℝ) (hx : x ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    (θ : ℝ) :
    returnFlowInverseSlope W.S W.C (liftSectorParameter W.S W.C x) m (i.val m, θ) =
      1 + (W.S.circle (3 / 4 : ℝ)).decode
        (W.through03.1.1.selectorInverseSlopeCircle W.hS W.hT i.val i.property x) m θ := by
  have hd := W.through03.1.1.selectorInverseSlopeCircle_decode
    W.hS W.hT i.val i.property x hx m θ
  have he := congrArg (fun a : ℝ => 1 + a) hd
  exact (he.trans ((add_comm _ _).trans (sub_add_cancel _ _))).symm

theorem negativeInverseSlope_angular_stateBudget :
    N04NegativeChartAngularStateBudget (pairGrading (sectorGrading W.S) realGrading)
      (fun _ => 1) (sectorNeighborhood W.S W.base W.ε W.ε) W.C.left W.C.right
      W.negativeInverseSlopeJointTower := by
  exact circle_angular_stateBudget_add_const W.closedInverseSlope_family
    (sectorPairGrading_monotone W.S)
    W.sector_parameter_interpolation (W.hS.2.1 (3 / 4 : ℝ))
    (material_circle_sample_weights_pos W.hT W.radial.1).2
    (circle_sample_height_bounded W.hT W.radial.1)
    W.C.left W.C.right (fun i : W.ClosedRadiusSelector => i.val) W.closedRadius_cover
    W.negativeInverseSlopeJointTower 1
    (fun i m _ x hx θ => W.closedInverseSlope_decode i m x hx θ)

theorem negativePulledCorrection_angular_stateBudget :
    N04NegativeChartAngularStateBudget (pairGrading (sectorGrading W.S) realGrading)
      (fun m => W.T.H (W.T.sample m) ^ (3 / 4 : ℝ))
      (sectorNeighborhood W.S W.base W.ε W.ε) W.C.left W.C.right
      W.negativePulledCorrectionJointTower := by
  have hg := W.through03.1.1.n04FixedBase_actualPulledCorrectionCircle W.hS W.hT
    (W.cutoff.sector_flow_slope W.through03.1.1) W.through03.1.2
    W.cutoff.cutoff W.cutoff.range_on_component
    (fun i : W.ClosedRadiusSelector => i.val) (fun i => i.property)
  exact hg.realized_strip_angular_stateBudget (sectorPairGrading_monotone W.S)
    W.sector_parameter_interpolation (W.hS.2.1 (3 / 4 : ℝ))
    (material_circle_sample_weights_pos W.hT W.radial.1).2 W.C.left W.C.right
    (fun i : W.ClosedRadiusSelector => i.val) W.closedRadius_cover
    W.negativePulledCorrectionJointTower (fun i m _ x hx θ =>
      (W.through03.1.1.returnCorrectionPulledDisplacementCircleLinear_decode W.hS W.hT
        W.cutoff.cutoff W.cutoff.range_on_component i.val i.property x hx
        (W.R.residual (liftSectorParameter W.S W.C x)) m θ).symm)

theorem negativeFirstIntegralDefect_angular_stateBudget :
    N04NegativeChartAngularStateBudget (pairGrading (sectorGrading W.S) realGrading)
      (fun m => W.T.H (W.T.sample m) ^ (3 / 4 : ℝ))
      (sectorNeighborhood W.S W.base W.ε W.ε) W.C.left W.C.right
      W.negativeFirstIntegralDefectJointTower := by
  have hg := W.through03.1.1.n04FixedBase_minusFirstIntegralSelectorCircle W.hS W.hT
    W.cutoff.cutoff W.cutoff.range_on_component
    (W.cutoff.sector_flow_slope W.through03.1.1)
    (fun i : W.ClosedRadiusSelector => i.val) (fun i => i.property)
  apply hg.realized_strip_angular_stateBudget (sectorPairGrading_monotone W.S)
    W.sector_parameter_interpolation (W.hS.2.1 (3 / 4 : ℝ))
    (material_circle_sample_weights_pos W.hT W.radial.1).2 W.C.left W.C.right
    (fun i : W.ClosedRadiusSelector => i.val) W.closedRadius_cover
    W.negativeFirstIntegralDefectJointTower
  intro i m _ x hx θ
  have hd := W.through03.1.1.n04NegativeChartMinusFirstIntegralSelectorCircle_decode W.hS W.hT
    W.cutoff.cutoff W.cutoff.range_on_component i.val i.property x hx m θ
  simpa only [negativeFirstIntegralDefect, negativeMinusFirstIntegral, W.minusFlow_eq] using hd.symm

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeFirstIntegralDefect_angular_stateBudget'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeFirstIntegralDefect_angular_stateBudget
