module

public import ContinuousFlexibility.Analysis.N04PulledFieldsActualAngularGrowth
public import ContinuousFlexibility.Analysis.N04PulledFieldsActualTransportIdentities
public import ContinuousFlexibility.Analysis.N04PulledFieldsCharacteristicPower
public import ContinuousFlexibility.Analysis.N04PulledFieldsRadialCutoffGrowth
public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseMixedGrowth
public import ContinuousFlexibility.Analysis.N01CharacteristicJointGrowth
public import ContinuousFlexibility.Analysis.N01ReturnTransportSpatialTowers
public import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Fixed-base mixed growth of the actual N02 velocity

The original characteristic, inverse slope and actual pulled residual
provide the primitive towers. Their radial transport equations give
the velocity estimate on the original sector parameter space, with
one low order before all parameter orders and one sampled height factor.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Select the genuine tower and its quantitative witness before specializing
the parameter model. This keeps the existential elimination abstract. -/
private theorem n04PulledFields_characteristicPower_of_existsJointGrowth
    {p : ℕ → Seminorm ℝ E} {W : I → ℝ}
    {U : Set E} {V : I → Set PolarPoint} {f : I → E × PolarPoint → ℝ}
    {base loss : ℕ}
    (hJ : ∃ J : ∀ i, SmoothDirections (U ×ˢ V i) (f i),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W J B L)
    (hp : Monotone p) (hIp : HasInterpolation p) (hW : ∀ i, 1 ≤ W i)
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i)) :
    ∃ J : ∀ i, SmoothDirections (U ×ˢ V i) (f i),
      ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
        N04PulledFieldsMixedPowerGrowth p W (fun _ => 1) J K B highLoss shift := by
  let J : ∀ i, SmoothDirections (U ×ˢ V i) (f i) := hJ.choose
  let bounds : ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧
      UniformWeightedJointGrowth p W J B L := hJ.choose_spec
  let B : ℕ := bounds.choose
  let L : ℕ := bounds.choose_spec.choose
  have hj : UniformWeightedJointGrowth p W J B L :=
    bounds.choose_spec.choose_spec.2.2
  let power := hj.n04PulledFields_fixedBase_mixedPowerGrowth hp hIp hW hV hc
  exact ⟨J, power.choose, power.choose_spec.2⟩

/-- Assemble the transport estimate while its towers and height bound
are abstract. The concrete application only supplies actual identities. -/
private theorem n04PulledFields_radialCutoff_growth_of_existsPrimitives
    {U : Set E} {V : I → Set PolarPoint}
    (p : ℕ → Seminorm ℝ E) (W H : I → ℝ)
    (hp : Monotone p) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    (height : ∃ KH : ℝ, 0 ≤ KH ∧ ∀ i, H i ≤ KH)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (χ : I → ℝ → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hcutoff : ∀ k : ℕ, ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧ ∀ i r,
      |iteratedDeriv k (χ i) r| ≤ C * W i ^ P)
    {fL fA fZ fV : I → E × PolarPoint → ℝ}
    (JA : ∀ i, SmoothDirections (U ×ˢ V i) (fA i))
    (JZ : ∀ i, SmoothDirections (U ×ˢ V i) (fZ i))
    (JV : ∀ i, SmoothDirections (U ×ˢ V i) (fV i))
    (characteristic : ∃ JL : ∀ i, SmoothDirections (U ×ˢ V i) (fL i),
      ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
        N04PulledFieldsMixedPowerGrowth p W (fun _ => 1) JL K B highLoss shift)
    (slope : ∀ KH : ℝ, 0 ≤ KH → (∀ i, H i ≤ KH) →
      ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
        N04PulledFieldsAngularPowerGrowth p W (fun _ => 1) JA K B highLoss shift)
    (displacement : ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsAngularPowerGrowth p W H JZ K B highLoss shift)
    (hAr : ∀ i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fA i (x, q)) y =
        angularPartial (fun q => fL i (x, q)) y * fA i (x, y) -
          fL i (x, y) * angularPartial (fun q => fA i (x, q)) y)
    (hZr : ∀ i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fZ i (x, q)) y =
        -((fL i (x, y) + deriv (χ i) y.1 * fA i (x, y) * fZ i (x, y)) *
          angularPartial (fun q => fZ i (x, q)) y))
    (hVeq : ∀ i, EqOn (fun x => deriv (χ i) x.2.1 * fA i x * fZ i x)
      (fV i) (U ×ˢ V i)) :
    N04PulledFieldsFixedBaseMixedGrowth p W H JV := by
  let KH : ℝ := height.choose
  let JL : ∀ i, SmoothDirections (U ×ˢ V i) (fL i) := characteristic.choose
  exact n04PulledFields_radialCutoff_fixedBase_growth p W H
    hp hW hH KH height.choose_spec.1 height.choose_spec.2 hU hV hc
    χ hχ hcutoff JL JA JZ JV characteristic.choose_spec
    (slope KH height.choose_spec.1 height.choose_spec.2) displacement hAr hZr hVeq

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

local instance n04PulledFieldsActualVelocityStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem n04PulledFields_velocityParameterInterpolation
    (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (pairGrading (sectorGrading S) realGrading) :=
  hasInterpolation_of_hasSmoothing (sectorPairGrading_monotone S)
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)

private theorem n04PulledFields_velocitySampleHeight
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) :
    ∃ KH : ℝ, 0 ≤ KH ∧ ∀ m, T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH := by
  let height := material_sample_height_coefficient_power_bounded
    hN.1.1 hT (fun m => m) 0 (by norm_num : 0 < (3 / 4 : ℝ))
  refine ⟨height.choose, height.choose_spec.1.le, fun m => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using height.choose_spec.2 m

private theorem n04PulledFields_velocityStripDiscriminant
    (j : ℕ → ℕ) (l h : ℕ → ℝ) {lam P : ℝ} (hlam : 0 < lam)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a y ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b y ^ 2 -
        (originalCoefficients D S C z).a y * (originalCoefficients D S C z).c y)
    (m : ℕ) (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (y : PolarPoint) (hy : y.1 ∈ Ioo (l m) (h m)) :
    0 < (originalCoefficients D S C (liftSectorParameter S C x)).b y ^ 2 -
      (originalCoefficients D S C (liftSectorParameter S C x)).a y *
        (originalCoefficients D S C (liftSectorParameter S C x)).c y := by
  have hd : 0 < lam * radialE (D.cellIndex (j m)) ^ (-P) / 2 :=
    half_pos (mul_pos hlam (Real.rpow_pos_of_pos
      (zero_lt_one.trans_le (one_le_radialE_of_nat _)) _))
  exact (pow_pos hd 2).trans_le (hpositive (liftSectorParameter S C x)
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl) m y hy).2

/-- The original characteristic has a genuine tower and a power prefix
whose low grading precedes every parameter order. -/
theorem N01Properties.n04PulledFields_existsCharacteristicPower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a y ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b y ^ 2 -
        (originalCoefficients D S C z).a y * (originalCoefficients D S C z).c y) :
    ∃ JL : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2),
      ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
        N04PulledFieldsMixedPowerGrowth (pairGrading (sectorGrading S) realGrading)
          (fun m => radialE (D.cellIndex (j m))) (fun _ => 1) JL K B highLoss shift := by
  exact n04PulledFields_characteristicPower_of_existsJointGrowth
    (hN.exists_minusCharacteristicSpeed_strip_joint_growth
      hS hT j hcell l h hl hh hlam hP hpositive)
    (sectorPairGrading_monotone S) (n04PulledFields_velocityParameterInterpolation hS)
    (fun m => one_le_radialE_of_nat (D.cellIndex (j m)))
    (fun _ => isOpen_Ioo.prod isOpen_univ)
    (fun m => (sectorNeighborhood_convex S base ε ε).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ))

/-- The same supplied actual velocity tower has one fixed low grading,
loss depending only on parameter order, and the full sampled height. -/
theorem N01Properties.n04PulledFields_actualVelocity_fixedBaseMixedGrowth
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {R : ReturnEquationData S} (hR : N02Properties D T S C R base ε)
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
        deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a y ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b y ^ 2 -
        (originalCoefficients D S C z).a y * (originalCoefficients D S C z).c y)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ C * radialE (D.cellIndex (j m)) ^ Q)
    (JV : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1) m x.2
          (R.residual (liftSectorParameter S C x.1)))) :
    N04PulledFieldsFixedBaseMixedGrowth (pairGrading (sectorGrading S) realGrading)
      (fun m => radialE (D.cellIndex (j m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) JV := by
  let E := StateDirections S × ℝ
  let U : Set E := sectorNeighborhood S base ε ε
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let p : ℕ → Seminorm ℝ E := pairGrading (sectorGrading S) realGrading
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let H : ℕ → ℝ := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  let fA : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2
  let fZ : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1) m x.2
      (R.residual (liftSectorParameter S C x.1))
  have hdisc := n04PulledFields_velocityStripDiscriminant j l h hlam hpositive
  let JA : ∀ m, SmoothDirections (U ×ˢ V m) (fA m) := fun m =>
    hN.returnFlowInverseSlope_parameterSpatialTower
      hS hT m (l m) (h m) (hl m) (hh m) (hdisc m)
  let JZ : ∀ m, SmoothDirections (U ×ˢ V m) (fZ m) := fun m =>
    hN.returnCorrectionPulledResidual_parameterSpatialTower
      hS hT m (l m) (h m) (hl m) (hh m) (hdisc m) χ hχ hχrange hR
  refine n04PulledFields_radialCutoff_growth_of_existsPrimitives p W H
    (sectorPairGrading_monotone S) (fun m => one_le_radialE_of_nat _)
    (fun m => Real.rpow_nonneg
      ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _)
    (n04PulledFields_velocitySampleHeight hN hT)
    (sectorNeighborhood_isOpen S base ε ε) (fun _ => isOpen_Ioo.prod isOpen_univ)
    (fun m => (sectorNeighborhood_convex S base ε ε).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ))
    χ hχ hcutoff JA JZ JV
    (hN.n04PulledFields_existsCharacteristicPower hS hT j hcell l h hl hh hlam hP hpositive)
    (fun KH hKH hheight => hN.n04PulledFields_returnFlowInverseSlope_angular_growth
      hS hT hflow l h hl hh KH hKH hheight W JA)
    (hN.n04PulledFields_actualPulledDisplacement_angular_growth
      hS hT hflow l h hl hh χ hχrange hR W JZ) ?_ ?_ ?_
  · intro m x hx y hy
    exact hN.n04PulledFields_slope_radialEquation hS hT m x hx y
      ⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩ (hdisc m x hx y hy.1)
  · intro m x hx y hy
    exact hN.n04PulledFields_actualDisplacement_radialEquation hS hT hR χ m
      (hχ m) (hχrange m) x hx y ⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩
  · intro m x _
    exact (returnCorrectionVelocityLinear_eq_transportProduct D S C χ
      (liftSectorParameter S C x.1) m x.2 (R.residual (liftSectorParameter S C x.1))).symm

end ContinuousFlexibility.Statements
