import ContinuousFlexibility.Analysis.N04PulledFieldsActualAngularGrowth
import ContinuousFlexibility.Analysis.N04PulledFieldsActualTransportIdentities
import ContinuousFlexibility.Analysis.N04PulledFieldsCharacteristicPower
import ContinuousFlexibility.Analysis.N04PulledFieldsRadialCutoffGrowth
import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseMixedGrowth
import ContinuousFlexibility.Analysis.N01CharacteristicJointGrowth
import ContinuousFlexibility.Analysis.N01ReturnTransportSpatialTowers
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Fixed-base mixed growth of the actual N02 velocity

The original characteristic, inverse slope and actual pulled residual
provide the primitive towers. Their radial transport equations give
the velocity estimate on the original sector parameter space, with
one low order before all parameter orders and one sampled height factor.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

local instance n04PulledFieldsActualVelocityStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

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
  obtain ⟨JL, B, L, _, _, hJL⟩ := hN.exists_minusCharacteristicSpeed_strip_joint_growth
    hS hT j hcell l h hl hh hlam hP hpositive
  have hp := sectorPairGrading_monotone S
  have hI : HasInterpolation (pairGrading (sectorGrading S) realGrading) :=
    hasInterpolation_of_hasSmoothing hp
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  have hV (m : ℕ) : IsOpen (Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ (univ : Set ℝ))) :=
    (sectorNeighborhood_convex S base ε ε).prod ((convex_Ioo (l m) (h m)).prod convex_univ)
  obtain ⟨B', _, hb⟩ := hJL.n04PulledFields_fixedBase_mixedPowerGrowth
    hp hI (fun m => one_le_radialE_of_nat (D.cellIndex (j m))) hV hc
  exact ⟨JL, B', hb⟩

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
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hH (m : ℕ) : 0 ≤ H m := Real.rpow_nonneg
    ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hV (m : ℕ) : IsOpen (V m) := isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ (U ×ˢ V m) :=
    (sectorNeighborhood_convex S base ε ε).prod ((convex_Ioo (l m) (h m)).prod convex_univ)
  have hdisc (m : ℕ) (x : E) (hx : x ∈ U) (y : PolarPoint)
      (hy : y.1 ∈ Ioo (l m) (h m)) :
      0 < (originalCoefficients D S C (liftSectorParameter S C x)).b y ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C x)).a y *
          (originalCoefficients D S C (liftSectorParameter S C x)).c y := by
    have hd : 0 < lam * W m ^ (-P) / 2 :=
      half_pos (mul_pos hlam (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hW m)) _))
    exact (pow_pos hd 2).trans_le (hpositive (liftSectorParameter S C x)
      (liftSectorParameter_mem_stateNeighborhood hx le_rfl) m y hy).2
  obtain ⟨JL, hL⟩ := hN.n04PulledFields_existsCharacteristicPower
    hS hT j hcell l h hl hh hlam hP hpositive
  let JA : ∀ m, SmoothDirections (U ×ˢ V m) (fA m) := fun m =>
    hN.returnFlowInverseSlope_parameterSpatialTower
      hS hT m (l m) (h m) (hl m) (hh m) (hdisc m)
  let JZ : ∀ m, SmoothDirections (U ×ˢ V m) (fZ m) := fun m =>
    hN.returnCorrectionPulledResidual_parameterSpatialTower
      hS hT m (l m) (h m) (hl m) (hh m) (hdisc m) χ hχ hχrange hR
  obtain ⟨KH, hKH, hKHbound⟩ := material_sample_height_coefficient_power_bounded
    hN.1.1 hT (fun m => m) 0 (by norm_num : 0 < (3 / 4 : ℝ))
  have hheight (m : ℕ) : H m ≤ KH := by
    simpa only [H, Real.rpow_zero, mul_one] using hKHbound m
  have hA := hN.n04PulledFields_returnFlowInverseSlope_angular_growth
    hS hT hflow l h hl hh KH hKH.le hheight W JA
  have hZ := hN.n04PulledFields_actualPulledDisplacement_angular_growth
    hS hT hflow l h hl hh χ hχrange hR W JZ
  refine n04PulledFields_radialCutoff_fixedBase_growth p W H
    (sectorPairGrading_monotone S) hW hH KH hKH.le hheight hU hV hc
    χ hχ hcutoff JL JA JZ JV hL hA hZ ?_ ?_ ?_
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
