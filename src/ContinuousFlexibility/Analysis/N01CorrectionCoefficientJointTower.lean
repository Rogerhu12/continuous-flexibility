import ContinuousFlexibility.Analysis.N01CoefficientJointTower
import ContinuousFlexibility.Analysis.N01CorrectionCoefficientJets
import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientJetSupport

/-!
# The actual correction coefficients jointly in parameters and space

The independently linear velocity, the velocity at the actual residual,
and the original coefficients all have genuine joint towers on the same
positive optical strip. The division-free reconstruction identifies the
result with the original coefficient error, including its zero values
where the cutoff derivative vanishes.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientJointTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

def correctionStateSpatialProjection (S : PhysicalSpacesData) :
    (((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) →L[ℝ]
      (StateDirections S × ℝ) × PolarPoint :=
  ((ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) (CircleSpace S)).comp
    (ContinuousLinearMap.fst ℝ ((StateDirections S × ℝ) × CircleSpace S) PolarPoint)).prod
      (ContinuousLinearMap.snd ℝ ((StateDirections S × ℝ) × CircleSpace S) PolarPoint)

def parameterAngularReflection (E : Type*)
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] :
    (E × PolarPoint) →L[ℝ] E × PolarPoint :=
  (ContinuousLinearMap.fst ℝ E PolarPoint).prod
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-(ContinuousLinearMap.snd ℝ ℝ ℝ))).comp
      (ContinuousLinearMap.snd ℝ E PolarPoint))

private theorem correctionStateSpatialProjection_apply (S : PhysicalSpacesData)
    (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) :
    correctionStateSpatialProjection S x = (x.1.1, x.2) := by
  simp only [correctionStateSpatialProjection, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

private theorem parameterAngularReflection_apply (E : Type*)
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] (x : E × PolarPoint) :
    parameterAngularReflection E x = (x.1, (x.2.1, -x.2.2)) := by
  simp only [parameterAngularReflection, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    neg_apply]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
  (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)
  (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ p : PolarPoint,
    p.1 ∈ Ioo l h →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

set_option diagnostics true in
include hN hS hT hR hχ hχrange j hcell hl hh hdisc in
private theorem returnCorrectionLocalCoefficient_parameterSpatialTower_nonempty :
    Nonempty (SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2)) := by
  refine ⟨?_⟩
  have hW : IsOpen
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo l h ×ˢ (univ : Set ℝ))) :=
    ((sectorNeighborhood_isOpen S base ε ε).prod
      (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))).prod
        ((isOpen_Ioo : IsOpen (Ioo l h)).prod (isOpen_univ : IsOpen (univ : Set ℝ)))
  let L : (((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) →L[ℝ]
      (StateDirections S × ℝ) × PolarPoint := correctionStateSpatialProjection S
  let P : (((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) →L[ℝ]
      ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint :=
    parameterAngularReflection ((StateDirections S × ℝ) × CircleSpace S)
  have hL : MapsTo L
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ)) := by
    intro x hx
    simpa only [L, correctionStateSpatialProjection_apply] using
      (show (x.1.1, x.2) ∈ sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ) from
        ⟨hx.1.1, hx.2⟩)
  have hP : MapsTo P
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) := by
    intro x hx
    simpa only [P, parameterAngularReflection_apply] using
      (show (x.1, (x.2.1, -x.2.2)) ∈
          (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ) from
        ⟨hx.1, hx.2.1, mem_univ _⟩)
  let JV : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2) :=
    hN.returnCorrectionVelocity_parameterSpatialTower hS hT χ hχrange hχ
      m l h hl hh hdisc
  let JVactual : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1)
          m x.2 (R.residual (liftSectorParameter S C x.1.1))) :=
    ((hN.returnCorrectionVelocity_actual_parameterSpatialTower hS hT χ hχrange hχ
      m l h hl hh hdisc hR).compLinear L hW hL).congrOn (by
        intro x hx
        simp only [L, correctionStateSpatialProjection_apply])
  let JD : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2)) :=
    (reflectedVelocityDirections JV (JV.compLinear P hW hP)).congrOn (by
      intro x hx
      simp only [P, parameterAngularReflection_apply,
        returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  let JE : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)),
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)))) :=
    (reflectedVelocityDirections JVactual (JVactual.compLinear P hW hP)).congrOn (by
      intro x hx
      simp only [P, parameterAngularReflection_apply,
        returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  have hLfull : MapsTo L
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (C.left m) (C.right m) ×ˢ univ)) := by
    intro x hx
    simpa only [L, correctionStateSpatialProjection_apply] using
      (show (x.1.1, x.2) ∈
          sectorNeighborhood S base ε ε ×ˢ (Ioo (C.left m) (C.right m) ×ˢ univ) from
        ⟨hx.1.1, ⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩, mem_univ _⟩)
  let Jcoeff (i : Fin 3) : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        originalCoefficientEntry D S C i (liftSectorParameter S C x.1.1) x.2) :=
    ((hN.originalCoefficient_parameterSpatialTower hS hT m j hcell i).compLinear
      L hW hLfull).congrOn (by
        intro x hx
        simp only [L, correctionStateSpatialProjection_apply])
  let JA : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2) :=
    (Jcoeff 0).congrOn
      (by intro x hx; simp only [originalCoefficientEntry, eq_self_iff_true, ite_true])
  let JB : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2) :=
    (Jcoeff 1).congrOn (by intro x hx; norm_num [originalCoefficientEntry])
  let JC : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2) :=
    (Jcoeff 2).congrOn (by intro x hx; norm_num [originalCoefficientEntry])
  let Jdisc : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
            (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2) :=
    ((smoothDirectionsProd (JB.mul JB) (JA.mul JC)).comp_contDiff
      (g := fun y : ℝ × ℝ => y.1 - y.2) (V := univ) isOpen_univ
      (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ _ => mem_univ _)).congrOn
      (by intro x hx; simp only [pow_two])
  let JQ : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
            (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2)) :=
    Jdisc.comp_contDiff (g := Real.sqrt) (V := Ioi (0 : ℝ)) isOpen_Ioi
      (contDiffOn_id.sqrt (fun q hq => ne_of_gt hq))
      (fun x hx => hdisc x.1.1 hx.1.1 x.2 hx.2.1)
  let F : (((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) → ℝ × ℝ := fun x =>
    (-(originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
        returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
      -2 * (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 *
          returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2 -
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
          returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)) *
          returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2 +
        2 * Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
            (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2) *
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2 +
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)) *
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2)
  let K : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) F :=
    coefficientPolynomialDirections JA JB JQ JE JD
  have hF : EqOn F
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2)
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) := by
    intro x hx
    have hp : x.2 ∈ annularOpen D := hN.negativeComponent_subset_annularOpen m
      ⟨⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩, mem_univ _⟩
    exact (returnCorrectionLocalCoefficientError_cancel_denominators D S C R χ
      (liftSectorParameter S C x.1.1) m x.2 x.1.2
      (hN.originalRadialCoefficient_pos
        (liftSectorParameter_mem_stateNeighborhood hx.1.1 le_rfl)
        (hN.2.2.1.liftSectorParameter_sector x.1.1) hp).ne').symm
  exact K.congrOn hF

def N01Properties.returnCorrectionLocalCoefficient_parameterSpatialTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2) :=
  Classical.choice (returnCorrectionLocalCoefficient_parameterSpatialTower_nonempty
    (hN := hN) (hS := hS) (hT := hT) (hR := hR) (χ := χ) (hχ := hχ)
    (hχrange := hχrange) (m := m) (j := j) (hcell := hcell) (l := l) (h := h)
    (hl := hl) (hh := hh) (hdisc := hdisc))

def N01Properties.returnCorrectionCoefficient_parameterSpatialTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1.1) x.2 x.1.2) :=
  (hN.returnCorrectionLocalCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
    m j hcell l h hl hh hdisc).congrOn (by
      intro x hx
      exact (congrArg (fun L : CircleSpace S →ₗ[ℝ] (ℝ × ℝ) => L x.1.2)
        (returnCorrectionCoefficientError_eq_local hN.2.2.2.1.2.2.1 R χ
          (liftSectorParameter S C x.1.1) m x.2
          ⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩)).symm)

end ContinuousFlexibility.Statements
