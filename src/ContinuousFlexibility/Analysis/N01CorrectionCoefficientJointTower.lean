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

set_option backward.isDefEq.respectTransparency false

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

def N01Properties.returnCorrectionLocalCoefficient_parameterSpatialTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2) := by
  have hW := ((sectorNeighborhood_isOpen S base ε ε).prod
    (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))).prod
      ((isOpen_Ioo : IsOpen (Ioo l h)).prod (isOpen_univ : IsOpen (univ : Set ℝ)))
  let L := correctionStateSpatialProjection S
  let P := parameterAngularReflection ((StateDirections S × ℝ) × CircleSpace S)
  have hL : MapsTo L
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ)) :=
    fun x hx => ⟨hx.1.1, hx.2⟩
  have hP : MapsTo P
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) :=
    fun x hx => ⟨hx.1, hx.2.1, mem_univ _⟩
  let JV := hN.returnCorrectionVelocity_parameterSpatialTower hS hT χ hχrange hχ
    m l h hl hh hdisc
  let JVactual := (hN.returnCorrectionVelocity_actual_parameterSpatialTower hS hT χ hχrange hχ
    m l h hl hh hdisc hR).compLinear L hW hL
  let JD := (reflectedVelocityDirections JV (JV.compLinear P hW hP)).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
        returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2))
    (by intro x hx; simp only [returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  let JE := (reflectedVelocityDirections JVactual (JVactual.compLinear P hW hP)).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1)),
        returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))))
    (by intro x hx; simp only [returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  have hLfull : MapsTo L
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (C.left m) (C.right m) ×ˢ univ)) :=
    fun x hx => ⟨hx.1.1, ⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩, mem_univ _⟩
  let Jcoeff (i : Fin 3) :=
    (hN.originalCoefficient_parameterSpatialTower hS hT m j hcell i).compLinear L hW hLfull
  let JA := (Jcoeff 0).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2)
    (by intro x hx; simp only [originalCoefficientEntry, if_pos rfl])
  let JB := (Jcoeff 1).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2)
    (by intro x hx; norm_num [originalCoefficientEntry])
  let JC := (Jcoeff 2).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2)
    (by intro x hx; norm_num [originalCoefficientEntry])
  let Jdisc := ((smoothDirectionsProd (JB.mul JB) (JA.mul JC)).comp_contDiff isOpen_univ
    (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ _ => mem_univ _)).congrOn
      (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
            (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2)
      (by intro x hx; simp only [pow_two])
  let JQ := Jdisc.comp_contDiff isOpen_Ioi
    (contDiffOn_id.sqrt (fun q (hq : q ∈ Ioi (0 : ℝ)) => ne_of_gt hq))
    (fun x hx => hdisc x.1.1 hx.1.1 x.2 hx.2.1)
  apply (coefficientPolynomialDirections JA JB JQ JE JD).congrOn
  intro x hx
  have hp : x.2 ∈ annularOpen D := hN.negativeComponent_subset_annularOpen m
    ⟨⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩, mem_univ _⟩
  exact (returnCorrectionLocalCoefficientError_cancel_denominators D S C R χ
    (liftSectorParameter S C x.1.1) m x.2 x.1.2
    (hN.originalRadialCoefficient_pos
      (liftSectorParameter_mem_stateNeighborhood hx.1.1 le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x.1.1) hp).ne').symm

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
