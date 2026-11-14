module

public import ContinuousFlexibility.Analysis.N01CoefficientJointTower
public import ContinuousFlexibility.Analysis.N01CorrectionCoefficientJets
public import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientJetSupport

/-!
# The actual correction coefficients jointly in parameters and space

The independently linear velocity, the velocity at the actual residual,
and the original coefficients all have genuine joint towers on the same
positive optical strip. The division-free reconstruction identifies the
result with the original coefficient error, including its zero values
where the cutoff derivative vanishes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientJointTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

private def n01CorrectionCoefficientJointTowerCircleSMul (S : PhysicalSpacesData) :
    SMul ℝ (CircleSpace S) :=
  Submodule.smul (R := ℝ) (S := ℝ)
    (ContinuousFlexibility.Analysis.compatibleSubmodule
      (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond)

private theorem n01CorrectionCoefficientJointTowerCircleSMul_eq (S : PhysicalSpacesData) :
    n01CorrectionCoefficientJointTowerCircleSMul S =
      (inferInstance : SMul ℝ (CircleSpace S)) := rfl

attribute [local instance] n01CorrectionCoefficientJointTowerCircleSMul

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

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

section ReflectionComposition

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : E → ℝ} {g : E → ℝ × ℝ}

private def reflectedVelocityDirections_compLinear_congr
    (J : SmoothDirections U f) (P : E →L[ℝ] E)
    (hU : IsOpen U) (hP : MapsTo P U U)
    (hfg : EqOn
      (fun x => ((f x - f (P x)) / 2, (-f (P x) - f x) / 2)) g U) :
    SmoothDirections U g :=
  (reflectedVelocityDirections
    (E := E) (U := U) (f := f) (g := fun x => f (P x))
    J (J.compLinear (E := E) (F := E) (G := ℝ)
      (U := U) (V := U) (f := f) P hU hP)).congrOn
        (F := E) (G := ℝ × ℝ) (U := U)
        (f := fun x => ((f x - f (P x)) / 2, (-f (P x) - f x) / 2))
        (g := g) hfg

private theorem reflectedVelocityDirections_compLinear_congr_D
    (J : SmoothDirections U f) (P : E →L[ℝ] E)
    (hU : IsOpen U) (hP : MapsTo P U U)
    (hfg : EqOn
      (fun x => ((f x - f (P x)) / 2, (-f (P x) - f x) / 2)) g U) :
    (reflectedVelocityDirections_compLinear_congr J P hU hP hfg).D =
      (reflectedVelocityDirections
        (E := E) (U := U) (f := f) (g := fun x => f (P x))
        J (J.compLinear (E := E) (F := E) (G := ℝ)
          (U := U) (V := U) (f := f) P hU hP)).D := rfl

end ReflectionComposition

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

include hN hl hh in
private theorem correctionJointStripRadialCoefficient_pos
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    {p : PolarPoint} (hp : p.1 ∈ Ioo l h) :
    0 < (originalCoefficients D S C (liftSectorParameter S C z)).a p := by
  have hpD : p ∈ annularOpen D := hN.negativeComponent_subset_annularOpen
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε) m
    ⟨⟨hl.trans hp.1, hp.2.trans hh⟩, mem_univ _⟩
  exact hN.originalRadialCoefficient_pos
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    (z := liftSectorParameter S C z) (p := p)
    (liftSectorParameter_mem_stateNeighborhood
      (S := S) (C := C) (base := base) (ε := ε) (q0 := ε) (z := z) hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector (D := D) (S := S) (C := C) z) hpD

private def originalCoefficient_correctionParameterSpatialTower (i : Fin 3) :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        originalCoefficientEntry D S C i (liftSectorParameter S C x.1.1) x.2) := by
  have hW : IsOpen
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo l h ×ˢ (univ : Set ℝ))) :=
    ((sectorNeighborhood_isOpen S base ε ε).prod
      (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))).prod
        ((isOpen_Ioo : IsOpen (Ioo l h)).prod (isOpen_univ : IsOpen (univ : Set ℝ)))
  let L : (((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) →L[ℝ]
      (StateDirections S × ℝ) × PolarPoint := correctionStateSpatialProjection S
  have hLfull : MapsTo L
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (C.left m) (C.right m) ×ˢ univ)) := by
    intro x hx
    simpa only [L, correctionStateSpatialProjection_apply] using
      (show (x.1.1, x.2) ∈
          sectorNeighborhood S base ε ε ×ˢ (Ioo (C.left m) (C.right m) ×ˢ univ) from
        ⟨hx.1.1, ⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩, mem_univ _⟩)
  exact ((hN.originalCoefficient_parameterSpatialTower
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hS hT m j hcell i).compLinear
      (E := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint)
      (F := (StateDirections S × ℝ) × PolarPoint) (G := ℝ)
      (U := sectorNeighborhood S base ε ε ×ˢ (Ioo (C.left m) (C.right m) ×ˢ univ))
      (V := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      L hW hLfull).congrOn
        (F := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) (G := ℝ)
        (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) (by
          intro x hx
          simp only [L, correctionStateSpatialProjection_apply])

private def correctionJointIndependentDriftSpeedTower :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2)) := by
  have hW : IsOpen
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo l h ×ˢ (univ : Set ℝ))) :=
    ((sectorNeighborhood_isOpen S base ε ε).prod
      (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))).prod
        ((isOpen_Ioo : IsOpen (Ioo l h)).prod (isOpen_univ : IsOpen (univ : Set ℝ)))
  let P : (((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) →L[ℝ]
      ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint :=
    parameterAngularReflection ((StateDirections S × ℝ) × CircleSpace S)
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
    hN.returnCorrectionVelocity_parameterSpatialTower
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT χ hχrange hχ
      m l h hl hh hdisc
  let JD : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2)) :=
    reflectedVelocityDirections_compLinear_congr
      (E := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint)
      (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (f := fun x => returnCorrectionVelocityLinear D S C χ
        (liftSectorParameter S C x.1.1) m x.2 x.1.2)
      (g := fun x =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2))
      JV P hW hP (by
        intro x hx
        simp only [P, parameterAngularReflection_apply,
          returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  exact JD

private def correctionJointActualDriftSpeedTower :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)),
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)))) := by
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
  let JVactual : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1)
          m x.2 (R.residual (liftSectorParameter S C x.1.1))) :=
    ((hN.returnCorrectionVelocity_actual_parameterSpatialTower
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      (R := R) hS hT χ hχrange hχ m l h hl hh hdisc hR).compLinear
        (E := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint)
        (F := (StateDirections S × ℝ) × PolarPoint) (G := ℝ)
        (U := sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
        (V := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
        L hW hL).congrOn
          (F := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) (G := ℝ)
          (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) (by
            intro x hx
            simp only [L, correctionStateSpatialProjection_apply])
  let JE : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)),
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)))) :=
    reflectedVelocityDirections_compLinear_congr
      (E := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint)
      (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (f := fun x => returnCorrectionVelocityLinear D S C χ
        (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1)))
      (g := fun x =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)),
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1))))
      JVactual P hW hP (by
        intro x hx
        simp only [P, parameterAngularReflection_apply,
          returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  exact JE

private def correctionJointLocalCoefficientFromDriftSpeedTowers
    (JD : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2)))
    (JE : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)),
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1))))) :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2) := by
  let Jcoeff (i : Fin 3) : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        originalCoefficientEntry D S C i (liftSectorParameter S C x.1.1) x.2) :=
    originalCoefficient_correctionParameterSpatialTower
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      (hN := hN) (hS := hS) (hT := hT) (m := m) (j := j) (hcell := hcell)
      (l := l) (h := h) (hl := hl) (hh := hh) i
  let JA : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2) :=
    (Jcoeff 0).congrOn
      (F := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) (G := ℝ)
      (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (by intro x hx; simp only [originalCoefficientEntry, eq_self_iff_true, ite_true])
  let JB : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2) :=
    (Jcoeff 1).congrOn
      (F := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) (G := ℝ)
      (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) (by
        intro x hx
        simp only [originalCoefficientEntry, show (1 : Fin 3) ≠ 0 by decide,
          eq_self_iff_true, ite_false, ite_true])
  let JC : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2) :=
    (Jcoeff 2).congrOn
      (F := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) (G := ℝ)
      (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) (by
        intro x hx
        simp only [originalCoefficientEntry, show (2 : Fin 3) ≠ 0 by decide,
          show (2 : Fin 3) ≠ 1 by decide, ite_false])
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
    coefficientPolynomialSqrtDirections
      (E := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint)
      (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) JA JB JC JE JD
      (fun x hx => hdisc x.1.1 hx.1.1 x.2 hx.2.1)
  have hF : EqOn F
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2)
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) := by
    intro x hx
    exact (returnCorrectionLocalCoefficientError_cancel_denominators D S C R χ
      (liftSectorParameter S C x.1.1) m x.2 x.1.2
      (correctionJointStripRadialCoefficient_pos
        (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
        (hN := hN) (m := m) (l := l) (h := h) (hl := hl) (hh := hh)
        (z := x.1.1) (p := x.2) hx.1.1 hx.2.1).ne').symm
  exact K.congrOn
    (F := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) (G := ℝ × ℝ)
    (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) hF

include hN hS hT hR hχ hχrange j hcell hl hh hdisc in
private theorem returnCorrectionLocalCoefficient_parameterSpatialTower_nonempty :
    Nonempty (SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2)) := by
  refine ⟨?_⟩
  let JD : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2)) :=
    correctionJointIndependentDriftSpeedTower
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      (hN := hN) (hS := hS) (hT := hT) (χ := χ) (hχ := hχ) (hχrange := hχrange)
      (m := m) (l := l) (h := h) (hl := hl) (hh := hh) (hdisc := hdisc)
  let JE : SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)),
          returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1)))) :=
    correctionJointActualDriftSpeedTower
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      (hN := hN) (hS := hS) (hT := hT) (hR := hR) (χ := χ)
      (hχ := hχ) (hχrange := hχrange) (m := m) (l := l) (h := h)
      (hl := hl) (hh := hh) (hdisc := hdisc)
  exact correctionJointLocalCoefficientFromDriftSpeedTowers
    (D := D) (T := T) (S := S) (C := C) (R := R) (base := base) (loss := loss) (ε := ε)
    (hN := hN) (hS := hS) (hT := hT) (χ := χ) (m := m) (j := j) (hcell := hcell)
    (l := l) (h := h) (hl := hl) (hh := hh) (hdisc := hdisc) JD JE

def N01Properties.returnCorrectionLocalCoefficient_parameterSpatialTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionLocalCoefficientError D S C R χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2) :=
  Classical.choice (returnCorrectionLocalCoefficient_parameterSpatialTower_nonempty
    (D := D) (T := T) (S := S) (C := C) (R := R) (base := base) (loss := loss) (ε := ε)
    (hN := hN) (hS := hS) (hT := hT) (hR := hR) (χ := χ) (hχ := hχ)
    (hχrange := hχrange) (m := m) (j := j) (hcell := hcell) (l := l) (h := h)
    (hl := hl) (hh := hh) (hdisc := hdisc))

def N01Properties.returnCorrectionCoefficient_parameterSpatialTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1.1) x.2 x.1.2) :=
  (hN.returnCorrectionLocalCoefficient_parameterSpatialTower
    (D := D) (T := T) (S := S) (C := C) (R := R) (base := base) (loss := loss) (ε := ε)
    hS hT hR χ hχ hχrange m j hcell l h hl hh hdisc).congrOn
      (F := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) (G := ℝ × ℝ)
      (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ)) (by
        intro x hx
        exact (congrArg (fun L : CircleSpace S →ₗ[ℝ] (ℝ × ℝ) => L x.1.2)
          (returnCorrectionCoefficientError_eq_local hN.2.2.2.1.2.2.1 R χ
            (liftSectorParameter S C x.1.1) m x.2
            ⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩)).symm)

end ContinuousFlexibility.Statements
