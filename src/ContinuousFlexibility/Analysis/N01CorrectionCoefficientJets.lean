import ContinuousFlexibility.Analysis.N01CorrectionCoefficientPointTower
import ContinuousFlexibility.Analysis.SmoothDirectionsScalarLine

/-!
# Actual multilinear coefficient fields for the return correction

These are the actual continuous directional derivatives at every
spatial point, assembled by the function-space multilinear map. Their
zeroth field is the existing coefficient error, and their parameter
line derivatives, parity and periodicity follow from the constructed
genuine towers. Spatial mixed-jet estimates can therefore concern this
single family rather than a separate formal representation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

local instance n01CorrectionCoefficientJetsParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ ((StateDirections S × ℝ) × CircleSpace S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis

private theorem coefficientScalarJets_pair_hasDerivAt
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → ℝ × ℝ} (J : SmoothDirections U f)
    (A : ∀ n : ℕ, E → (Fin n → E) → ℝ × ℝ)
    (hA : ∀ n y v, A n y v = J.D n y v)
    (n : ℕ) (x w : E) (v : Fin n → E) (t : ℝ) (ht : x + t • w ∈ U) :
    HasDerivAt (fun s => (A n (x + s • w) v).1)
      (A (n + 1) (x + t • w) (Fin.cons w v)).1 t ∧
    HasDerivAt (fun s => (A n (x + s • w) v).2)
      (A (n + 1) (x + t • w) (Fin.cons w v)).2 t := by
  have hfst : HasDerivAt (fun s => (J.D n (x + s • w) v).1)
      (J.D (n + 1) (x + t • w) (Fin.cons w v)).1 t := by
    simpa only [solveSmoothDirectionsPostcomp,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.coe_fst'] using
      (solveSmoothDirectionsPostcomp J (ContinuousLinearMap.fst ℝ ℝ ℝ)).hasDerivAt_line_jet
        x w n v ht
  have hsnd : HasDerivAt (fun s => (J.D n (x + s • w) v).2)
      (J.D (n + 1) (x + t • w) (Fin.cons w v)).2 t := by
    simpa only [solveSmoothDirectionsPostcomp,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.coe_snd'] using
      (solveSmoothDirectionsPostcomp J (ContinuousLinearMap.snd ℝ ℝ ℝ)).hasDerivAt_line_jet
        x w n v ht
  constructor
  · exact (hfst.congr_deriv
      (congrArg (fun q : ℝ × ℝ => q.1) (hA (n + 1) (x + t • w) (Fin.cons w v))).symm)
      .congr_of_eventuallyEq (Filter.Eventually.of_forall fun s =>
        congrArg (fun q : ℝ × ℝ => q.1) (hA n (x + s • w) v))
  · exact (hsnd.congr_deriv
      (congrArg (fun q : ℝ × ℝ => q.2) (hA (n + 1) (x + t • w) (Fin.cons w v))).symm)
      .congr_of_eventuallyEq (Filter.Eventually.of_forall fun s =>
        congrArg (fun q : ℝ × ℝ => q.2) (hA n (x + s • w) v))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
  (hdisc : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m p, p.1 ∈ Ioo (C.left m) (C.right m) → deriv (χ m) p.1 ≠ 0 →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

def N01Properties.returnCorrectionCoefficientScalarJets
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S) :
    MultilinearMap ℝ (fun _ : Fin n => (StateDirections S × ℝ) × CircleSpace S)
      (PolarPoint → ℝ × ℝ) :=
  MultilinearMap.pi (fun p =>
    ((hN.returnCorrectionCoefficient_pointTower hS hT hR j hcell χ hχrange hcutoff hdisc p).D
      n x).toMultilinearMap)

theorem N01Properties.returnCorrectionCoefficientScalarJets_apply
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) (p : PolarPoint) :
    hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc n x v p =
      (hN.returnCorrectionCoefficient_pointTower hS hT hR j hcell χ hχrange hcutoff hdisc p).D
        n x v := rfl

theorem N01Properties.returnCorrectionCoefficientScalarJets_zero
    (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
        0 x Fin.elim0 =
      fun p => returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1) p x.2 := by
  funext p
  exact (hN.returnCorrectionCoefficient_pointTower hS hT hR j hcell χ hχrange hcutoff
    hdisc p).zero x hx

theorem N01Properties.returnCorrectionCoefficientScalarJets_hasDerivAt
    (n : ℕ) (x w : (StateDirections S × ℝ) × CircleSpace S)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S)
    (t : ℝ) (ht : x + t • w ∈ sectorNeighborhood S base ε ε ×ˢ univ) (p : PolarPoint) :
    HasDerivAt (fun s => (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ
      hχrange hcutoff hdisc n (x + s • w) v p).1)
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
        (n + 1) (x + t • w) (Fin.cons w v) p).1 t ∧
    HasDerivAt (fun s => (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ
      hχrange hcutoff hdisc n (x + s • w) v p).2)
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
        (n + 1) (x + t • w) (Fin.cons w v) p).2 t := by
  let J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C y.1) p y.2) :=
    hN.returnCorrectionCoefficient_pointTower hS hT hR j hcell χ hχrange hcutoff hdisc p
  exact coefficientScalarJets_pair_hasDerivAt J
    (fun k y vs => hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ
      hχrange hcutoff hdisc k y vs p)
    (fun k y vs => hN.returnCorrectionCoefficientScalarJets_apply hS hT hR j hcell χ
      hχrange hcutoff hdisc k y vs p)
    n x w v t ht

theorem N01Properties.returnCorrectionCoefficientScalarJets_reflection
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) (r θ : ℝ) :
    hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
        n x v (r, -θ) =
      (-(hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          n x v (r, θ)).1,
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          n x v (r, θ)).2) := by
  let J : ∀ p : PolarPoint, SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C y.1) p y.2) :=
    hN.returnCorrectionCoefficient_pointTower hS hT hR j hcell χ hχrange hcutoff hdisc
  have href : (J (r, -θ)).D n x v =
      (-((J (r, θ)).D n x v).1, ((J (r, θ)).D n x v).2) :=
    returnCorrectionCoefficientError_jets_reflection hS R χ
      (fun y => liftSectorParameter S C y.1) (fun y => y.2) J n x hx v r θ
  have hneg : hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ
      hχrange hcutoff hdisc n x v (r, -θ) = (J (r, -θ)).D n x v :=
    hN.returnCorrectionCoefficientScalarJets_apply hS hT hR j hcell χ
      hχrange hcutoff hdisc n x v (r, -θ)
  have hbase : hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ
      hχrange hcutoff hdisc n x v (r, θ) = (J (r, θ)).D n x v :=
    hN.returnCorrectionCoefficientScalarJets_apply hS hT hR j hcell χ
      hχrange hcutoff hdisc n x v (r, θ)
  exact hneg.trans (href.trans
    (congrArg (fun q : ℝ × ℝ => (-q.1, q.2)) hbase).symm)

theorem N01Properties.returnCorrectionCoefficientScalarJets_periodic
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) (r θ : ℝ) :
    hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
        n x v (r, θ + Real.pi) =
      hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
        n x v (r, θ) := by
  let J : ∀ p : PolarPoint, SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C y.1) p y.2) :=
    hN.returnCorrectionCoefficient_pointTower hS hT hR j hcell χ hχrange hcutoff hdisc
  have hperiodic : (J (r, θ + Real.pi)).D n x v = (J (r, θ)).D n x v :=
    hN.returnCorrectionCoefficientError_jets_periodic hS R χ hχrange
      (fun y => liftSectorParameter S C y.1) (fun y => y.2)
      (fun y hy => liftSectorParameter_mem_stateNeighborhood hy.1 le_rfl)
      (fun y hy => hN.2.2.1.liftSectorParameter_sector y.1) J n x hx v r θ
  have hleft : hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ
      hχrange hcutoff hdisc n x v (r, θ + Real.pi) = (J (r, θ + Real.pi)).D n x v :=
    hN.returnCorrectionCoefficientScalarJets_apply hS hT hR j hcell χ
      hχrange hcutoff hdisc n x v (r, θ + Real.pi)
  have hright : hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ
      hχrange hcutoff hdisc n x v (r, θ) = (J (r, θ)).D n x v :=
    hN.returnCorrectionCoefficientScalarJets_apply hS hT hR j hcell χ
      hχrange hcutoff hdisc n x v (r, θ)
  exact hleft.trans (hperiodic.trans hright.symm)

end ContinuousFlexibility.Statements
