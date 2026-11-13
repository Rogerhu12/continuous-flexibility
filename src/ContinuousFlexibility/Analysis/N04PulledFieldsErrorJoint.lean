import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientRegularity
import ContinuousFlexibility.Analysis.SmoothDirectionsGluing

/-!
# The actual correction error has a joint tower on the whole annulus

The fixed cutoff strips and the interior of their common zero region cover
the physical annulus. On each strip the retained independent-residual
coefficient tower is genuine. On the zero region the literal error vanishes
for every state and residual. Uniqueness glues these towers before the
actual N02 residual is substituted into the state graph.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

local instance n04PulledFieldsErrorJointStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (Q : N04bOpticalCutoffData D S C base ε)
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)

/-- The independent-residual error is jointly smooth on the original
state neighborhood and the entire open physical annulus. -/
def n04PulledFields_opticalErrorJointDirections (π : (ℝ × ℝ) →L[ℝ] ℝ) :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ annularOpen D)
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        π (returnCorrectionCoefficientError D S C R Q.cutoff
          (liftSectorParameter S C x.1.1) x.2 x.1.2)) := by
  classical
  let U : Set ((StateDirections S × ℝ) × CircleSpace S) :=
    sectorNeighborhood S base ε ε ×ˢ univ
  let Z : Set PolarPoint := {q | ∀ m, deriv (Q.cutoff m) q.1 = 0}
  let V : Option ℕ → Set (((StateDirections S × ℝ) × CircleSpace S) × PolarPoint)
    | none => U ×ˢ (annularOpen D ∩ interior Z)
    | some m => U ×ˢ
        (annularOpen D ∩ (Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ univ))
  have hU : IsOpen U := (sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ
  have hΩ : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hV (i : Option ℕ) : IsOpen (V i) := by
    cases i with
    | none => exact hU.prod (hΩ.inter isOpen_interior)
    | some m => exact hU.prod (hΩ.inter (isOpen_Ioo.prod isOpen_univ))
  have hsub (i : Option ℕ) : V i ⊆ U ×ˢ annularOpen D := by
    cases i <;> exact fun _ hx => ⟨hx.1, hx.2.1⟩
  have hcover : ∀ x ∈ U ×ˢ annularOpen D, ∃ i, x ∈ V i := by
    intro x hx
    rcases hN.cutoffStrip_or_eventually_zero Q.cutoff Q.support_interior
      Q.endpoint_germs Q.stripLeft Q.stripRight Q.strip_support hx.2.1 with
      ⟨m, hm⟩ | hz
    · exact ⟨some m, hx.1, hx.2, hm, mem_univ _⟩
    · have hnear : Z ∈ 𝓝 x.2 := (continuous_fst.tendsto x.2).eventually hz
      exact ⟨none, hx.1, hx.2, mem_interior_iff_mem_nhds.mpr hnear⟩
  let J : ∀ i, SmoothDirections (V i)
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        π (returnCorrectionCoefficientError D S C R Q.cutoff
          (liftSectorParameter S C x.1.1) x.2 x.1.2)) := by
    intro i
    cases i with
    | none =>
        apply (smoothDirections_constant (hV none) (0 : ℝ)).congrOn
        intro x hx
        have hz : ∀ m, deriv (Q.cutoff m) x.2.1 = 0 := interior_subset hx.2.2
        have hinactive : ¬ ∃ m,
            x.2.1 ∈ Ioo (C.left m) (C.right m) ∧
              deriv (Q.cutoff m) x.2.1 ≠ 0 := by
          rintro ⟨m, _, hm⟩
          exact hm (hz m)
        simp only [returnCorrectionCoefficientError, dif_neg hinactive,
          LinearMap.zero_apply, map_zero]
    | some m =>
        let K := solveSmoothDirectionsPostcomp
          (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR
            Q.cutoff Q.cutoff_smooth Q.range_on_component m (Q.cell m) (Q.component_cell m)
            (Q.stripLeft m) (Q.stripRight m) (Q.stripLeft_gt m) (Q.stripRight_lt m)
            (fun z hz q hq => Q.strip_discriminant hN hS hT z hz m q hq)) π
        exact K.restrict (hV (some m)) (fun _ hx => ⟨hx.1, hx.2.2⟩)
  exact (exists_smoothDirections_of_open_cover (hU.prod hΩ) V J hsub hcover).choose

/-- Substitute the genuine N02 residual into the joint tower. The
physical annulus and the state neighborhood both remain unchanged. -/
def n04PulledFields_actualErrorJointDirections (π : (ℝ × ℝ) →L[ℝ] ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ annularOpen D)
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        π (returnCorrectionCoefficientError D S C R Q.cutoff
          (liftSectorParameter S C x.1) x.2
            (R.residual (liftSectorParameter S C x.1)))) := by
  let H := S.circle (3 / 4 : ℝ)
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × CircleSpace S) :=
    (withSeminorms_pairGrading (sectorPairGrading_withSeminorms S)
      (withSeminorms_graded (fun n => H.level n) H.bond)).toLocallyConvexSpace
  have hU : IsOpen (sectorNeighborhood S base ε ε) :=
    sectorNeighborhood_isOpen S base ε ε
  have hΩ : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hres : SmoothTameOn (pairGrading (sectorGrading S) realGrading) H.grading
      (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) :=
    hR.2.2.2.2.2.2.2.2.2.2
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z : StateDirections S × ℝ => (z, R.residual (liftSectorParameter S C z))) :=
    smoothDirectionsProd
      (smoothDirectionsLinearOn (ContinuousLinearMap.id ℝ (StateDirections S × ℝ)) hU)
      hres.choose
  let Jstate := J.compLinear
    (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) PolarPoint)
    (hU.prod hΩ) (fun _ hx => hx.1)
  let Jpoint := smoothDirectionsLinearOn
    (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) PolarPoint) (hU.prod hΩ)
  exact smoothDirections_realCompTVS (smoothDirectionsProd Jstate Jpoint)
    (n04PulledFields_opticalErrorJointDirections Q hN hS hT hR π)
    (fun _ hx => ⟨⟨hx.1, mem_univ _⟩, hx.2⟩)

end ContinuousFlexibility.Analysis
