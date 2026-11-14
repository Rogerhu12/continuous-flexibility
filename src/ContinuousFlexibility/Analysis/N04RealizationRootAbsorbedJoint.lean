import ContinuousFlexibility.Analysis.N04RealizationPolarInputJoint
import ContinuousFlexibility.Analysis.N06RootAbsorbedPacket
import ContinuousFlexibility.Analysis.N01cCoefficientJetCalculus

/-!
# The actual absorbed root packet has genuine joint parameter jets

This is the existing six-coordinate packet. The four state-dependent
entries are the original polar height inputs multiplied by the scalar
parameter, with the fixed reciprocal reference profile where prescribed.
The same physical and state domain is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem actualRootAbsorbedCoordinates_polar
    (D : ReferenceData) (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    n06ActualRootAbsorbedCoordinates D S z p =
      ![D.w p.1, (D.w p.1)⁻¹ * (z.2 * stateUPolarInput S 0 z.1 p),
        z.2 * stateUPolarInput S 1 z.1 p,
        (D.w p.1)⁻¹ * (z.2 * stateUPolarInput S 3 z.1 p),
        (D.w p.1)⁻¹ * (z.2 * stateUPolarInput S 4 z.1 p), 1] := by
  rw [n06_actualRootAbsorbedCoordinates_eq_packet]
  funext i
  fin_cases i
  · rfl
  · change z.2 * ((D.w p.1)⁻¹ * radialPartial (stateU S z.1) p) =
      (D.w p.1)⁻¹ * (z.2 * radialPartial (stateU S z.1) p)
    ring
  · rfl
  · change z.2 * ((D.w p.1)⁻¹ * radialPartial (heightAngular (stateU S z.1)) p) =
      (D.w p.1)⁻¹ * (z.2 * radialPartial (heightAngular (stateU S z.1)) p)
    ring
  · change z.2 * ((D.w p.1)⁻¹ * angularPartial (heightAngular (stateU S z.1)) p) =
      (D.w p.1)⁻¹ * (z.2 * angularPartial (heightAngular (stateU S z.1)) p)
    ring
  · rfl

/-- The genuine tower of the existing absorbed packet on the original
state neighborhood and the full open annulus. -/
def n04Realization_rootAbsorbedCoordinates_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1) :
    SmoothDirections (stateNeighborhood S C base ε ×ˢ annularOpen D)
      (fun z : (AnnularState S × ℝ) × PolarPoint =>
        n06ActualRootAbsorbedCoordinates D S z.1 z.2) := by
  let U : Set ((AnnularState S × ℝ) × PolarPoint) :=
    stateNeighborhood S C base ε ×ˢ annularOpen D
  have hU : IsOpen U :=
    (isOpen_stateNeighborhood S C base ε).prod (isOpen_Ioo.prod isOpen_univ)
  have hΩ : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hw : ContDiffOn ℝ ∞ (fun p : PolarPoint => D.w p.1) (annularOpen D) :=
    (hD.choose_spec.1.2.2.1.1.comp contDiff_fst).contDiffOn
  have hwinv : ContDiffOn ℝ ∞ (fun p : PolarPoint => (D.w p.1)⁻¹) (annularOpen D) :=
    hw.inv (fun p hp => (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1).ne')
  let π : ((AnnularState S × ℝ) × PolarPoint) →L[ℝ] PolarPoint :=
    ContinuousLinearMap.snd ℝ (AnnularState S × ℝ) PolarPoint
  let Jw : SmoothDirections U (fun z => D.w z.2.1) :=
    ((smoothDirectionsOfContDiffOn hΩ hw).compAffine π 0 hU
      (fun z hz => by simpa only [zero_add, π, ContinuousLinearMap.coe_snd'] using hz.2)).congr
        (fun z _ => by simp only [zero_add, π, ContinuousLinearMap.coe_snd'])
  let Ji : SmoothDirections U (fun z => (D.w z.2.1)⁻¹) :=
    ((smoothDirectionsOfContDiffOn hΩ hwinv).compAffine π 0 hU
      (fun z hz => by simpa only [zero_add, π, ContinuousLinearMap.coe_snd'] using hz.2)).congr
        (fun z _ => by simp only [zero_add, π, ContinuousLinearMap.coe_snd'])
  let JP (i : Fin 5) : SmoothDirections U
      (fun z => z.1.2 * stateUPolarInput S i z.1.1 z.2) :=
    n04Realization_polarInputJointDirections hT hS hD.choose_spec.1.1 hε i
  let F : Fin 6 → ((AnnularState S × ℝ) × PolarPoint) → ℝ :=
    ![fun z => D.w z.2.1,
      fun z => (D.w z.2.1)⁻¹ * (z.1.2 * stateUPolarInput S 0 z.1.1 z.2),
      fun z => z.1.2 * stateUPolarInput S 1 z.1.1 z.2,
      fun z => (D.w z.2.1)⁻¹ * (z.1.2 * stateUPolarInput S 3 z.1.1 z.2),
      fun z => (D.w z.2.1)⁻¹ * (z.1.2 * stateUPolarInput S 4 z.1.1 z.2),
      fun _ => 1]
  let JF : ∀ i : Fin 6, SmoothDirections U (F i) :=
    Fin.cases Jw (Fin.cases (smoothDirections_realMul Ji (JP 0)) (Fin.cases (JP 1)
      (Fin.cases (smoothDirections_realMul Ji (JP 3))
        (Fin.cases (smoothDirections_realMul Ji (JP 4))
          (Fin.cases (smoothDirections_constant hU (1 : ℝ)) (fun i => i.elim0))))))
  apply (smoothDirections_scalarTuple hU JF).congr
  intro z hz
  rw [actualRootAbsorbedCoordinates_polar]
  funext i
  fin_cases i <;> rfl

end ContinuousFlexibility.Analysis
