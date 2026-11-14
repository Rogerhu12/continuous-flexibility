module

public import ContinuousFlexibility.Analysis.N07aAngularCandidateKernel
public import ContinuousFlexibility.Analysis.N07aScalarSolution

/-!
# Uniqueness among all actual normalized height-pair solutions

Both candidates are arbitrary elements of the original physical height
space. Their difference satisfies the genuine homogeneous scalar equation.
The preceding result constructs its fixed-domain representative before
using N06 injectivity; no membership or boundary certificate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B} {ε : ℝ}

theorem n07a_scalarSolution_unique
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hborder : RadialTrueBorder D)
    (hrad : CanonicalGeometry.ReferenceRadial S C K)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : S.Source} {u v : HeightPair S × ℝ}
    (hu : N07aScalarSolution D S C L z f u)
    (hv : N07aScalarSolution D S C L z f v) : u = v := by
  have hneg := n07aScalarSolution_smul hS hT h01 h02 h03 hz hs hv (-1)
  have hsum := n07aScalarSolution_add hS hT h01 h02 h03 hz hs hu hneg
  have hzero : N07aScalarSolution D S C L z 0 (u - v) := by
    simpa only [neg_one_smul, ← sub_eq_add_neg, sub_self] using hsum
  let ζ := n07aSectorParameterOfState h01.2.2.1 z hs
  have hζ : ζ ∈ sectorNeighborhood S base ε ε :=
    n07aSectorParameterOfState_mem h01.2.2.1 hz hs
  have hζeq : liftSectorParameter S C ζ = z :=
    lift_n07aSectorParameterOfState h01.2.2.1 z hs
  have heq : ∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients (liftSectorParameter S C ζ))
        (heightPairField S (u - v).1) p +
        (u - v).2 * nuColumnField D S C (liftSectorParameter S C ζ) p = 0 := by
    intro p hp
    simpa only [hζeq, Submodule.coe_zero, map_zero, Pi.zero_apply] using hzero.2 p hp
  have hkernel := n07a_heightPair_homogeneous_eq_zero
    hD hT hS h01 h02 h03 h04 hborder hrad href hcur hRatio hcanonical h05 h06
      ζ hζ (u - v).1 (u - v).2 hzero.1 heq
  exact sub_eq_zero.mp hkernel

end ContinuousFlexibility.Analysis
