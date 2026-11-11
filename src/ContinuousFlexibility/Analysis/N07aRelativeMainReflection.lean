import ContinuousFlexibility.Analysis.N07aRelativeMainIdentity
import ContinuousFlexibility.Analysis.N07aScalarColumnSupport
import ContinuousFlexibility.Analysis.N07aCanonicalJetRealization
import ContinuousFlexibility.Analysis.N07aReferenceReturn

/-! Reflection of the genuine relative source and its finite-rank part. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}

theorem n07aRelativeScalarPart_reflection
    (hS : IsPhysicalSpaces D T S) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (U : CanonicalUnknown S K) :
    n07aAngularReflection m (n07aRelativeScalarPart href hcur z hz m hm U) =
      n07aRelativeScalarPart href hcur z hz m hm U := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl
  have hs := h01.2.2.1.liftSectorParameter_sector z
  have hfix (i : Fin 3) :
      n07aAngularReflection m ((n07aCurrentScalarOpenCoefficient href hcur z hz m hm i).sub
        (n07aReferenceScalarOpenCoefficient href m hm i)).toLp =
      ((n07aCurrentScalarOpenCoefficient href hcur z hz m hm i).sub
        (n07aReferenceScalarOpenCoefficient href m hm i)).toLp := by
    apply N07aCanonicalOpenCoefficient.toLp_even
    intro p hp
    exact congrArg₂ (fun a b : ℝ => a - b)
      (n07a_canonicalScalarColumn_even hS h03 h04 _ hz' hs m i p hp)
      (n07a_canonicalScalarColumn_even hS h03 h04 _
        (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m i p hp)
  simp only [n07aRelativeScalarPart, map_add, map_smul, hfix]

theorem n07aRelativeMainSource_reflection
    (hS : IsPhysicalSpaces D T S) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hV : IsVolumeModel T S K V)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.left m < K.right m) :
    n07aAngularReflection m (n07aRelativeMainSource (P := P) href hcur z hz F m hm) =
      n07aRelativeMainSource (P := P) href hcur z hz F m hm := by
  rw [n07aRelativeMainSource, map_sub, n07a_volume_forget_reflection hV,
    n07aRelativeScalarPart_reflection hS h01 h03 h04]

end ContinuousFlexibility.Analysis
