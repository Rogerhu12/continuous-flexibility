module

public import ContinuousFlexibility.Analysis.N06PrimitiveReferenceDistribution
public import ContinuousFlexibility.Analysis.N07aReferenceSecondNormal
public import ContinuousFlexibility.Analysis.N07aCanonicalModeEnergySum

/-!
# Positive graph energy of the same N05 inverse on its original intervals

The first normal derivative is supplied by N05.  The actual reference
equation and the reciprocal leading coefficient recover the second normal
derivative in the original canonical L2 space.  These are the fields used
by the principal mode estimate on the original intervals.  There is no
N06 premise and no replacement of K, V, b or B.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency false

/-- Five genuine weak derivatives of one given canonical L2 field. -/
structure N06PrimitivePositiveJets {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} (u : CanonicalL2 S K m) where
  radial : CanonicalL2 S K m
  angular : CanonicalL2 S K m
  radialAngular : CanonicalL2 S K m
  angularAngular : CanonicalL2 S K m
  secondRadial : CanonicalL2 S K m
  radial_weak : N07aWeakCanonicalMixedDerivative S K m u radial 1 0
  angular_weak : N07aWeakCanonicalMixedDerivative S K m u angular 0 1
  radialAngular_weak : N07aWeakCanonicalMixedDerivative S K m radial radialAngular 0 1
  angularAngular_weak : N07aWeakCanonicalMixedDerivative S K m angular angularAngular 0 1
  secondRadial_weak : N07aWeakCanonicalMixedDerivative S K m radial secondRadial 1 0
  secondRadial_weak_two : N07aWeakCanonicalMixedDerivative S K m u secondRadial 2 0

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

local instance n06PrimitivePositiveLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06PrimitivePositiveLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _
local instance n06PrimitivePositiveUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n06PrimitivePositiveUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n06PrimitivePositiveGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06PrimitivePositiveGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

/-- The source projection of the same N05 inverse gives the actual
distribution equation, before any relative source is constructed. -/
theorem n06_primitiveReferenceInverse_positive_distribution
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (hJ : ReferenceJets D T S C L K)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.positive m = true) :
    N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m)
      (n07aReferenceInverseField (B := B) F m)
      (n07aReferenceCanonicalRhs hJ m (h04.1.referenceBounds m).2.1
        (B.inverse F).val.1 (V.forget (3 / 4 : ℝ) 0 b F)) := by
  have hsource : (B.inverse F).val.2 = F := h05.2.2.2.2.2.2.2.1 F
  simpa only [hsource, n07aReferenceInverseField] using
    n06_primitiveReference_positive_distribution hS h01 h03 h04 h05 hJ (B.inverse F) m hm

/-- The actual N05 first-normal and angular estimates, followed by the
actual reference equation, construct all five fields of the divergence. -/
theorem n06_primitiveReferenceInverse_positiveJets_nonempty
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.positive m = true) :
    Nonempty (N06PrimitivePositiveJets (n07aReferenceInverseField (B := B) F m)) := by
  obtain ⟨ur, uθ, urθ, uθθ, hr, hθ, hrθ, hθθ⟩ := n07a_referenceInverse_finiteJets h05 F m
  have heq := n06_primitiveReferenceInverse_positive_distribution hS h01 h03 h04 h05 hJ F m hm
  obtain ⟨urr, hrr, hrr₂⟩ := n07a_reference_secondNormal_of_fourJets hJ hP
    (h04.1.referenceBounds m).2.1 hr hθ hrθ hθθ heq
  exact ⟨⟨ur, uθ, urθ, uθθ, urr, hr, hθ, hrθ, hθθ, hrr, hrr₂⟩⟩

end ContinuousFlexibility.Analysis
