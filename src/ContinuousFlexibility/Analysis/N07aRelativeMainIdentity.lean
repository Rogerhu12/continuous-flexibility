import ContinuousFlexibility.Analysis.N07aActualPotentialBlock
import ContinuousFlexibility.Analysis.N07aRelativeNegative
import ContinuousFlexibility.Analysis.N07aRelativeExpanded

/-!
# Removing the three genuine scalar columns from the relative source

The remaining local class is exactly the principal coefficient difference
and the signed potential difference acting on the original reference
inverse. On negative pieces the principal part vanishes identically.
-/

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

local instance n07aRelativeMainIdentityLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n07aRelativeMainIdentityLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _
local instance n07aRelativeMainIdentityUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aRelativeMainIdentityUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n07aRelativeMainIdentityGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aRelativeMainIdentityGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

def n07aRelativeScalarPart
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (U : CanonicalUnknown S K) : CanonicalL2 S K m :=
  U.2.1 • ((n07aCurrentScalarOpenCoefficient href hcur z hz m hm 0).sub
      (n07aReferenceScalarOpenCoefficient href m hm 0)).toLp +
    U.2.2.1 • ((n07aCurrentScalarOpenCoefficient href hcur z hz m hm 1).sub
      (n07aReferenceScalarOpenCoefficient href m hm 1)).toLp +
    U.2.2.2 • ((n07aCurrentScalarOpenCoefficient href hcur z hz m hm 2).sub
      (n07aReferenceScalarOpenCoefficient href m hm 2)).toLp

theorem n07aRelativeCanonicalLower_eq_potential_add_scalars
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (U : CanonicalUnknown S K) :
    n07aRelativeCanonicalLower href hcur z hz m hm U =
      (n07aRelativePotentialCoefficient href hcur z hz m hm).mul (U.1 m) +
        n07aRelativeScalarPart href hcur z hz m hm U := by
  unfold n07aRelativeCanonicalLower n07aCanonicalLowerDifference
    n07aRelativePotentialCoefficient n07aRelativeScalarPart
  abel

def n07aRelativeMainSource
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.left m < K.right m) : CanonicalL2 S K m :=
  V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z) F) m -
    n07aRelativeScalarPart href hcur z hz m hm (B.inverse F).val.1

theorem n07a_relativeMain_expanded
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.left m < K.right m)
    (ur uθ urr urθ uθθ : CanonicalL2 S K m)
    (hr : N07aWeakCanonicalMixedDerivative S K m (n07aReferenceInverseField (B := B) F m) ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m (n07aReferenceInverseField (B := B) F m) uθ 0 1)
    (hrr : N07aWeakCanonicalMixedDerivative S K m ur urr 1 0)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1) :
    n07aRelativeMainSource (P := P) href hcur z hz F m hm =
      n07aRelativePrincipalJet href hcur z hz m hm ur uθ urr urθ uθθ +
        (n07aRelativePotentialCoefficient href hcur z hz m hm).mul
          (n07aReferenceInverseField (B := B) F m) := by
  rw [n07aRelativeMainSource,
    n07a_relativeCanonical_expanded hab hS hT h01 h02 h03 h04 href hcur h05 h06
      z hz F m hm ur uθ urr urθ uθθ hr hθ hrr hrθ hθθ,
    n07aRelativeCanonicalLower_eq_potential_add_scalars]
  abel

theorem n07a_relativeMain_negative
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.left m < K.right m)
    (hneg : K.positive m = false) :
    n07aRelativeMainSource (P := P) href hcur z hz F m hm =
      (n07aRelativePotentialCoefficient href hcur z hz m hm).mul
        (n07aReferenceInverseField (B := B) F m) := by
  rw [n07aRelativeMainSource,
    n07a_relativeCanonical_negative hab hS hT h01 h02 h03 h04 href hcur h05 h06 z hz F m hm hneg,
    n07aRelativeCanonicalLower_eq_potential_add_scalars, add_sub_cancel_right]

end ContinuousFlexibility.Analysis
