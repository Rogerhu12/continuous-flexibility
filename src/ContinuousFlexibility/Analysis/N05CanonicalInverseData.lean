module

public import ContinuousFlexibility.Analysis.N05CanonicalInverseLinearity
public import ContinuousFlexibility.Analysis.N05ReferenceInterface

/-!
# The actual canonical reference inverse data

The physical inverse supplies its own three-point exponent window. Its
weaker endpoint, its original material orders, and material loss four define
one canonical inverse, including the continuous restriction at angular order
two. No endpoint or Sobolev order changes the underlying map or its scalars.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
  {ρ M0 M1 : ℝ} (hρ : 0 < ρ) (hρbound : ρ < (1 / 4 : ℝ))
  {G : RadialSource → RadialUnknown}
  (hGminus : ReferenceInverseProperties D ((3 / 4 : ℝ) - ρ) M0 M1 G)

/-- The same actual map and the prescribed continuous base restriction. -/
def n05CanonicalReferenceInverseData : N05ReferenceInverseData S K V where
  weakExponent := (3 / 4 : ℝ) - ρ
  sourceMaterial := M0
  outputMaterial := M1
  lossMaterial := 4
  physicalInverse := G
  baseInverse := n05CanonicalBaseInverse hD hT hS h hcoordinates
    (by linarith only [hρbound]) hGminus hV (sub_lt_self _ hρ)
  globalInverse := n05CanonicalGlobalInverse D S C K G

@[simp] theorem n05CanonicalReferenceInverseData_base_apply
    (v : V.level (3 / 4 : ℝ) 0 2) :
    (n05CanonicalReferenceInverseData hD hT hS h hcoordinates hV hρ hρbound hGminus).baseInverse v =
      n05CanonicalGlobalInverse D S C K G
        (V.forget (3 / 4 : ℝ) 0 2 v) := by
  exact n05CanonicalBaseInverse_apply hD hT hS h hcoordinates
    (by linarith only [hρbound]) hGminus hV (sub_lt_self _ hρ) v

@[simp] theorem n05CanonicalReferenceInverseData_global_apply
    (F : CanonicalSequence S K) :
    (n05CanonicalReferenceInverseData hD hT hS h hcoordinates hV hρ hρbound hGminus).globalInverse F =
      n05CanonicalGlobalInverse D S C K G F := rfl

end ContinuousFlexibility.Statements
