import ContinuousFlexibility.Analysis.N07aAngularReferenceGraph

/-!
# The actual N05 inverse preserves angular bands

The physical weak relation, the actual radial reference coordinates, and
the radial auxiliary column give a projected member of the same graph.
N05's existing section identity then forces equality with its prescribed
inverse.  The statement concerns that inverse and its genuine global
extension, rather than an independently supplied spectral operator.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory CanonicalGeometry
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b}

local instance n07aRefInverseVolumeGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _

local instance n07aRefInverseVolumeSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

local instance n07aRefInverseUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) := inferInstance

local instance n07aRefInverseUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) := inferInstance

local instance n07aRefInverseGraphGroup : NormedAddCommGroup B.Space := Submodule.normedAddCommGroup _

local instance n07aRefInverseGraphSpace : NormedSpace ℝ B.Space := Submodule.normedSpace _

theorem n07a_referenceInverse_angularBand
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (h05 : N05Properties D T S C K V b B) (hK : ∀ m, K.left m < K.right m)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hmap : ∀ m, MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (physicalPieceOpen S K m))
    (hsm : ∀ m, ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m) (physicalPieceOpen S K m))
    (F : V.level (3 / 4 : ℝ) 0 b) (n : ℕ) :
    (B.inverse (n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hK b n F)).val.1 =
      n07aAngularUnknownBand hK n (B.inverse F).val.1 := by
  have hrel : ReferenceCanonicalRelation D T S C K V B.weakExponent
      B.sourceMaterial B.outputMaterial B.lossMaterial (B.inverse F).val.1
      (V.forget (3 / 4 : ℝ) 0 b F) := by
    have h := (h05.2.2.2.2.2.2.1 (B.inverse F).val).mp (B.inverse F).property
    rw [h05.2.2.2.2.2.2.2.1 F] at h
    exact h
  let U : CanonicalUnknown S K := n07aAngularUnknownBand hK n (B.inverse F).val.1
  let Q : V.level (3 / 4 : ℝ) 0 b := n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hK b n F
  have hproj : ReferenceCanonicalRelation D T S C K V B.weakExponent
      B.sourceMaterial B.outputMaterial B.lossMaterial U (V.forget (3 / 4 : ℝ) 0 b Q) := by
    dsimp only [U, Q]
    rw [n07aAngularLevelBand_forget]
    exact n07a_referenceCanonicalRelation_band hD hborder h05.2.1 hK hR hAux hmap hsm
      h05.2.2.1 hrel n
  have hmem : (U, Q) ∈ B.graph := (h05.2.2.2.2.2.2.1 (U, Q)).mpr hproj
  exact congrArg (fun u : B.Space => u.val.1)
    (h05.2.2.2.2.2.2.2.2.1 ⟨(U, Q), hmem⟩)

/-- Coherence transfers the same band identity to the actual global inverse
used in all reference weighted estimates. -/
theorem n07a_referenceGlobalInverse_angularBand
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (h05 : N05Properties D T S C K V b B) (hK : ∀ m, K.left m < K.right m)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hmap : ∀ m, MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (physicalPieceOpen S K m))
    (hsm : ∀ m, ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m) (physicalPieceOpen S K m))
    (F : V.level (3 / 4 : ℝ) 0 b) (n : ℕ) :
    B.globalInverse (V.forget (3 / 4 : ℝ) 0 b
      (n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hK b n F)) =
      n07aAngularUnknownBand hK n (B.globalInverse (V.forget (3 / 4 : ℝ) 0 b F)) :=
  (h05.2.2.2.2.2.2.2.2.2.1 _).symm.trans
    ((n07a_referenceInverse_angularBand hD hborder h05 hK hR hAux hmap hsm F n).trans
      (congrArg (n07aAngularUnknownBand hK n) (h05.2.2.2.2.2.2.2.2.2.1 F)))

end ContinuousFlexibility.Statements
