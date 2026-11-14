module

public import ContinuousFlexibility.Analysis.N07aVolumeLinearLift
public import ContinuousFlexibility.Analysis.N07aAngularMaterialEmbedding
public import ContinuousFlexibility.Analysis.N07aAngularCanonicalProjection

/-!
# The genuine material inclusion as a bounded linear map

This packages the already constructed contractive inclusion without
changing its representative.  It intertwines the actual angular bands,
as required to identify a Schur lift with the original base operator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

local instance n07aMaterialEmbeddingLinearLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aMaterialEmbeddingLinearLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

def n07aAngularMaterialToBaseLinear
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t)
    {b s : ℕ} (hbs : b ≤ s) : V.level γ t s →L[ℝ] V.level γ 0 b :=
  n07aVolumeBoundedLift hV γ 0 b (V.forget γ t s) 1 (fun F =>
    ⟨n07aAngularMaterialToBase hD hT hV ht hbs F,
      n07aAngularMaterialToBase_forget hD hT hV ht hbs F,
      by simpa only [one_mul] using n07aAngularMaterialToBase_norm_le hD hT hV ht hbs F⟩)

theorem n07aAngularMaterialToBaseLinear_forget
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t)
    {b s : ℕ} (hbs : b ≤ s) (F : V.level γ t s) :
    V.forget γ 0 b (n07aAngularMaterialToBaseLinear hD hT hV ht hbs F) = V.forget γ t s F :=
  n07aVolumeBoundedLift_forget hV γ 0 b (V.forget γ t s) 1 _ F

theorem n07aAngularMaterialToBaseLinear_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t)
    {b s : ℕ} (hbs : b ≤ s) (F : V.level γ t s) :
    n07aAngularMaterialToBaseLinear hD hT hV ht hbs F =
      n07aAngularMaterialToBase hD hT hV ht hbs F := by
  apply hV.2.2.1 γ 0 b
  rw [n07aAngularMaterialToBaseLinear_forget, n07aAngularMaterialToBase_forget]

theorem n07aAngularMaterialToBaseLinear_norm_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t)
    {b s : ℕ} (hbs : b ≤ s) :
    ‖n07aAngularMaterialToBaseLinear hD hT hV (γ := γ) ht hbs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro F
  rw [one_mul, n07aAngularMaterialToBaseLinear_apply]
  exact n07aAngularMaterialToBase_norm_le hD hT hV ht hbs F

theorem n07aAngularMaterialToBaseLinear_band
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t)
    {b s : ℕ} (hbs : b ≤ s) (hI : ∀ m, K.left m < K.right m)
    (n : ℕ) (F : V.level γ t s) :
    n07aAngularLevelBand hV γ 0 hI b n (n07aAngularMaterialToBaseLinear hD hT hV ht hbs F) =
      n07aAngularMaterialToBaseLinear hD hT hV ht hbs (n07aAngularLevelBand hV γ t hI s n F) := by
  apply hV.2.2.1 γ 0 b
  rw [n07aAngularLevelBand_forget, n07aAngularMaterialToBaseLinear_forget,
    n07aAngularMaterialToBaseLinear_forget, n07aAngularLevelBand_forget]

end ContinuousFlexibility.Analysis
