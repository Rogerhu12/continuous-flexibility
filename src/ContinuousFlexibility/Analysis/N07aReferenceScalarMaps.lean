import ContinuousFlexibility.Analysis.N07aAngularReferenceInverse

/-!
# The three actual scalar functionals of the reference inverse

They are bounded projections of the prescribed inverse, with frequencies
zero, one and zero.  Their band support follows from the proved physical
reference graph projection, including the original border column.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n07aUnknownScalar {S : PhysicalSpacesData} {K : CanonicalData S}
    (U : CanonicalUnknown S K) (i : Fin 3) : ℝ := ![U.2.1, U.2.2.1, U.2.2.2] i

def n07aScalarFrequency (i : Fin 3) : ℕ := ![0, 1, 0] i

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} (B : CanonicalDomainData S K V b)

local instance n07aReferenceScalarMapsLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n07aReferenceScalarMapsLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _
local instance n07aReferenceScalarMapsUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aReferenceScalarMapsUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n07aReferenceScalarMapsGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aReferenceScalarMapsGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

def n07aUnknownScalarMap (i : Fin 3) : CanonicalUnknown S K →L[ℝ] ℝ :=
  let s := ContinuousLinearMap.snd ℝ (CanonicalL2Sequence S K) (ℝ × ℝ × ℝ)
  ![(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp s,
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).comp s,
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).comp s] i

theorem n07aUnknownScalarMap_apply (i : Fin 3) (U : CanonicalUnknown S K) :
    n07aUnknownScalarMap i U = n07aUnknownScalar U i := by
  fin_cases i <;>
    simp only [n07aUnknownScalarMap, n07aUnknownScalar, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.fst_apply, ContinuousLinearMap.snd_apply]

theorem n07aUnknownScalar_abs_le_norm (U : CanonicalUnknown S K) (i : Fin 3) :
    |n07aUnknownScalar U i| ≤ ‖U‖ := by
  fin_cases i
  · exact (norm_fst_le U.2).trans (norm_snd_le U)
  · exact ((norm_fst_le U.2.2).trans (norm_snd_le U.2)).trans (norm_snd_le U)
  · exact ((norm_snd_le U.2.2).trans (norm_snd_le U.2)).trans (norm_snd_le U)

def n07aReferenceScalarMap (i : Fin 3) : V.level (3 / 4 : ℝ) 0 b →L[ℝ] ℝ :=
  (n07aUnknownScalarMap i).comp
    (((ContinuousLinearMap.fst ℝ (CanonicalUnknown S K) (V.level (3 / 4 : ℝ) 0 b)).comp
      B.graph.subtypeL).comp B.inverse)

theorem n07aReferenceScalarMap_apply (i : Fin 3) (F : V.level (3 / 4 : ℝ) 0 b) :
    n07aReferenceScalarMap B i F = n07aUnknownScalar (B.inverse F).val.1 i := by
  rw [n07aReferenceScalarMap, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, ContinuousLinearMap.fst_apply, n07aUnknownScalarMap_apply]

theorem n07aReferenceScalarMap_norm_le (i : Fin 3) :
    ‖n07aReferenceScalarMap B i‖ ≤ ‖B.inverse‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  rw [n07aReferenceScalarMap_apply, Real.norm_eq_abs]
  exact (n07aUnknownScalar_abs_le_norm (B.inverse F).val.1 i).trans
    ((norm_fst_le (B.inverse F).val).trans (B.inverse.le_opNorm F))

theorem n07aReferenceScalarMap_band
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (h05 : N05Properties D T S C K V b B) (hI : ∀ m, K.left m < K.right m)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hmap : ∀ m, MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (physicalPieceOpen S K m))
    (hsm : ∀ m, ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m) (physicalPieceOpen S K m))
    (i : Fin 3) (j : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) :
    n07aReferenceScalarMap B i (n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j F) =
      if n07aScalarFrequency i = j then n07aReferenceScalarMap B i F else 0 := by
  rw [n07aReferenceScalarMap_apply,
    n07a_referenceInverse_angularBand hD hborder h05 hI hR hAux hmap hsm F j,
    n07aReferenceScalarMap_apply]
  fin_cases i <;>
    simp only [n07aUnknownScalar, n07aScalarFrequency, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      n07aAngularUnknownBand_left, n07aAngularUnknownBand_border, n07aAngularUnknownBand_auxiliary]

end ContinuousFlexibility.Analysis
