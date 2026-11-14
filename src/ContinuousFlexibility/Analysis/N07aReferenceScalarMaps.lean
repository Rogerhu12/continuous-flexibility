module

public import ContinuousFlexibility.Analysis.N07aAngularReferenceInverse

/-!
# The three actual scalar functionals of the reference inverse

They are bounded projections of the prescribed inverse, with frequencies
zero, one and zero.  Their band support follows from the proved physical
reference graph projection, including the original border column.
-/

@[expose] public section

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
    simp only [n07aUnknownScalarMap, n07aUnknownScalar, Matrix.cons_val_zero',
      Matrix.cons_val_succ', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

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

private theorem n07a_scalar_graph_projection_apply
    {X E Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Q : Submodule ℝ (E × Y)) (g : X →L[ℝ] Q) (f : E →L[ℝ] ℝ) (x : X) :
    (f.comp (((ContinuousLinearMap.fst ℝ E Y).comp Q.subtypeL).comp g)) x =
      f (g x).val.1 := by
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.coe_fst']

theorem n07aReferenceScalarMap_apply (i : Fin 3) (F : V.level (3 / 4 : ℝ) 0 b) :
    n07aReferenceScalarMap B i F = n07aUnknownScalar (B.inverse F).val.1 i := by
  exact (n07a_scalar_graph_projection_apply B.graph B.inverse
    (n07aUnknownScalarMap i) F).trans (n07aUnknownScalarMap_apply i (B.inverse F).val.1)

theorem n07aReferenceScalarMap_norm_le (i : Fin 3) :
    ‖n07aReferenceScalarMap B i‖ ≤ ‖B.inverse‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  have he : ‖n07aReferenceScalarMap B i F‖ = |n07aUnknownScalar (B.inverse F).val.1 i| :=
    (congrArg (fun x : ℝ => ‖x‖) (n07aReferenceScalarMap_apply B i F)).trans
      (Real.norm_eq_abs _)
  have hB : ‖(B.inverse F).val‖ ≤ ‖B.inverse‖ * ‖F‖ :=
    (Submodule.norm_coe (B.inverse F)).le.trans (B.inverse.le_opNorm F)
  exact he.le.trans ((n07aUnknownScalar_abs_le_norm (B.inverse F).val.1 i).trans
    ((norm_fst_le (B.inverse F).val).trans hB))

theorem n07aUnknownScalar_angularBand
    (hI : ∀ m, K.left m < K.right m) (i : Fin 3) (j : ℕ) (U : CanonicalUnknown S K) :
    n07aUnknownScalar (n07aAngularUnknownBand hI j U) i =
      if n07aScalarFrequency i = j then n07aUnknownScalar U i else 0 := by
  fin_cases i <;>
    simp only [n07aUnknownScalar, n07aScalarFrequency, Matrix.cons_val_zero',
      Matrix.cons_val_succ', n07aAngularUnknownBand_left,
      n07aAngularUnknownBand_border, n07aAngularUnknownBand_auxiliary]

theorem n07aReferenceScalarMap_band
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (h05 : N05Properties D T S C K V b B) (hI : ∀ m, K.left m < K.right m)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hmap : ∀ m, MapsTo (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) (referencePhysicalPieceOpen S K m))
    (hsm : ∀ m, ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    (i : Fin 3) (j : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) :
    n07aReferenceScalarMap B i (n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j F) =
      if n07aScalarFrequency i = j then n07aReferenceScalarMap B i F else 0 := by
  calc
    _ = n07aUnknownScalar
        (B.inverse (n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j F)).val.1 i :=
      n07aReferenceScalarMap_apply B i _
    _ = n07aUnknownScalar (n07aAngularUnknownBand hI j (B.inverse F).val.1) i :=
      congrArg (fun U : CanonicalUnknown S K => n07aUnknownScalar U i)
        (n07a_referenceInverse_angularBand hD hborder h05 hI hR hAux hmap hsm F j)
    _ = if n07aScalarFrequency i = j then n07aUnknownScalar (B.inverse F).val.1 i else 0 :=
      n07aUnknownScalar_angularBand hI i j (B.inverse F).val.1
    _ = _ := congrArg (fun x : ℝ => if n07aScalarFrequency i = j then x else 0)
      (n07aReferenceScalarMap_apply B i F).symm

end ContinuousFlexibility.Analysis
