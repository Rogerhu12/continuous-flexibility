import ContinuousFlexibility.Analysis.CylinderTestPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Circle data inside the fixed model Banach space

Extending a circle function constantly over a radial interval of length one,
and by zero elsewhere, is an isometry into the material cylinder `L²` space.
Applying it to every component embeds the natural circle Banach space into
the fixed `PhysicalModelBanach`. Its Hilbert adjoint is a contractive left
inverse. This supplies the Banach-space change needed by the circle Fourier
retraction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal

private instance circleAngleMeasure_sFinite : SFinite angleMeasure := by
  unfold angleMeasure
  infer_instance

private def circleUnitRadialMeasure : Measure ℝ :=
  volume.restrict (Ioc (0 : ℝ) 1)

private instance circleUnitRadialMeasure_probability :
    IsProbabilityMeasure circleUnitRadialMeasure := by
  constructor
  simp only [circleUnitRadialMeasure, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero, ENNReal.ofReal_one]

def circleCylinderWindow : Set PolarPoint := Ioc (0 : ℝ) 1 ×ˢ univ

theorem measurableSet_circleCylinderWindow : MeasurableSet circleCylinderWindow :=
  measurableSet_Ioc.prod MeasurableSet.univ

private theorem circleCylinderWindow_measure :
    materialCylinderMeasure.restrict circleCylinderWindow =
      circleUnitRadialMeasure.prod angleMeasure := by
  rw [materialCylinderMeasure_eq_prod, circleCylinderWindow, ← Measure.prod_restrict,
    Measure.restrict_univ]
  rfl

private theorem circleCylinderProjection_preserving :
    MeasurePreserving Prod.snd
      (materialCylinderMeasure.restrict circleCylinderWindow) angleMeasure := by
  rw [circleCylinderWindow_measure]
  exact measurePreserving_snd

private theorem circleCylinderProjection_quasiPreserving :
    Measure.QuasiMeasurePreserving Prod.snd materialCylinderMeasure angleMeasure := by
  rw [materialCylinderMeasure_eq_prod]
  exact Measure.quasiMeasurePreserving_snd

def circleCylinderExtension (f : AngleL2) : PolarPoint → ℝ :=
  circleCylinderWindow.indicator (fun p => f p.2)

private theorem circleCylinderExtension_memLp (f : AngleL2) :
    MemLp (circleCylinderExtension f) 2 materialCylinderMeasure := by
  apply (memLp_indicator_iff_restrict measurableSet_circleCylinderWindow).mpr
  exact (Lp.memLp f).comp_measurePreserving circleCylinderProjection_preserving

def circleCylinderEmbeddingFun (f : AngleL2) : CylinderL2 :=
  (circleCylinderExtension_memLp f).toLp (circleCylinderExtension f)

theorem circleCylinderEmbeddingFun_ae (f : AngleL2) :
    (circleCylinderEmbeddingFun f : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      circleCylinderExtension f :=
  MemLp.coeFn_toLp (circleCylinderExtension_memLp f)

theorem circleCylinderEmbeddingFun_norm (f : AngleL2) :
    ‖circleCylinderEmbeddingFun f‖ = ‖f‖ := by
  calc
    ‖circleCylinderEmbeddingFun f‖ =
        (eLpNorm (circleCylinderExtension f) 2 materialCylinderMeasure).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (circleCylinderEmbeddingFun_ae f)]
    _ = (eLpNorm f 2 angleMeasure).toReal := by
      unfold circleCylinderExtension
      rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_circleCylinderWindow]
      exact congrArg ENNReal.toReal
        (eLpNorm_comp_measurePreserving (Lp.memLp f).aestronglyMeasurable
          circleCylinderProjection_preserving)
    _ = ‖f‖ := by rw [Lp.norm_def]

/-- Unit radial extension, as a genuine linear isometry of the `L²` spaces. -/
def circleCylinderEmbedding : AngleL2 →ₗᵢ[ℝ] CylinderL2 where
  toFun := circleCylinderEmbeddingFun
  map_add' := by
    intro f g
    apply Lp.ext
    filter_upwards [circleCylinderEmbeddingFun_ae (f + g),
      circleCylinderEmbeddingFun_ae f, circleCylinderEmbeddingFun_ae g,
      Lp.coeFn_add (circleCylinderEmbeddingFun f) (circleCylinderEmbeddingFun g),
      circleCylinderProjection_quasiPreserving.ae (Lp.coeFn_add f g)]
      with p hfg hf hg hout hbase
    change (f + g) p.2 = f p.2 + g p.2 at hbase
    rw [hfg, hout]
    simp only [Pi.add_apply]
    rw [hf, hg]
    unfold circleCylinderExtension
    by_cases hp : p ∈ circleCylinderWindow
    · simpa only [Set.indicator_of_mem hp, Pi.add_apply] using hbase
    · simp only [Set.indicator_of_notMem hp, add_zero]
  map_smul' := by
    intro c f
    apply Lp.ext
    filter_upwards [circleCylinderEmbeddingFun_ae (c • f), circleCylinderEmbeddingFun_ae f,
      Lp.coeFn_smul c (circleCylinderEmbeddingFun f),
      circleCylinderProjection_quasiPreserving.ae (Lp.coeFn_smul c f)]
      with p hcf hf hout hbase
    change (c • f) p.2 = c • f p.2 at hbase
    simp only [RingHom.id_apply]
    rw [hcf, hout]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    unfold circleCylinderExtension
    by_cases hp : p ∈ circleCylinderWindow
    · simpa only [Set.indicator_of_mem hp, Pi.smul_apply, smul_eq_mul] using hbase
    · simp only [Set.indicator_of_notMem hp, mul_zero]
  norm_map' := circleCylinderEmbeddingFun_norm

theorem circleCylinderEmbedding_apply (f : AngleL2) :
    circleCylinderEmbedding f = circleCylinderEmbeddingFun f := rfl

/-- The natural Banach space of unweighted circle sequences. -/
abbrev CircleModelBanach := lp (fun _ : ℕ => AngleL2) 2

private def circleFamilyCylinderEmbeddingFun (u : CircleModelBanach) : PhysicalModelBanach :=
  ⟨fun m => circleCylinderEmbedding (u m),
    (lp.memℓp u).mono' (fun m => (circleCylinderEmbedding.norm_map (u m)).le)⟩

private theorem circleFamilyCylinderEmbeddingFun_apply (u : CircleModelBanach) (m : ℕ) :
    circleFamilyCylinderEmbeddingFun u m = circleCylinderEmbedding (u m) := rfl

private theorem circleFamilyCylinderEmbeddingFun_norm (u : CircleModelBanach) :
    ‖circleFamilyCylinderEmbeddingFun u‖ = ‖u‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    rw [circleFamilyCylinderEmbeddingFun_apply, circleCylinderEmbedding.norm_map]
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    rw [circleFamilyCylinderEmbeddingFun_apply, circleCylinderEmbedding.norm_map]

/-- Isometric inclusion of the natural Fourier Banach space into the fixed
Banach space appearing in `modelGrading`. -/
def circleFamilyCylinderEmbedding : CircleModelBanach →ₗᵢ[ℝ] PhysicalModelBanach where
  toFun := circleFamilyCylinderEmbeddingFun
  map_add' := by
    intro u v
    apply lp.ext
    funext m
    simp only [lp.coeFn_add, Pi.add_apply, circleFamilyCylinderEmbeddingFun_apply, map_add]
  map_smul' := by
    intro c u
    apply lp.ext
    funext m
    simp only [lp.coeFn_smul, Pi.smul_apply, circleFamilyCylinderEmbeddingFun_apply, map_smul,
      RingHom.id_apply]
  norm_map' := circleFamilyCylinderEmbeddingFun_norm

theorem circleFamilyCylinderEmbedding_apply (u : CircleModelBanach) (m : ℕ) :
    circleFamilyCylinderEmbedding u m = circleCylinderEmbedding (u m) :=
  circleFamilyCylinderEmbeddingFun_apply u m

/-- The contraction back to circle data is the adjoint of the preceding
isometry; it is not extra data assumed from a caller. -/
def circleFamilyCylinderProjection : PhysicalModelBanach →L[ℝ] CircleModelBanach :=
  circleFamilyCylinderEmbedding.toContinuousLinearMap.adjoint

theorem circleFamilyCylinderProjection_embedding (u : CircleModelBanach) :
    circleFamilyCylinderProjection (circleFamilyCylinderEmbedding u) = u := by
  have h := DFunLike.congr_fun circleFamilyCylinderEmbedding.adjoint_comp_self u
  simpa only [circleFamilyCylinderProjection, ContinuousLinearMap.comp_apply, one_apply_eq_self,
    LinearIsometry.coe_toContinuousLinearMap] using h

theorem circleFamilyCylinderProjection_norm_le (u : PhysicalModelBanach) :
    ‖circleFamilyCylinderProjection u‖ ≤ ‖u‖ := by
  have hnorm : ‖circleFamilyCylinderProjection‖ ≤ 1 := by
    unfold circleFamilyCylinderProjection
    rw [LinearIsometryEquiv.norm_map]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [LinearIsometry.coe_toContinuousLinearMap, circleFamilyCylinderEmbedding.norm_map,
      one_mul] using le_refl ‖v‖
  exact (circleFamilyCylinderProjection.le_opNorm u).trans
    ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg u)).trans_eq (one_mul _))

end ContinuousFlexibility.Statements
