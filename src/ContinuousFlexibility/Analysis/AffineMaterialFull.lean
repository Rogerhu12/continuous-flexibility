module

public import ContinuousFlexibility.Analysis.AffineMaterialSampling
public import ContinuousFlexibility.Analysis.MaterialRadialExpansion

/-!
# The material coordinates and weights for an accumulating radial profile

The affine scalar construction and the actual trace scaffold give one
material data witness satisfying every clause of the W01 target.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

theorem affineMaterial_W01_statement : W01Statement := by
  intro D hRef
  have hab : D.a < D.b := hRef.choose_spec.1.2.1
  obtain ⟨sample, hsample, hwidth, hcompare⟩ := exists_affineMaterialData_sampling hRef
  exact ⟨affineMaterialData D sample,
    affineMaterialData_smooth_scalar hab,
    fun _ hr => affineMaterialData_positive hab hr,
    fun _ hr => hasDerivAt_affineMaterialData_rho hab hr,
    strictMonoOn_affineMaterialData_rho hab,
    tendsto_affineMaterialData_rho_left hab,
    tendsto_affineMaterialData_rho_right hab,
    contDiff_affineMaterialData_radius,
    affineMaterialData_radius_mem_rho hab,
    fun _ hr => affineMaterialData_radius_rho hab hr,
    hasDerivAt_affineMaterialData_radius hab,
    affineMaterialData_endpoint_formulas hab,
    affineMaterialData_E0_rpow_le_M,
    affineMaterialData_H_rpow_mul_M_rpow hab,
    logarithmicDerivativeBounds_affineMaterialData hab,
    radialMaterialExpansion_affineMaterialData hab,
    hsample, hwidth, hcompare⟩

end ContinuousFlexibility.Statements
