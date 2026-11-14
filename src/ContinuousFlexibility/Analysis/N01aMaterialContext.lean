module

public import ContinuousFlexibility.Analysis.AffineMaterialFull

/-!
# Choosing the canonical material data for N01a

The explicit material construction is used so that the optical estimates
can be compared with its sampled coefficient weight. The sampling collars
are exactly those already provided by the accumulating profile.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

theorem exists_n01a_affineMaterialData {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ sample : ℕ → ℝ, IsMaterialData D (affineMaterialData D sample) ∧
      (∀ m, sample m ∈ D.cells m) ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ m,
        1 ≤ Real.log ((affineMaterialData D sample).E0 (sample m)) ∧
        radialQ (D.cellIndex m) ≤
          A * Real.log ((affineMaterialData D sample).E0 (sample m)) := by
  have hab : D.a < D.b := hD.choose_spec.1.2.1
  obtain ⟨sample, hsample, hwidth, hcompare⟩ := exists_affineMaterialData_sampling hD
  have hT : IsMaterialData D (affineMaterialData D sample) :=
    ⟨affineMaterialData_smooth_scalar hab,
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
  obtain ⟨A, K, hA, _, hb⟩ := affineMaterialData_cell_log_bounds (sample := sample) hD
  refine ⟨sample, hT, hsample, A, hA, fun m => ?_⟩
  exact ⟨(hb m (sample m) (hsample m)).1, (hb m (sample m) (hsample m)).2.1⟩

end ContinuousFlexibility.Statements
