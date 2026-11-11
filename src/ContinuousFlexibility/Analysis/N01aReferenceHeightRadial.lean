import ContinuousFlexibility.Analysis.N01aReferenceHeightMaterialJets
import ContinuousFlexibility.Analysis.N01aReferenceHeightMoments

/-!
# Square integrability of the actual weighted radial reference jets

The two output realizations provide the zeroth and first radial moments.
The actual Jacobi equation and coordinate chain rule supply every higher
jet, so no regularity or high-jet integrability is added as a premise.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n01aReferenceWeightedRadial (D : ReferenceData) (sample : ℕ → ℝ) (β x : ℝ) : ℝ :=
  (affineMaterialData D sample).H ((affineMaterialData D sample).radius x) ^ (-β) *
    D.phi ((affineMaterialData D sample).radius x)

theorem contDiff_n01aReferenceWeightedRadial {D : ReferenceData} {sample : ℕ → ℝ}
    (hD : RadialProfileGeometry D) (β : ℝ) :
    ContDiff ℝ ∞ (n01aReferenceWeightedRadial D sample β) := by
  let T := affineMaterialData D sample
  have hi (x : ℝ) := (affineMaterialData_radius_mem_rho (sample := sample) hD.2.1 x).1
  have hH : ContDiff ℝ ∞ (fun x => T.H (T.radius x)) :=
    (affineMaterialData_smooth_scalar (sample := sample) hD.2.1 T.H (by simp [T])).comp_contDiff
      (contDiff_affineMaterialData_radius (sample := sample)) hi
  have hp (x : ℝ) : T.H (T.radius x) ≠ 0 :=
    (affineMaterialData_positive (sample := sample) hD.2.1 (hi x)).2.1.ne'
  exact (hH.rpow_const_of_ne hp).mul
    (hD.2.2.2.1.1.comp (contDiff_affineMaterialData_radius (sample := sample)))

theorem n01a_reference_weighted_radial_jets_memLp {D : ReferenceData} {sample : ℕ → ℝ}
    (hD : IsRadialReference D) {β ε M : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε)
    (hphi : OutputRealization D (β + ε) M 0
      ((fun p => D.phi p.1 * Radial.cosineMode 2 p.2), 0))
    (hphi' : OutputRealization D (β + ε) M 0
      ((fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2), 0)) (a c : ℕ) :
    MemLp (fun x => (affineMaterialData D sample).M ((affineMaterialData D sample).radius x) ^ c *
      iteratedDeriv a (n01aReferenceWeightedRadial D sample β) x) 2 volume := by
  obtain ⟨C₀, hprofile⟩ := hD.1
  have hgeom := hprofile.1
  let T := affineMaterialData D sample
  have hi (x : ℝ) := (affineMaterialData_radius_mem_rho (sample := sample) hgeom.2.1 x).1
  have hM (x : ℝ) : 0 ≤ T.M (T.radius x) := zero_le_one.trans
    (affineMaterialData_positive (sample := sample) hgeom.2.1 (hi x)).2.2.2
  have hH (x : ℝ) : 0 ≤ T.H (T.radius x) ^ (-β) :=
    Real.rpow_nonneg
      (affineMaterialData_positive (sample := sample) hgeom.2.1 (hi x)).2.1.le _
  obtain ⟨k, C, hC, hb⟩ := n01a_reference_weighted_material_jets (sample := sample) hD β a
  let F : ℝ → ℝ := fun x => T.M (T.radius x) ^ (c + k) * T.H (T.radius x) ^ (-β) *
    D.phi (T.radius x)
  let G : ℝ → ℝ := fun x => T.M (T.radius x) ^ (c + k) * T.H (T.radius x) ^ (-β) *
    deriv D.phi (T.radius x)
  have hF : MemLp F 2 volume := n01a_reference_material_moment_memLp (sample := sample)
    hD.1 hgeom.2.2.2.1.1.continuous hβ hε hphi (c + k)
  have hG : MemLp G 2 volume := n01a_reference_material_moment_memLp (sample := sample)
    hD.1 (contDiff_infty_iff_deriv.mp hgeom.2.2.2.1.1).2.continuous hβ hε hphi' (c + k)
  have hmajor : MemLp (fun x => C * (‖F x‖ + ‖G x‖)) 2 volume :=
    (hF.norm.add hG.norm).const_mul C
  have hMc : Continuous (fun x => T.M (T.radius x) ^ c) :=
    (((affineMaterialData_smooth_scalar (sample := sample) hgeom.2.1 T.M (by simp [T])).comp_contDiff
      (contDiff_affineMaterialData_radius (sample := sample)) hi).pow c).continuous
  have hJc : Continuous (iteratedDeriv a (n01aReferenceWeightedRadial D sample β)) :=
    (contDiff_n01aReferenceWeightedRadial hgeom β).continuous_iteratedDeriv a (by simp)
  apply hmajor.mono' (hMc.mul hJc).aestronglyMeasurable
  filter_upwards [] with x
  have hjet := hb x (mem_univ x)
  change |iteratedDeriv a (n01aReferenceWeightedRadial D sample β) x| ≤
    C * T.M (T.radius x) ^ k *
      (T.H (T.radius x) ^ (-β) * (|D.phi (T.radius x)| + |deriv D.phi (T.radius x)|)) at hjet
  have hweight : 0 ≤ T.M (T.radius x) ^ (c + k) * T.H (T.radius x) ^ (-β) :=
    mul_nonneg (pow_nonneg (hM x) _) (hH x)
  have hFnorm : ‖F x‖ =
      (T.M (T.radius x) ^ (c + k) * T.H (T.radius x) ^ (-β)) * |D.phi (T.radius x)| := by
    change |(T.M (T.radius x) ^ (c + k) * T.H (T.radius x) ^ (-β)) * D.phi (T.radius x)| = _
    rw [abs_mul, abs_of_nonneg hweight]
  have hGnorm : ‖G x‖ =
      (T.M (T.radius x) ^ (c + k) * T.H (T.radius x) ^ (-β)) * |deriv D.phi (T.radius x)| := by
    change |(T.M (T.radius x) ^ (c + k) * T.H (T.radius x) ^ (-β)) * deriv D.phi (T.radius x)| = _
    rw [abs_mul, abs_of_nonneg hweight]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (hM x) c)]
  calc
    _ ≤ T.M (T.radius x) ^ c *
        (C * T.M (T.radius x) ^ k *
          (T.H (T.radius x) ^ (-β) * (|D.phi (T.radius x)| + |deriv D.phi (T.radius x)|))) :=
      mul_le_mul_of_nonneg_left hjet (pow_nonneg (hM x) c)
    _ = C * (‖F x‖ + ‖G x‖) := by
      rw [hFnorm, hGnorm, pow_add]
      ring

end ContinuousFlexibility.Statements
