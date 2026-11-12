import ContinuousFlexibility.Analysis.N01aReferenceHeightWeights
import ContinuousFlexibility.Analysis.N01aReferenceWeightedMultiplier
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Material-coordinate square moments of a weighted radial output

The change of variables is performed with the actual affine material
coordinate and its proved derivative. The square-root density multiplier
is exactly the Jacobian needed for Lebesgue measure in the material line.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n01a_memLp_comp_affineRadius_of_density {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) {f : ℝ → ℝ} (hf : ContinuousOn f (radialCore D))
    (hdensity : MemLp (fun r =>
      Real.sqrt (((affineMaterialData D sample).ell r)⁻¹) * f r)
        2 (volume.restrict (radialCore D))) :
    MemLp (fun x => f ((affineMaterialData D sample).radius x)) 2 volume := by
  let T := affineMaterialData D sample
  have hinside (x : ℝ) : T.radius x ∈ radialCore D :=
    (affineMaterialData_radius_mem_rho (sample := sample) hab x).1
  have hc : Continuous (fun x => f (T.radius x)) :=
    hf.comp_continuous (contDiff_affineMaterialData_radius (sample := sample)).continuous hinside
  have himage : T.rho '' radialCore D = univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact ⟨T.radius x, hinside x,
      (affineMaterialData_radius_mem_rho (sample := sample) hab x).2⟩
  have hchange := integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    (f := T.rho) (f' := fun r => 1 / T.ell r) (s := radialCore D)
    measurableSet_Ioo
    (fun r hr => (hasDerivAt_affineMaterialData_rho (sample := sample) hab hr).hasDerivWithinAt)
    (strictMonoOn_affineMaterialData_rho (sample := sample) hab).monotoneOn
    (fun x => f (T.radius x) ^ 2)
  rw [himage, integrableOn_univ] at hchange
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  apply hchange.mpr
  apply hdensity.integrable_sq.congr
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with r hr
  rw [affineMaterialData_radius_rho (sample := sample) hab hr, smul_eq_mul,
    mul_pow, Real.sq_sqrt (inv_nonneg.mpr
      (affineMaterialData_positive (sample := sample) hab hr).1.le), one_div]

/-- Every fixed material envelope moment of an output at a strictly
stronger reference weight is genuinely square integrable. -/
theorem n01a_reference_material_moment_memLp {D : ReferenceData} {sample : ℕ → ℝ}
    (hD : IsAccumulatingProfile D) {f : ℝ → ℝ} (hf : Continuous f)
    {β ε M : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε)
    (houtput : OutputRealization D (β + ε) M 0
      ((fun p => f p.1 * Radial.cosineMode 2 p.2), 0)) (k : ℕ) :
    MemLp (fun x => (affineMaterialData D sample).M
        ((affineMaterialData D sample).radius x) ^ k *
      (affineMaterialData D sample).H ((affineMaterialData D sample).radius x) ^ (-β) *
      f ((affineMaterialData D sample).radius x)) 2 volume := by
  let T := affineMaterialData D sample
  have hprofile := hD
  obtain ⟨C, hbounds⟩ := hprofile
  have hgeom := hbounds.1
  have hpart := hbounds.2.1
  have hab : D.a < D.b := hgeom.2.1
  have hs := affineMaterialData_smooth_scalar (sample := sample) hab
  have hp (r : ℝ) (hr : r ∈ radialCore D) :=
    affineMaterialData_positive (sample := sample) hab hr
  have hell : ContinuousOn (fun r => (T.ell r)⁻¹) (radialCore D) :=
    ((hs T.ell (by simp [T])).continuousOn).inv₀ (fun r hr => (hp r hr).1.ne')
  have hw : ContinuousOn (fun r => T.M r ^ k * T.H r ^ (-β)) (radialCore D) :=
    ((hs T.M (by simp [T])).pow k).continuousOn.mul
      ((hs T.H (by simp [T])).rpow_const_of_ne
        (fun r hr => (hp r hr).2.1.ne')).continuousOn
  let g : ℝ → ℝ := fun r => Real.sqrt ((T.ell r)⁻¹) * (T.M r ^ k * T.H r ^ (-β))
  have hg : ContinuousOn g (radialCore D) := hell.sqrt.mul hw
  obtain ⟨K, hK, hbound⟩ := n01a_affine_height_cell_density_bound
    (sample := sample) hD hβ hε M k
  have hgb (m : ℕ) (r : ℝ) (hr : r ∈ D.cells m) :
      g r ^ 2 ≤ K * Real.exp (-2 * M * radialQ (D.cellIndex m) +
        2 * (β + ε) * radialS (D.cellIndex m)) := by
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr
      (hp r (hpart.2.2.2.1 m hr)).1.le)]
    exact hbound m r hr
  have hm := n01a_weighted_radial_multiplier_memLp hab.le hpart hf houtput hg hK hgb
  have hdensity : MemLp (fun r => Real.sqrt ((T.ell r)⁻¹) *
      (T.M r ^ k * T.H r ^ (-β) * f r)) 2 (volume.restrict (radialCore D)) := by
    simpa only [g, mul_assoc] using hm
  exact n01a_memLp_comp_affineRadius_of_density hab (hw.mul hf.continuousOn) hdensity

end ContinuousFlexibility.Statements
