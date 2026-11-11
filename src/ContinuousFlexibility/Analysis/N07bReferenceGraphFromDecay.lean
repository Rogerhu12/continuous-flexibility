import ContinuousFlexibility.Analysis.N07bContinuousRadialMembers
import ContinuousFlexibility.Analysis.N07bReferenceCompatibility

/-!
# The actual reference graph from finite regularity and material decay

The hypotheses concern the physical field and its genuine differential
expression.  C² regularity gives Green symmetry, the radial endpoint
degeneracy gives source compatibility, and actual material decay gives the
natural weighted source and output classes.  No graph membership, weak
equation, or natural-space membership is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

/-- The actual reference differential expression of a global C² field is
continuous. Flatness of the profile removes the apparent singularity at
radius zero, so this statement does not depend on endpoint representatives. -/
theorem n07b_c2_continuous_referencePDE {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ 2 u) :
    Continuous (fun p : PolarPoint => radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2) := by
  have hwr : Continuous (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hgeom.2.2.1.1).2.continuous
  have hr : Continuous (radialPartial u) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (contDiffAt_radialPartial hu.contDiffAt (m := 1) (by norm_num)).continuousAt
  have hrr : Continuous (radialPartial (radialPartial u)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (contDiffAt_radialPartial
      (contDiffAt_radialPartial hu.contDiffAt (m := 1) (by norm_num))
      (m := 0) (by norm_num)).continuousAt
  have hθθ : Continuous (angularPartial (angularPartial u)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (contDiffAt_angularPartial
      (contDiffAt_angularPartial hu.contDiffAt (m := 1) (by norm_num))
      (m := 0) (by norm_num)).continuousAt
  have heq : (fun p : PolarPoint => radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2) =
      (fun p => deriv D.w p.1 * radialPartial u p +
        D.w p.1 * radialPartial (radialPartial u) p +
        deriv D.w p.1 / p.1 * angularPartial (angularPartial u) p) := by
    funext p
    exact n07b_c2_radialPDE_eq_polar_jets
      (hgeom.2.2.1.1.differentiable (by simp) p.1) hu.contDiffAt
  rw [heq]
  exact (((hwr.comp continuous_fst).mul hr).add
    ((hgeom.2.2.1.1.continuous.comp continuous_fst).mul hrr)).add
      (((r11b_continuous_flat_deriv_div hgeom.1 hgeom.2.2.1).comp continuous_fst).mul hθθ)

private theorem n07b_referenceGraph_column_continuous {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    Continuous (fun p : PolarPoint => referenceColumn D p.1 * cosineMode 2 p.2) := by
  have hcos : Continuous (cosineMode 2) :=
    continuous_iff_continuousAt.mpr (fun θ => (hasDerivAt_cosineMode 2 θ).continuousAt)
  exact ((r11b_continuous_referenceColumn hgeom hborder).comp continuous_fst).mul
    (hcos.comp continuous_snd)

/-- A pointwise reference equation on the open annulus implies its actual
weak equation. The three test products are genuinely integrable for the
physical measure before Fubini and linearity are used. -/
theorem n07b_c2_reference_weak_of_eqOn {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    {u f : PolarPoint → ℝ} {μ : ℝ} (hu : ContDiff ℝ 2 u)
    (hup : Function.Periodic u (0, Real.pi))
    (hf : EqOn f (fun p =>
      radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2 +
        μ * referenceColumn D p.1 * cosineMode 2 p.2) (annularOpen D))
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    radialWeakPairing D u φ + μ *
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceColumn D r * cosineMode 2 θ * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ)) := by
  let P : PolarPoint → ℝ :=
    fun p => radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2
  let Q : PolarPoint → ℝ := fun p => referenceColumn D p.1 * cosineMode 2 p.2
  have hPLp : MemLp P 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (n07b_c2_continuous_referencePDE hgeom hu)
  have hQLp : MemLp Q 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (n07b_referenceGraph_column_continuous hgeom hborder)
  have hφLp : MemLp φ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hφ.1.continuous
  have hPI : Integrable (fun p => P p * φ p) (radialPhysicalMeasure D) :=
    hPLp.integrable_mul hφLp
  have hQI : Integrable (fun p => Q p * φ p) (radialPhysicalMeasure D) :=
    hQLp.integrable_mul hφLp
  have hpair : (fun p => P p * φ p + μ * (Q p * φ p)) =ᵐ[radialPhysicalMeasure D]
      (fun p => f p * φ p) := by
    have hstrip : ∀ᵐ p ∂radialPhysicalMeasure D,
        p ∈ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
    filter_upwards [hstrip] with p hp
    change P p * φ p + μ * (Q p * φ p) = f p * φ p
    rw [hf ⟨hp.1, mem_univ _⟩]
    dsimp only [P, Q]
    ring
  have hFI : Integrable (fun p => f p * φ p) (radialPhysicalMeasure D) :=
    (hPI.add (hQI.const_mul μ)).congr hpair
  have hsum : (∫ p, P p * φ p ∂radialPhysicalMeasure D) +
      μ * (∫ p, Q p * φ p ∂radialPhysicalMeasure D) =
      ∫ p, f p * φ p ∂radialPhysicalMeasure D := by
    rw [← integral_const_mul, ← integral_add hPI (hQI.const_mul μ)]
    exact integral_congr_ae hpair
  rw [n07b_c2_reference_green hgeom hu.contDiffOn hup hφ]
  change (∫ r in D.a..D.b, radialAngularMean (fun θ => P (r, θ) * φ (r, θ))) +
      μ * (∫ r in D.a..D.b, radialAngularMean (fun θ => Q (r, θ) * φ (r, θ))) = _
  rw [r11b_integral_angularMean_eq hgeom.2.1.le hPI,
    r11b_integral_angularMean_eq hgeom.2.1.le hQI,
    r11b_integral_angularMean_eq hgeom.2.1.le hFI]
  calc
    _ = (2 * Real.pi)⁻¹ * ((∫ p, P p * φ p ∂radialPhysicalMeasure D) +
        μ * (∫ p, Q p * φ p ∂radialPhysicalMeasure D)) := by ring
    _ = _ := by rw [hsum]

/-- Primitive physical regularity, actual material decay, symmetry and the
row condition place a genuine solution in the maximal reference graph.
The weighted exponents are arbitrary subject only to `γ < δ` and `0 < δ`. -/
theorem n07b_referenceGraph_of_material_decay {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D) {δ γ Ku Kf a μ : ℝ}
    (hδ : 0 < δ) (hγδ : γ < δ) (hKu : 0 ≤ Ku) (hKf : 0 ≤ Kf)
    {u f : PolarPoint → ℝ} (hu : ContDiff ℝ 2 u)
    (hup : Function.Periodic u (0, Real.pi))
    (hue : ∀ r θ, u (r, -θ) = u (r, θ))
    (hfp : Function.Periodic f (0, Real.pi))
    (hfe : ∀ r θ, f (r, -θ) = f (r, θ))
    (hf : EqOn f (fun p =>
      radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2 +
        μ * referenceColumn D p.1 * cosineMode 2 p.2) (annularOpen D))
    (hrow : referenceRow D u = 0)
    (hub : ∀ p ∈ annularOpen D, |u p - a * D.chiLeft p.1| ≤ Ku * T.H p.1 ^ δ)
    (hfb : ∀ p ∈ annularOpen D, |f p| ≤ Kf * T.H p.1 ^ δ)
    (M₀ M₁ : ℝ) : ReferenceGraph D γ M₀ M₁ (u, μ) (f, 0) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hforcing : Continuous (fun p : PolarPoint =>
      radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2 +
        μ * referenceColumn D p.1 * cosineMode 2 p.2) := by
    have hQ := (n07b_referenceGraph_column_continuous hgeom hborder).const_mul μ
    simpa only [mul_assoc] using (n07b_c2_continuous_referencePDE hgeom hu).add hQ
  have hfcont : ContinuousOn f (annularOpen D) := by
    intro p hp
    have heq : f =ᶠ[𝓝 p] (fun q =>
        radialPDE D.w (fun r θ => u (r, θ)) q.1 q.2 +
          μ * referenceColumn D q.1 * cosineMode 2 q.2) := by
      filter_upwards [hopen.mem_nhds hp] with q hq
      exact hf hq
    exact (hforcing.continuousAt.congr_of_eventuallyEq heq).continuousWithinAt
  have hQzero : physicalSourceIntegral D f = 0 :=
    n07b_c2_reference_compatibility_of_eqOn hgeom (fun _ _ => hu.contDiffAt) hup μ hf
  have hsource : SourceMember D γ M₀ (f, 0) :=
    n07b_sourceMember_of_material_decay hD hT hδ hγδ hKf hfcont hfb hfp hfe M₀ 0 hQzero
  have houtput : OutputRealization D γ M₁ a (u, μ) :=
    n07b_outputRealization_of_material_decay hD hT hborder hδ hγδ hKu
      hu.continuous.continuousOn hub hup hue M₁
  exact ⟨⟨a, houtput⟩, hsource, hrow,
    fun _ hφ => n07b_c2_reference_weak_of_eqOn hgeom hborder hu hup hf hφ⟩

end ContinuousFlexibility.Analysis
