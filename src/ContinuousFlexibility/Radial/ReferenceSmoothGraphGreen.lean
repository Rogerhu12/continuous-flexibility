import ContinuousFlexibility.Radial.ReferenceSmoothGreen
import ContinuousFlexibility.Radial.ReferenceRadialCutoff
import ContinuousFlexibility.Radial.ReferenceGraphClosed
import ContinuousFlexibility.Radial.ReferenceGreenClosure

/-!
# Green reciprocity on the smooth weak graph

First move derivatives onto the smooth graph field by the genuine Green
identity. Radial cutoffs then extend the weak equation to arbitrary smooth
periodic tests by dominated convergence. This proves reciprocity on the
smooth graph without assuming a pointwise PDE or an endpoint trace theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

/-- A smooth graph field can be tested against every smooth periodic field:
the radial support restriction is removed by actual bounded cutoffs. -/
theorem reference_smooth_graph_test {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hUF : ReferenceGraph D γ M₀ M₁ U F) (hU : ContDiff ℝ ∞ U.1)
    {v : PolarPoint → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvp : Function.Periodic v (0, 2 * Real.pi)) :
    radialWeakPairing D v U.1 + U.2 * referenceRow D v =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ) * v (r, θ)) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hup : Function.Periodic U.1 (0, 2 * Real.pi) :=
    reference_periodic_two_pi hUF.1.choose_spec.2.2.1
  have hv₂ : MemLp v 2 (radialPhysicalMeasure D) := r11b_continuous_memLp hv.continuous
  have hf₂ : MemLp F.1 2 (radialPhysicalMeasure D) :=
    r11b_source_memLp hD hγ hUF.2.1
  have hLU₂ : MemLp (fun x : PolarPoint =>
      radialPDE D.w (fun r θ => U.1 (r, θ)) x.1 x.2) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_continuous_radialPDE_test hgeom hU)
  have hcol₂ : MemLp (fun x : PolarPoint =>
      referenceColumn D x.1 * cosineMode 2 x.2) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (reference_column_mode_continuous hgeom hborder)
  have hLU := hv₂.integrable_mul hLU₂
  have hcol := hcol₂.integrable_mul hv₂
  have hf := hf₂.integrable_mul hv₂
  have hLUconv := reference_mean_cutoff_tendsto hgeom.2.1.le hLU
  have hcolconv := reference_mean_cutoff_tendsto hgeom.2.1.le hcol
  have hfconv := reference_mean_cutoff_tendsto hgeom.2.1.le hf
  have heq (n : ℕ) :
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceRadialCutoff D n r *
          (v (r, θ) * radialPDE D.w (fun s φ => U.1 (s, φ)) r θ))) +
      U.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceRadialCutoff D n r *
          ((referenceColumn D r * cosineMode 2 θ) * v (r, θ)))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceRadialCutoff D n r * (F.1 (r, θ) * v (r, θ))) := by
    let ψ : PolarPoint → ℝ := fun x => referenceRadialCutoff D n x.1 * v x
    have hψ : RadialTest D ψ := referenceRadialCutoff_test hv hvp n
    have hw := hUF.2.2.2 ψ hψ
    rw [reference_smooth_pairing_symm hgeom hU hψ.1 hup hψ.2.1] at hw
    simpa only [ψ, radialWeakPairing, mul_assoc, mul_left_comm, mul_comm] using hw
  have hidentity :
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        v (r, θ) * radialPDE D.w (fun s φ => U.1 (s, φ)) r θ)) +
      U.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (referenceColumn D r * cosineMode 2 θ) * v (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ) * v (r, θ)) := by
    apply tendsto_nhds_unique (hLUconv.add (hcolconv.const_mul U.2))
    simpa only [heq] using hfconv
  have hrow :
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (referenceColumn D r * cosineMode 2 θ) * v (r, θ))) = referenceRow D v := by
    rw [r11b_integral_angularMean_eq hgeom.2.1.le hcol,
      referenceRow_eq_physical_pairing hgeom hborder hv₂]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun x => mul_comm _ _)
  rw [hrow] at hidentity
  exact hidentity

/-- The final border row is the physical pairing with the actual column,
so the smooth weak graph satisfies the full bordered Green formula. -/
theorem reference_smooth_graph_green {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U V : RadialUnknown} {F K : RadialSource}
    (hUF : ReferenceGraph D γ M₀ M₁ U F)
    (hVK : ReferenceGraph D γ M₀ M₁ V K)
    (hU : SmoothAdmissibleField D U) (hV : SmoothAdmissibleField D V) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => U.1 (r, θ) * K.1 (r, θ))) +
        U.2 * K.2 =
      (∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ) * V.1 (r, θ))) +
        F.2 * V.2 := by
  have hu := reference_smooth_graph_test hD hborder hγ hUF hU.1 hV.1
    (reference_periodic_two_pi hV.2.1)
  have hv := reference_smooth_graph_test hD hborder hγ hVK hV.1 hU.1
    (reference_periodic_two_pi hU.2.1)
  have hsym := reference_smoothAdmissible_pairing_symm hD.choose_spec.1 hU hV
  rw [hVK.2.2.1] at hu
  rw [hUF.2.2.1, hsym] at hv
  have hswap :
      (∫ r in D.a..D.b, radialAngularMean (fun θ => K.1 (r, θ) * U.1 (r, θ))) =
        ∫ r in D.a..D.b, radialAngularMean (fun θ => U.1 (r, θ) * K.1 (r, θ)) := by
    congr 1
    funext r
    congr 1
    funext θ
    exact mul_comm _ _
  rw [hswap] at hv
  nlinarith

/-- Full Green reciprocity now requires only the actual smooth-core density
theorem; no separate reciprocity assumption remains. -/
theorem referenceGreenReciprocity_of_smooth_core {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    (hcore : ReferenceSmoothCoreClosure D γ M₀ M₁) :
    ReferenceGreenReciprocity D γ M₀ M₁ :=
  referenceGreenReciprocity_of_smoothCoreClosure hD hborder hγ hcore
    (fun _ _ _ _ hUF hVK hU hV => reference_smooth_graph_green hD hborder hγ hUF hVK hU hV)

end ContinuousFlexibility.Radial
