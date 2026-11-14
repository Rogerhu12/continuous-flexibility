import ContinuousFlexibility.Analysis.RadialReferencePrincipalFormulas
import ContinuousFlexibility.Analysis.ReferenceCircleFlow
import ContinuousFlexibility.Analysis.N04bOperatorGerms

/-!
# The potential of radial chart and height germs

The radial representatives are the actual zero-angle slices. Their total
derivatives suffice for the local operator formula. A unit radial density
and zero mixed density force the actual physical mixed coefficient to
vanish; this supplies the coefficient germ needed for the potential.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem radial_reference_chart_germ_on_strip
    {F : PolarPoint → PolarPoint} {l r : ℝ} {x : PolarPoint}
    (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)))
    (hshape : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ),
      F q = ((F (q.1, 0)).1, q.2))
    (hx : x ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    F =ᶠ[𝓝 x] positiveReferenceCylinderChart (fun t => (F (t, 0)).1) ∧
      DifferentiableAt ℝ (fun t => (F (t, 0)).1) x.1 := by
  have hU : IsOpen (Ioo l r ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  refine ⟨?_, ?_⟩
  · filter_upwards [hU.mem_nhds hx] with q hq
    exact hshape q hq
  · have hx₀ : (x.1, (0 : ℝ)) ∈ Ioo l r ×ˢ (univ : Set ℝ) :=
      ⟨hx.1, mem_univ _⟩
    have hdF := (hF.contDiffAt (hU.mem_nhds hx₀)).differentiableAt (by simp)
    have hdline : DifferentiableAt ℝ (fun t : ℝ => (t, (0 : ℝ))) x.1 :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    have hd : DifferentiableAt ℝ (fun t => F (t, 0)) x.1 :=
      hdF.comp x.1 hdline
    exact hd.fst

theorem physical_mixed_zero_of_radial_unit_density
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {l r : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)))
    (hshape : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ),
      F q = ((F (q.1, 0)).1, q.2))
    (hheight : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ), h q = h (q.1, 0))
    (hunit : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ),
      (coordinatePrincipalDensity A F h).a q = 1 ∧
        (coordinatePrincipalDensity A F h).b q = 0)
    {x : PolarPoint} (hx : x ∈ Ioo l r ×ˢ (univ : Set ℝ)) : A.b x = 0 := by
  obtain ⟨hFg, hY⟩ := radial_reference_chart_germ_on_strip hF hshape hx
  have hHg : h =ᶠ[𝓝 x] (fun q : PolarPoint => h (q.1, 0)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hx] with q hq
    exact hheight q hq
  have hform := coordinatePrincipalDensity_radial_cylinder
    (A := A) (H := fun t => h (t, 0)) hY
  have ha := (coordinatePrincipalDensity_component_eventuallyEq
    (A := A) hFg hHg 0).self_of_nhds
  have hb := (coordinatePrincipalDensity_component_eventuallyEq
    (A := A) hFg hHg 1).self_of_nhds
  norm_num only [canonicalCoefficientComponent] at ha hb
  have hrad : h (x.1, 0) ^ 2 / |deriv (fun t => (F (t, 0)).1) x.1| *
      (A.a x * deriv (fun t => (F (t, 0)).1) x.1 ^ 2) = 1 :=
    hform.1.symm.trans (ha.symm.trans (hunit x hx).1)
  have hmix : h (x.1, 0) ^ 2 / |deriv (fun t => (F (t, 0)).1) x.1| *
      (A.b x * deriv (fun t => (F (t, 0)).1) x.1) = 0 :=
    hform.2.1.symm.trans (hb.symm.trans (hunit x hx).2)
  have hscale : h (x.1, 0) ^ 2 / |deriv (fun t => (F (t, 0)).1) x.1| ≠ 0 := by
    intro he
    rw [he, zero_mul] at hrad
    exact zero_ne_one hrad
  have hslope : deriv (fun t => (F (t, 0)).1) x.1 ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide : 2 ≠ 0), mul_zero, mul_zero] at hrad
    exact zero_ne_one hrad
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hmix).resolve_left hscale)).resolve_right hslope

theorem divergenceOperator_of_radial_germs
    {A : SymmetricCoefficients} {h : PolarPoint → ℝ} {w H : ℝ → ℝ}
    {x : PolarPoint}
    (hh : h =ᶠ[𝓝 x] (fun q : PolarPoint => H q.1))
    (ha : A.a =ᶠ[𝓝 x] (fun q : PolarPoint => w q.1))
    (hb : A.b =ᶠ[𝓝 x] (fun _ : PolarPoint => (0 : ℝ))) :
    divergenceOperator A h x = deriv (fun t => w t * deriv H t) x.1 := by
  have hrad :
      (fun q => A.a q * radialPartial (Radial.radialHeightField H) q +
        A.b q * angularPartial (Radial.radialHeightField H) q) =ᶠ[𝓝 x]
      Radial.radialHeightField (fun t => w t * deriv H t) := by
    filter_upwards [ha] with q hqa
    simp only [radialPartial_radialHeightField_total,
      angularPartial_radialHeightField_total, hqa, Radial.radialHeightField,
      mul_zero, add_zero]
  have hang :
      (fun q => A.b q * radialPartial (Radial.radialHeightField H) q +
        A.c q * angularPartial (Radial.radialHeightField H) q) =ᶠ[𝓝 x]
      (fun _ : PolarPoint => (0 : ℝ)) := by
    filter_upwards [hb] with q hqb
    simp only [hqb, angularPartial_radialHeightField_total, zero_mul, mul_zero, add_zero]
  calc
    divergenceOperator A h x = divergenceOperator A (Radial.radialHeightField H) x :=
      n04b_divergenceOperator_congr_germ hh
    _ = radialPartial (Radial.radialHeightField (fun t => w t * deriv H t)) x +
        angularPartial (fun _ : PolarPoint => (0 : ℝ)) x := by
      have hrad' := hrad.fderiv_eq (𝕜 := ℝ)
      have hang' := hang.fderiv_eq (𝕜 := ℝ)
      simp only [radialPartial, angularPartial] at hrad' hang'
      unfold divergenceOperator radialPartial angularPartial
      rw [hrad', hang']
    _ = deriv (fun t => w t * deriv H t) x.1 := by
      rw [radialPartial_radialHeightField_total]
      simp only [angularPartial_const, add_zero]

theorem inverseChartPotential_radial_formula_on_strip
    {A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {w : ℝ → ℝ} {l r : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)))
    (hshape : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ),
      F q = ((F (q.1, 0)).1, q.2))
    (hheight : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ), h q = h (q.1, 0))
    (ha : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ), A.a q = w q.1)
    (hb : ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ), A.b q = 0)
    {p : PolarPoint} (hp : G p ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    inverseChartPotential A F G h p =
      h ((G p).1, 0) *
        deriv (fun t => w t * deriv (fun s => h (s, 0)) t) (G p).1 /
          |deriv (fun t => (F (t, 0)).1) (G p).1| := by
  obtain ⟨hFg, hY⟩ := radial_reference_chart_germ_on_strip hF hshape hp
  have hU : IsOpen (Ioo l r ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hHg : h =ᶠ[𝓝 (G p)] (fun q : PolarPoint => h (q.1, 0)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hheight q hq
  have hag : A.a =ᶠ[𝓝 (G p)] (fun q : PolarPoint => w q.1) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact ha q hq
  have hbg : A.b =ᶠ[𝓝 (G p)] (fun _ : PolarPoint => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hb q hq
  have hJ : planeJacobian F (G p) = deriv (fun t => (F (t, 0)).1) (G p).1 := by
    calc
      _ = planeJacobian (positiveReferenceCylinderChart (fun t => (F (t, 0)).1))
          (G p) := by simp only [planeJacobian, hFg.fderiv_eq]
      _ = _ := planeJacobian_positiveReferenceCylinderChart hY
  unfold inverseChartPotential
  rw [divergenceOperator_of_radial_germs (w := w) (H := fun t => h (t, 0))
    hHg hag hbg, hJ, hHg.self_of_nhds]

end ContinuousFlexibility.Analysis
