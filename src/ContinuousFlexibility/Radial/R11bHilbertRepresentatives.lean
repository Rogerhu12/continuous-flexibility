import ContinuousFlexibility.Radial.R11bHilbertModes
import ContinuousFlexibility.Statements.RadialTargets

/-!
# Representatives and ordinary radial integrals

The actual radial Hilbert density is strictly positive on the core, so its
a.e. equality is exactly ordinary radial a.e. equality there. This permits
raw angular coefficients and their L² classes to be used interchangeably in
the frozen modal weak graph.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem r11b_radialHilbert_ae_eq_iff {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {α : Type*} {f g : ℝ → α} :
    f =ᵐ[radialHilbertMeasure D] g ↔ f =ᵐ[volume.restrict (radialCore D)] g := by
  apply withDensity_ae_eq (r11b_radial_density_measurable hgeom).aemeasurable.ennreal_ofReal
  exact (r11b_radial_density_pos_ae hgeom).mono
    (fun r hr => (ENNReal.ofReal_pos.mpr hr).ne')

theorem r11b_toLp_radialHilbert_ae {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {f : ℝ → ℝ}
    (hf : MemLp f 2 (radialHilbertMeasure D)) :
    ((hf.toLp f : RadialModeL2 D) : ℝ → ℝ) =ᵐ[volume.restrict (radialCore D)] f :=
  (r11b_radialHilbert_ae_eq_iff hgeom).mp hf.coeFn_toLp

theorem r11b_zero_radialHilbert_ae {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) :
    ((0 : RadialModeL2 D) : ℝ → ℝ) =ᵐ[volume.restrict (radialCore D)] 0 :=
  (r11b_radialHilbert_ae_eq_iff hgeom).mp Lp.coeFn_zero

theorem r11b_intervalIntegral_eq_core {D : ReferenceData} (hab : D.a ≤ D.b)
    (f : ℝ → ℝ) : (∫ r in D.a..D.b, f r) = ∫ r in radialCore D, f r := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  rfl

theorem r11b_intervalIntegral_congr_core {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g : ℝ → ℝ} (hfg : f =ᵐ[volume.restrict (radialCore D)] g) :
    (∫ r in D.a..D.b, f r) = ∫ r in D.a..D.b, g r := by
  rw [r11b_intervalIntegral_eq_core hab, r11b_intervalIntegral_eq_core hab]
  exact integral_congr_ae hfg

end ContinuousFlexibility.Radial
