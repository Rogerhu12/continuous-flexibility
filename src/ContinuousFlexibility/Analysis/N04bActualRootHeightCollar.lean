import ContinuousFlexibility.Analysis.N04bRootBoundaryGeometry
import ContinuousFlexibility.Analysis.N04bFieldRegularity
import ContinuousFlexibility.Analysis.RootCharacteristicFactor

/-!
# A genuine positive smooth root height for the actual corrected coefficient

The leading coefficient is the actual corrected a evaluated in the
oriented physical root coordinate. Raw field regularity supplies its
local smoothness and positivity. Intersecting the genuine chart collar
with a physical radial collar gives a single two-sided strip where the
actual height quotient is smooth, positive and exactly normalized.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual leading coefficient in the oriented root variable. -/
def n04bRootLeadingCoefficient {S : PhysicalSpacesData}
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ)
    (r₀ ι : ℝ) (p : PolarPoint) : ℝ :=
  (L.coefficients z).a (rootProfileShift r₀ ι p)

/-- Local regularity and positivity are inherited from the raw corrected
field by the actual affine physical coordinate. -/
theorem n04b_rootLeadingCoefficient_regularity
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r₀ ι : ℝ} {p : PolarPoint}
    (hp : rootProfileShift r₀ ι p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (n04bRootLeadingCoefficient L z r₀ ι) p ∧
      0 < n04bRootLeadingCoefficient L z r₀ ι p := by
  have hshift : ContDiff ℝ ∞ (rootProfileShift r₀ ι) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have ha := (hfield.smooth_coefficients z hz hs).1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  exact ⟨ha.comp p hshift.contDiffAt,
    hfield.positive_a z hz hs (rootProfileShift r₀ ι p) hp⟩

/-- All inverse-chart and height positivity conditions hold on one true
two-sided periodic collar of the physical root. The height uses the
actual coefficient, with no assumed root quotient formula. -/
theorem n04b_exists_actual_root_height_collar
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r₀ ι : ℝ} (hr₀ : r₀ ∈ Ioo D.a D.b)
    {d c₀ : PolarPoint → ℝ} {hL : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ hL Φ R σ G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r θ : ℝ, |r| < δ →
      rootProfileShift r₀ ι (r, θ) ∈ annularOpen D ∧
      ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (r, θ) ∧
      0 < extendedRootOddCoefficient G (r, θ) ∧
      0 < planeJacobian (extendedRootEvenOddChart G) (r, θ) ∧
      0 < angularPartial (extendedRootEven G) (r, θ) ∧
      0 < rootAngularProduct G (r, θ) ∧
      ContDiffAt ℝ ∞ (rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G) (r, θ) ∧
      0 < rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G (r, θ) ∧
      rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G (r, θ) ^ 2 *
        rootHeightFactor (n04bRootLeadingCoefficient L z r₀ ι) G (r, θ) = 1 := by
  obtain ⟨δ₁, hδ₁, hgeometry⟩ := H.exists_uniform_positive_geometry
  have hshift : Continuous (fun r : ℝ => r₀ + ι * r) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), r₀ + ι * r ∈ Ioo D.a D.b :=
    hshift.continuousAt.tendsto.eventually
      (by simpa only [mul_zero, add_zero] using isOpen_Ioo.mem_nhds hr₀)
  obtain ⟨δ₂, hδ₂, hphysical⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min δ₁ δ₂, lt_min_iff.mpr ⟨hδ₁, hδ₂⟩, ?_⟩
  intro r θ hr
  have hp : rootProfileShift r₀ ι (r, θ) ∈ annularOpen D := by
    refine ⟨hphysical ?_, mem_univ _⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      hr.trans_le (min_le_right δ₁ δ₂)
  have hg := hgeometry r θ (hr.trans_le (min_le_left _ _))
  have ha := n04b_rootLeadingCoefficient_regularity hfield hz hs hp
  have hfactor :
      0 < rootHeightFactor (n04bRootLeadingCoefficient L z r₀ ι) G (r, θ) :=
    div_pos (mul_pos ha.2 hg.2.2.1) hg.2.2.2.2
  have hheight :
      ContDiffAt ℝ ∞ (rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G) (r, θ) :=
    contDiffAt_rootSmoothHeight H.smooth Real.pi_ne_zero
      (fun r _ => H.odd_period r) (fun r _ => H.even_period r)
      ha.1 hg.2.1.ne' hg.2.2.2.2.ne' hfactor
  refine ⟨hp, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2,
    hheight, inv_pos.mpr (Real.sqrt_pos.mpr hfactor), ?_⟩
  rw [rootSmoothHeight, inv_pow, Real.sq_sqrt hfactor.le]
  exact inv_mul_cancel₀ hfactor.ne'

end ContinuousFlexibility.Analysis
