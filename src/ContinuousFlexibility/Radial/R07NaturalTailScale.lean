module

public import ContinuousFlexibility.Statements.RadialTargets
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Positive scalar invariance of the actual natural tail

Multiplication of the physical coefficient by a positive constant multiplies
the Jacobi expression and its weighted measure by that constant.  Thus it
leaves the actual smooth, nonzero natural solution space unchanged.  These
identities require only the coefficient equality on the open tail; no choice
of a solution or a boundary line is incorporated into their hypotheses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

/-- The Jacobi expression is exactly linear under a constant rescaling of
its physical coefficient, without auxiliary differentiability hypotheses. -/
theorem radialJacobi_const_mul_profile (a scale : ℝ) (w u : ℝ → ℝ) (r : ℝ) :
    radialJacobi a (fun x => scale * w x) u r = scale * radialJacobi a w u r := by
  have hp : (fun x => (scale * w x) * deriv u x) =
      (fun x => scale * (w x * deriv u x)) := by
    funext x
    ring
  unfold radialJacobi
  dsimp only
  rw [hp, deriv_const_mul_field, deriv_const_mul_field]
  ring

theorem radialJacobi_profile_congr_germ {w v : ℝ → ℝ} {r : ℝ}
    (h : w =ᶠ[𝓝 r] v) (a : ℝ) (u : ℝ → ℝ) :
    radialJacobi a w u r = radialJacobi a v u r := by
  have hp : (fun x => w x * deriv u x) =ᶠ[𝓝 r] fun x => v x * deriv u x := by
    filter_upwards [h] with x hx
    rw [hx]
  simp only [radialJacobi, hp.deriv_eq, h.deriv_eq]

theorem radialJacobi_profile_scale_germ {w v : ℝ → ℝ} {r scale : ℝ}
    (h : v =ᶠ[𝓝 r] fun x => scale * w x) (a : ℝ) (u : ℝ → ℝ) :
    radialJacobi a v u r = scale * radialJacobi a w u r :=
  (radialJacobi_profile_congr_germ h a u).trans (radialJacobi_const_mul_profile a scale w u r)

/-- Constant coefficient scaling preserves the homogeneous equation on any
open interval or open set. -/
theorem radialHomogeneousOn_profile_scale_iff {D E : Statements.ReferenceData}
    {J : Set ℝ} (hJ : IsOpen J) {scale : ℝ} (hs : scale ≠ 0)
    (hw : EqOn E.w (fun r => scale * D.w r) J) (j : ℕ) (u : ℝ → ℝ) :
    Statements.RadialHomogeneousOn E j J u ↔ Statements.RadialHomogeneousOn D j J u := by
  have heq (r : ℝ) (hr : r ∈ J) :
      radialJacobi ((j : ℝ) ^ 2) E.w u r = scale * radialJacobi ((j : ℝ) ^ 2) D.w u r := by
    apply radialJacobi_profile_scale_germ
    filter_upwards [hJ.mem_nhds hr] with x hx
    exact hw hx
  constructor
  · rintro ⟨hu, hode⟩
    refine ⟨hu, fun r hr => ?_⟩
    have hz : scale * radialJacobi ((j : ℝ) ^ 2) D.w u r = 0 :=
      (heq r hr).symm.trans (hode r hr)
    exact (mul_eq_zero.mp hz).resolve_left hs
  · rintro ⟨hu, hode⟩
    refine ⟨hu, fun r hr => ?_⟩
    rw [heq r hr, hode r hr, mul_zero]

/-- The weighted radial measure, restricted to a measurable region where
the coefficient is scaled, has exactly the same scalar scaling. -/
theorem radialHilbertMeasure_restrict_scale {D E : Statements.ReferenceData}
    {s : Set ℝ} (hs : MeasurableSet s)
    (hcore : Statements.radialCore E = Statements.radialCore D)
    {scale : ℝ} (hscale : 0 ≤ scale) (hw : EqOn E.w (fun r => scale * D.w r) s) :
    (Statements.radialHilbertMeasure E).restrict s =
      ENNReal.ofReal scale • (Statements.radialHilbertMeasure D).restrict s := by
  rw [Statements.radialHilbertMeasure, Statements.radialHilbertMeasure,
    restrict_withDensity hs, restrict_withDensity hs, hcore]
  let μ : Measure ℝ := (volume.restrict (Statements.radialCore D)).restrict s
  change μ.withDensity (fun r => ENNReal.ofReal (12 * E.w r / r ^ 2)) =
    ENNReal.ofReal scale • μ.withDensity (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2))
  calc
    _ = μ.withDensity (ENNReal.ofReal scale •
        (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2))) := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hs] with r hr
      simp only [Pi.smul_apply, smul_eq_mul, hw hr]
      rw [show 12 * (scale * D.w r) / r ^ 2 = scale * (12 * D.w r / r ^ 2) by ring,
        ENNReal.ofReal_mul hscale]
    _ = _ := withDensity_smul' _ _ ENNReal.ofReal_ne_top

theorem memLp_radialHilbertMeasure_restrict_scale_iff {D E : Statements.ReferenceData}
    {s : Set ℝ} (hs : MeasurableSet s)
    (hcore : Statements.radialCore E = Statements.radialCore D)
    {scale : ℝ} (hscale : 0 < scale) (hw : EqOn E.w (fun r => scale * D.w r) s)
    (u : ℝ → ℝ) (p : ℝ≥0∞) :
    MemLp u p ((Statements.radialHilbertMeasure E).restrict s) ↔
      MemLp u p ((Statements.radialHilbertMeasure D).restrict s) := by
  have hforward := radialHilbertMeasure_restrict_scale hs hcore hscale.le hw
  have hwinv : EqOn D.w (fun r => scale⁻¹ * E.w r) s := by
    intro r hr
    dsimp only
    rw [hw hr, ← mul_assoc, inv_mul_cancel₀ hscale.ne', one_mul]
  have hreverse := radialHilbertMeasure_restrict_scale hs hcore.symm
    (inv_pos.mpr hscale).le hwinv
  constructor
  · intro hu
    rw [hreverse]
    exact hu.smul_measure ENNReal.ofReal_ne_top
  · intro hu
    rw [hforward]
    exact hu.smul_measure ENNReal.ofReal_ne_top

/-- Positive coefficient scaling on the same geometric tail preserves
exactly the predicate defining the actual natural solution space. -/
theorem radialNaturalTail_scale_iff {D E : Statements.ReferenceData}
    (ha : E.a = D.a) (hb : E.b = D.b) {right : Bool} {entry scale : ℝ}
    (hscale : 0 < scale)
    (hw : EqOn E.w (fun r => scale * D.w r) (Statements.radialTailInterval D right entry))
    (j : ℕ) (u : ℝ → ℝ) :
    Statements.RadialNaturalTail E right j entry u ↔ Statements.RadialNaturalTail D right j entry u := by
  have hcore : Statements.radialCore E = Statements.radialCore D := by
    simp only [Statements.radialCore, ha, hb]
  have htail : Statements.radialTailInterval E right entry =
      Statements.radialTailInterval D right entry := by
    cases right <;> simp only [Statements.radialTailInterval, Bool.false_eq_true, if_false, if_true, ha, hb]
  have hopen : IsOpen (Statements.radialTailInterval D right entry) := by
    cases right <;> exact isOpen_Ioo
  have hhom := radialHomogeneousOn_profile_scale_iff hopen hscale.ne' hw j u
  have hmem := memLp_radialHilbertMeasure_restrict_scale_iff hopen.measurableSet hcore hscale hw u 2
  unfold Statements.RadialNaturalTail
  rw [htail, hhom, hmem]

end ContinuousFlexibility.Radial
