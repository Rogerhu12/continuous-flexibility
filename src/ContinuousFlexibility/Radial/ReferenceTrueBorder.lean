import ContinuousFlexibility.Radial.CentralTrueBorder
import ContinuousFlexibility.Statements.RadialTargets

/-!
# Installing the true border on the same reference geometry

The profile, its kernel and every cell and localizer are retained exactly.
Only the compact metric control and the left endpoint cutoff are installed.
Thus a central patch in the geometry delivered by R08 already suffices for
the actual normalized border, independently of the construction of an inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

/-- A smooth cutoff equal to one near the left endpoint and zero near the right. -/
def referenceLeftCutoff (a b r : ℝ) : ℝ :=
  1 - smoothTransition ((r - (a + (b - a) / 4)) / ((b - a) / 4))

theorem contDiff_referenceLeftCutoff (a b : ℝ) :
    ContDiff ℝ ∞ (referenceLeftCutoff a b) :=
  contDiff_const.sub (smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _))

theorem referenceLeftCutoff_eq_one {a b r : ℝ} (hab : a < b)
    (hr : r ≤ a + (b - a) / 4) : referenceLeftCutoff a b r = 1 := by
  have hwidth : 0 < (b - a) / 4 := by linarith
  have harg : (r - (a + (b - a) / 4)) / ((b - a) / 4) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hwidth.le
  rw [referenceLeftCutoff, smoothTransition.zero_of_nonpos harg, sub_zero]

theorem referenceLeftCutoff_eq_zero {a b r : ℝ} (hab : a < b)
    (hr : b - (b - a) / 4 ≤ r) : referenceLeftCutoff a b r = 0 := by
  have hwidth : 0 < (b - a) / 4 := by linarith
  have harg : 1 ≤ (r - (a + (b - a) / 4)) / ((b - a) / 4) := by
    apply (le_div_iff₀ hwidth).mpr
    linarith
  rw [referenceLeftCutoff, smoothTransition.one_of_one_le harg, sub_self]

theorem referenceLeftCutoff_endpoint_germs {a b : ℝ} (hab : a < b) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ r ∈ Ioo a (a + ε), referenceLeftCutoff a b r = 1) ∧
      (∀ r ∈ Ioo (b - ε) b, referenceLeftCutoff a b r = 0) := by
  refine ⟨(b - a) / 4, by linarith, ?_, ?_⟩
  · intro r hr
    exact referenceLeftCutoff_eq_one hab hr.2.le
  · intro r hr
    exact referenceLeftCutoff_eq_zero hab hr.1.le

/-- Updating the controls keeps the actual radial geometry unchanged. -/
def referenceWithTrueBorderControls (D : ReferenceData) (χ : ℝ → ℝ) : ReferenceData :=
  { D with chi := χ, chiLeft := referenceLeftCutoff D.a D.b }

theorem referenceWithTrueBorderControls_fields (D : ReferenceData) (χ : ℝ → ℝ) :
    (referenceWithTrueBorderControls D χ).a = D.a ∧
      (referenceWithTrueBorderControls D χ).b = D.b ∧
      (referenceWithTrueBorderControls D χ).w = D.w ∧
      (referenceWithTrueBorderControls D χ).phi = D.phi ∧
      (referenceWithTrueBorderControls D χ).cells = D.cells ∧
      (referenceWithTrueBorderControls D χ).localizer = D.localizer ∧
      (referenceWithTrueBorderControls D χ).cellIndex = D.cellIndex :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem referenceWithTrueBorderControls_column (D : ReferenceData) (χ : ℝ → ℝ) :
    referenceColumn (referenceWithTrueBorderControls D χ) =
      fun r => radialJacobi 4 (fun t => D.w t * χ t) D.phi r := rfl

theorem referenceWithTrueBorderControls_accumulating_iff (D : ReferenceData) (χ : ℝ → ℝ) :
    IsAccumulatingProfile (referenceWithTrueBorderControls D χ) ↔ IsAccumulatingProfile D :=
  Iff.rfl

theorem referenceWithTrueBorderControls_centralPatch_iff
    (D : ReferenceData) (χ : ℝ → ℝ) (l h : ℝ) :
    CentralPatch (referenceWithTrueBorderControls D χ) l h ↔ CentralPatch D l h :=
  Iff.rfl

/-- An accumulating reference with a genuine central patch admits a true
border without changing any of its profile or partition data. -/
theorem exists_reference_true_border_controls {D : ReferenceData} {l h : ℝ}
    (hacc : IsAccumulatingProfile D) (hpatch : CentralPatch D l h) :
    ∃ χ : ℝ → ℝ,
      IsAccumulatingProfile (referenceWithTrueBorderControls D χ) ∧
      CentralPatch (referenceWithTrueBorderControls D χ) l h ∧
      RadialTrueBorder (referenceWithTrueBorderControls D χ) ∧
      tsupport χ ⊆ Ioo (centralRadius (sqrt centralOscillatorA)) h ∧
      ContDiff ℝ ∞ (referenceColumn (referenceWithTrueBorderControls D χ)) ∧
      HasCompactSupport (referenceColumn (referenceWithTrueBorderControls D χ)) ∧
      tsupport (referenceColumn (referenceWithTrueBorderControls D χ)) ⊆
        Ioo (centralRadius (sqrt centralOscillatorA)) h := by
  have hgeom : RadialProfileGeometry D := hacc.choose_spec.1
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hφ : ContDiff ℝ ∞ D.phi := hgeom.2.2.2.1.1
  have hpatch' := hpatch
  rcases hpatch' with ⟨hal, hlturn, hturnh, hhb, scale, amplitude,
    hscale, hamplitude, hwmodel, hφmodel⟩
  have hlright : l < centralRadius (sqrt centralOscillatorA) :=
    hlturn.trans central_turning_radii_pos_ordered.2
  have haright : D.a < centralRadius (sqrt centralOscillatorA) := hal.trans hlright
  have hwcap : EqOn D.w (centralRadialProfile scale)
      (Ioo (centralRadius (sqrt centralOscillatorA)) h) := by
    intro r hr
    exact hwmodel r ⟨hlright.trans hr.1, hr.2⟩
  have hφcap : EqOn D.phi (fun r => amplitude * centralKernelHeight r)
      (Ioo (centralRadius (sqrt centralOscillatorA)) h) := by
    intro r hr
    exact hφmodel r ⟨hlright.trans hr.1, hr.2⟩
  obtain ⟨χ, hχsmooth, hχcompact, hχcap, _, hχsign, hgsmooth, hgcompact, hgcap,
      _, hpair⟩ :=
    exists_central_true_border hw hφ hscale hamplitude haright hturnh hhb le_rfl hwcap hφcap
  have hborder : RadialTrueBorder (referenceWithTrueBorderControls D χ) := by
    refine ⟨hχsmooth, hχcompact, ?_, hpair,
      contDiff_referenceLeftCutoff D.a D.b,
      referenceLeftCutoff_endpoint_germs hgeom.2.1⟩
    intro r hr
    have hrclosed : r ∈ tsupport χ := hr
    have hrinterval := hχcap hrclosed
    exact ⟨⟨haright.trans hrinterval.1, hrinterval.2.trans hhb⟩,
      (hχsign r hrclosed).1⟩
  refine ⟨χ, ?_, ?_, hborder, hχcap, ?_, ?_, ?_⟩
  · exact (referenceWithTrueBorderControls_accumulating_iff D χ).mpr hacc
  · exact (referenceWithTrueBorderControls_centralPatch_iff D χ l h).mpr hpatch
  · rw [referenceWithTrueBorderControls_column]
    exact hgsmooth
  · rw [referenceWithTrueBorderControls_column]
    exact hgcompact
  · rw [referenceWithTrueBorderControls_column]
    exact hgcap

/-- The same-geometry version makes every retained data field explicit. -/
theorem exists_reference_true_border {D : ReferenceData} {l h : ℝ}
    (hacc : IsAccumulatingProfile D) (hpatch : CentralPatch D l h) :
    ∃ D' : ReferenceData,
      D'.a = D.a ∧ D'.b = D.b ∧ D'.w = D.w ∧ D'.phi = D.phi ∧
      D'.cells = D.cells ∧ D'.localizer = D.localizer ∧ D'.cellIndex = D.cellIndex ∧
      IsAccumulatingProfile D' ∧ CentralPatch D' l h ∧ RadialTrueBorder D' ∧
      ContDiff ℝ ∞ (referenceColumn D') ∧ HasCompactSupport (referenceColumn D') ∧
      tsupport (referenceColumn D') ⊆ Ioo (centralRadius (sqrt centralOscillatorA)) h := by
  obtain ⟨χ, hacc', hpatch', hborder, _, hgsmooth, hgcompact, hgcap⟩ :=
    exists_reference_true_border_controls hacc hpatch
  exact ⟨referenceWithTrueBorderControls D χ, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    hacc', hpatch', hborder, hgsmooth, hgcompact, hgcap⟩

end ContinuousFlexibility.Radial
