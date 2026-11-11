import ContinuousFlexibility.Radial.TerminalCapLift
import ContinuousFlexibility.Radial.ModeSmoothWeakEquation
import ContinuousFlexibility.Radial.ModeRegionWeakEquation
import ContinuousFlexibility.Radial.MatchingTraceCalculus

/-!
# Actual regional terminal lifts

The cutoff lift is placed in the radial Hilbert space and restricted to
the inner interval. Its representative retains the two boundary traces
and is identically zero outside that interval. The actual commutator
source gives the frozen weak equation, with its scalar component zero.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem terminalCapLift_memLp {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (lam : ℝ) {χ u : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    MemLp (terminalCapLift lam χ u) 2 (radialHilbertMeasure D) := by
  have hc := (terminalCapLift_smooth lam hχ hu).continuous
  exact matching_memLp_of_continuousOn hD hc.measurable hc.continuousOn 2

def terminalCapVector {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (lam : ℝ) {χ u : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    RadialModeL2 D :=
  (terminalCapLift_memLp hD lam hχ hu).toLp (terminalCapLift lam χ u)

theorem terminalCapVector_coe {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (lam : ℝ) {χ u : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    (terminalCapVector hD lam hχ hu : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      terminalCapLift lam χ u :=
  MemLp.coeFn_toLp _

def terminalCapInnerLift {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (l h lam : ℝ) {χ u : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    RadialModePair D :=
  modeInnerSource D l h (terminalCapVector hD lam hχ hu, 0)

def terminalCapInnerSource {D : ReferenceData} (l h lam : ℝ) (χ u : ℝ → ℝ)
    (hf : MemLp (terminalCapHilbertSource lam D.w χ u) 2 (radialHilbertMeasure D)) :
    RadialModePair D :=
  modeInnerSource D l h (hf.toLp (terminalCapHilbertSource lam D.w χ u), 0)

theorem terminalCapInnerLift_ae {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (l h lam : ℝ) {χ u : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    ((terminalCapInnerLift hD l h lam hχ hu).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      modeInnerExtension l h (terminalCapLift lam χ u) :=
  modeInnerSource_extension_ae hD l h _ (terminalCapVector_coe hD lam hχ hu)

theorem terminalCapInnerLift_zero_outside {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (l h lam : ℝ)
    {χ u : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    ((terminalCapInnerLift hD l h lam hχ hu).1 : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (Ioo l h)ᶜ] (fun _ => 0) :=
  modeInnerSource_zero_outside D l h _

theorem terminalCapInnerLift_representative_smooth (l h lam : ℝ)
    {χ u : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    ContDiffOn ℝ ∞ (modeInnerExtension l h (terminalCapLift lam χ u)) (Icc l h) :=
  modeInnerExtension_contDiffOn (terminalCapLift_smooth lam hχ hu).contDiffOn

/-- Homogeneity is only required where the cutoff is nonzero inside the
retained interval, so no extension of the stand-in equation is assumed. -/
theorem terminalCapInnerLift_equation {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {l h lam : ℝ} {j : ℕ} {χ u : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hcore : Ioo l h ⊆ radialCore D)
    (heq : ∀ r ∈ Ioo l h, r ∈ Function.support χ →
      radialJacobi ((j : ℝ) ^ 2) D.w u r = 0)
    (hf : MemLp (terminalCapHilbertSource lam D.w χ u) 2 (radialHilbertMeasure D)) :
    ModeLocalEquation D j (Ioo l h) (terminalCapInnerLift hD l h lam hχ hu)
      (terminalCapInnerSource l h lam χ u hf) := by
  unfold terminalCapInnerLift terminalCapInnerSource
  apply modeLocalEquation_modeInnerRestriction hD
  apply modeLocalEquation_of_smooth_pointwise hD (terminalCapLift_smooth lam hχ hu)
    (terminalCapVector_coe hD lam hχ hu) (MemLp.coeFn_toLp hf) rfl
  intro r hr
  have hg := matchingProfileGeometry hD
  have hrad : r ≠ 0 := (lt_trans hg.1 (hcore hr).1).ne'
  have hw : D.w r ≠ 0 := (hg.2.2.2.2.1 r (hcore hr)).ne'
  have hρ := terminalCapHilbertSource_density (lam := lam) (χ := χ) (u := u) hrad hw
  rw [terminalCapLift_jacobi ((j : ℝ) ^ 2) lam r hg.2.2.1.1 hχ hu]
  by_cases hz : χ r = 0
  · rw [hz, zero_mul, zero_div, zero_sub]
    linarith only [hρ]
  · rw [heq r hr hz, mul_zero, zero_div, zero_sub]
    linarith only [hρ]

theorem terminalCapInnerSource_norm_le {D : ReferenceData} (l h lam : ℝ)
    (χ u : ℝ → ℝ)
    (hf : MemLp (terminalCapHilbertSource lam D.w χ u) 2 (radialHilbertMeasure D)) :
    ‖(terminalCapInnerSource l h lam χ u hf).1‖ ≤
      ‖hf.toLp (terminalCapHilbertSource lam D.w χ u)‖ :=
  modeRegionVector_norm_le D (Ioo l h) measurableSet_Ioo _

/-- The retained representative has the exact actual inward derivative
at either regular cut, despite its zero extension on the other side. -/
theorem terminalCapInnerLift_derivWithin {l h r lam : ℝ}
    (hlh : l < h) (hr : r ∈ Icc l h)
    {χ u : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hnear : χ =ᶠ[𝓝 r] fun _ => (1 : ℝ)) :
    derivWithin (modeInnerExtension l h (terminalCapLift lam χ u)) (Icc l h) r =
      deriv u r / sqrt lam := by
  rw [derivWithin_congr (modeInnerExtension_eqOn l h _)
    (modeInnerExtension_eqOn l h _ hr)]
  rw [((terminalCapLift_smooth lam hχ hu).differentiable (by simp) r).derivWithin
    ((uniqueDiffOn_Icc hlh).uniqueDiffWithinAt hr)]
  exact terminalCapLift_deriv_eq hnear

theorem terminalCapInnerLift_normalized_value {l h r lam : ℝ}
    (hr : r ∈ Icc l h) (hlam : 0 < lam) {χ u : ℝ → ℝ}
    (hχ : χ r = 1) (hu : u r = 1) :
    sqrt lam * modeInnerExtension l h (terminalCapLift lam χ u) r = 1 := by
  rw [modeInnerExtension_eqOn l h _ hr]
  exact terminalCapLift_normalized_trace hlam hχ hu

end ContinuousFlexibility.Radial
