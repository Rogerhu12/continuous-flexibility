import ContinuousFlexibility.Analysis.N06BoundaryRadialJets
import ContinuousFlexibility.Analysis.N06CharacteristicRootJets
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Higher boundary jets of the actual characteristic-root construction

The output of the genuine root-flow construction supplies all finite
boundary derivatives, not only its displayed first jets. These derivatives
are smooth angular functions of the actual normalized physical chart and
of the actual logarithmic height. They can therefore be used directly in
the relative order-four / order-three Taylor patches.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (P : N04bRootCoordinateProperties d c₀ β Φ R σ G)

include P

theorem n06_physicalChart_contDiffAt_boundary (r ι v τ θ : ℝ) :
    ContDiffAt ℝ ∞ (n06NormalizedPhysicalRootChart G r ι v τ) (r, θ) := by
  have hsource : ContDiffAt ℝ ∞ (extendedRootEvenOddChart G)
      (n06RootPhysicalInput r ι (r, θ)) := by
    simpa only [n06RootPhysicalInput_boundary] using P.n06_chart_contDiffAt_zero θ
  have hcomp : ContDiffAt ℝ ∞
      (fun p => extendedRootEvenOddChart G (n06RootPhysicalInput r ι p)) (r, θ) :=
    hsource.comp (r, θ) (contDiff_n06RootPhysicalInput r ι).contDiffAt
  exact (contDiffAt_const.add (contDiffAt_const.mul hcomp.fst)).prodMk hcomp.snd

theorem n06_physicalHeight_contDiffAt_boundary {a : PolarPoint → ℝ}
    {θ : ℝ} (ha : ContDiffAt ℝ ∞ a (0, θ)) (ha0 : 0 < a (0, θ)) (r ι : ℝ) :
    ContDiffAt ℝ ∞ (n06PhysicalRootHeight a G r ι) (r, θ) ∧
      0 < n06PhysicalRootHeight a G r ι (r, θ) := by
  have hh := P.height_boundary θ ha ha0
  have hsource : ContDiffAt ℝ ∞ (rootSmoothHeight a G)
      (n06RootPhysicalInput r ι (r, θ)) := by
    simpa only [n06RootPhysicalInput_boundary] using hh.2.1
  refine ⟨hsource.comp (r, θ) (contDiff_n06RootPhysicalInput r ι).contDiffAt, ?_⟩
  simpa only [n06PhysicalRootHeight, n06RootPhysicalInput_boundary] using hh.2.2.1

/-- Both coordinate components of the true root chart supply angularly
smooth radial boundary jets of every finite order. -/
theorem n06_physicalChart_boundaryJets_smooth (r ι v τ : ℝ) (n : ℕ) :
    ContDiff ℝ ∞
        (radialBoundaryJet (fun p => (n06NormalizedPhysicalRootChart G r ι v τ p).1) r n) ∧
      ContDiff ℝ ∞
        (radialBoundaryJet (fun p => (n06NormalizedPhysicalRootChart G r ι v τ p).2) r n) :=
  ⟨n06_contDiff_radialBoundaryJet_of_axis
      (fun θ => (P.n06_physicalChart_contDiffAt_boundary r ι v τ θ).fst) n,
    n06_contDiff_radialBoundaryJet_of_axis
      (fun θ => (P.n06_physicalChart_contDiffAt_boundary r ι v τ θ).snd) n⟩

/-- The genuine positive root height supplies the logarithmic boundary
data through order three, and in fact at every finite order. -/
theorem n06_physicalLogHeight_boundaryJets_smooth {a : PolarPoint → ℝ}
    (ha : ∀ θ, ContDiffAt ℝ ∞ a (0, θ)) (ha0 : ∀ θ, 0 < a (0, θ))
    (r ι : ℝ) (n : ℕ) :
    ContDiff ℝ ∞
      (radialBoundaryJet (fun p => Real.log (n06PhysicalRootHeight a G r ι p)) r n) := by
  apply n06_contDiff_radialBoundaryJet_of_axis
  intro θ
  have hh := P.n06_physicalHeight_contDiffAt_boundary (ha θ) (ha0 θ) r ι
  exact hh.1.log hh.2.ne'

end N04bRootCoordinateProperties

end ContinuousFlexibility.Analysis
