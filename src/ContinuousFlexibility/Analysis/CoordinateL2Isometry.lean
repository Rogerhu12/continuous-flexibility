import Mathlib.MeasureTheory.Function.L2Space

/-!
# L2 isometry for an actual coordinate embedding

Pullback by a measurable embedding is a surjective L2 isometry onto the
original measure space when a left inverse of the coordinate map is given.
The physical measure is the actual pushforward measure.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory

set_option backward.isDefEq.respectTransparency false

def coordinateL2Pullback (μ : Measure ℝ) (R : ℝ → ℝ) (hR : MeasurableEmbedding R) :
    Lp ℝ 2 (Measure.map R μ) →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ R ⟨hR.measurable, rfl⟩

theorem coordinateL2Pullback_ae (μ : Measure ℝ) (R : ℝ → ℝ) (hR : MeasurableEmbedding R)
    (f : Lp ℝ 2 (Measure.map R μ)) :
    coordinateL2Pullback μ R hR f =ᵐ[μ] fun x => f (R x) :=
  Lp.coeFn_compMeasurePreserving f ⟨hR.measurable, rfl⟩

theorem coordinateL2Pullback_surjective (μ : Measure ℝ) (R X : ℝ → ℝ)
    (hR : MeasurableEmbedding R) (hX : Function.LeftInverse X R) :
    Function.Surjective (coordinateL2Pullback μ R hR) := by
  intro f
  let g : ℝ → ℝ := fun r => f (X r)
  have hcomp : g ∘ R = f := by
    funext x
    simp only [Function.comp_apply, g, hX x]
  have hg : MemLp g 2 (Measure.map R μ) := by
    apply hR.memLp_map_measure_iff.mpr
    rw [hcomp]
    exact Lp.memLp f
  refine ⟨hg.toLp g, ?_⟩
  apply Lp.ext
  filter_upwards [coordinateL2Pullback_ae μ R hR (hg.toLp g),
    ae_eq_comp hR.measurable.aemeasurable hg.coeFn_toLp] with x hx hgx
  exact hx.trans (hgx.trans (congrFun hcomp x))

def coordinateL2Equiv (μ : Measure ℝ) (R X : ℝ → ℝ)
    (hR : MeasurableEmbedding R) (hX : Function.LeftInverse X R) :
    Lp ℝ 2 (Measure.map R μ) ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (coordinateL2Pullback μ R hR)
    (coordinateL2Pullback_surjective μ R X hR hX)

theorem coordinateL2Equiv_ae (μ : Measure ℝ) (R X : ℝ → ℝ)
    (hR : MeasurableEmbedding R) (hX : Function.LeftInverse X R)
    (f : Lp ℝ 2 (Measure.map R μ)) :
    coordinateL2Equiv μ R X hR hX f =ᵐ[μ] fun x => f (R x) :=
  coordinateL2Pullback_ae μ R hR f

end ContinuousFlexibility.Analysis
