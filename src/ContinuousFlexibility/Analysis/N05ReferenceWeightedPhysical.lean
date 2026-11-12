import ContinuousFlexibility.Radial.ReferenceWeightedMeasure
import ContinuousFlexibility.Radial.ReferenceGraphNorms

/-!
# Positive reference weights control actual physical L² limits

This uses the genuine cell partition and the existing exponential weight
embedding. It applies to all fields, including odd angular derivatives,
without imposing source compatibility or output parity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

theorem n05_referenceWeighted_physical_square_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : PolarPoint → ℝ,
      MemLp f 2 (referenceWeightedMeasure D γ M) →
      MemLp f 2 (radialPhysicalMeasure D) ∧
        (∫ x, f x ^ 2 ∂radialPhysicalMeasure D) ≤
          C * ∫ x, f x ^ 2 ∂referenceWeightedMeasure D γ M := by
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hpart : RadialPartition D := hD.choose_spec.2.1
  obtain ⟨C, hC, hbound⟩ := r11b_cell_weighted_L2_bound hpart hab (2 * M) γ hγ
  refine ⟨C, hC, fun f hf => ?_⟩
  obtain ⟨hl, hs⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hf
  obtain ⟨hp, hb⟩ := hbound f hl hs
  refine ⟨hp, ?_⟩
  rw [integral_sq_referenceWeightedMeasure_eq hab hpart hl hs]
  exact hb

theorem n05_referenceWeighted_tendsto_physical_sq {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {f : ℕ → PolarPoint → ℝ} {g : PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (referenceWeightedMeasure D γ M))
    (hg : MemLp g 2 (referenceWeightedMeasure D γ M))
    (hlim : Tendsto (fun n => ∫ x, (f n x - g x) ^ 2
      ∂referenceWeightedMeasure D γ M) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (f n x - g x) ^ 2 ∂radialPhysicalMeasure D)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := n05_referenceWeighted_physical_square_bound hD hγ M
  apply squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _))
    (fun n => (hbound (fun x => f n x - g x) ((hf n).sub hg)).2)
  simpa only [mul_zero] using hlim.const_mul C

theorem n05_referenceWeighted_tendsto_physical {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {f : ℕ → PolarPoint → ℝ} {g : PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (referenceWeightedMeasure D γ M))
    (hg : MemLp g 2 (referenceWeightedMeasure D γ M))
    (hlim : Tendsto (fun n => ∫ x, (f n x - g x) ^ 2
      ∂referenceWeightedMeasure D γ M) atTop (𝓝 0)) :
    ∃ hfp : ∀ n, MemLp (f n) 2 (radialPhysicalMeasure D),
      ∃ hgp : MemLp g 2 (radialPhysicalMeasure D),
        Tendsto (fun n => (hfp n).toLp (f n)) atTop (𝓝 (hgp.toLp g)) := by
  obtain ⟨_, _, hbound⟩ := n05_referenceWeighted_physical_square_bound hD hγ M
  let hfp (n : ℕ) : MemLp (f n) 2 (radialPhysicalMeasure D) := (hbound (f n) (hf n)).1
  let hgp : MemLp g 2 (radialPhysicalMeasure D) := (hbound g hg).1
  exact ⟨hfp, hgp, reference_memLp_tendsto_of_sub_sq hfp hgp
    (n05_referenceWeighted_tendsto_physical_sq hD hγ hf hg hlim)⟩

end ContinuousFlexibility.Radial
