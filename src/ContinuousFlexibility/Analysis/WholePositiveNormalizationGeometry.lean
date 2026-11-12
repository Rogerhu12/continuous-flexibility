import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer
import ContinuousFlexibility.Analysis.WholePositiveCanonicalFields

/-!
# Normalization on the actual middle of each positive component

Disjointness of the genuine positive components puts every normalization
point in its own buffer. The already constructed middle germs then give
the same chart and height for any two members of the family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem N04PositiveNormalizationBuffer.mem_middle_of_mem_region
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (hf : Continuous f)
    (i : N04PositiveComponent a b f) {r : ℝ}
    (hi : r ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i))
    (hr : r ∈ B.region) : r ∈ Icc (B.centerLeft i) (B.centerRight i) := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hr
  have ho := B.ordered j
  have hrj : r ∈ Ioo (n04PositiveLeft j) (n04PositiveRight j) :=
    ⟨(ho.1.trans ho.2.1).trans hj.1,
      hj.2.trans (ho.2.2.2.1.trans ho.2.2.2.2)⟩
  have hij : i = j := by
    by_contra hne
    exact Set.disjoint_left.mp
      (n04PositiveComponent_interval_pairwiseDisjoint hf hne) hi hrj
  subst j
  exact ⟨(ho.2.1.trans hj.1).le, (hj.2.trans ho.2.2.2.1).le⟩

theorem N04PositiveNormalizationBuffer.chart_height_normalization
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (hf : Continuous f)
    (i : N04PositiveComponent a b f)
    {F G F₀ G₀ : PolarPoint → PolarPoint} {h h₀ : PolarPoint → ℝ}
    (H : WholePositiveChartGeometry F G h
      (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i))
    (H₀ : WholePositiveChartGeometry F₀ G₀ h₀
      (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i))
    {p : PolarPoint}
    (hp : p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ))
    (hn : p.1 ∈ B.region) : F p = F₀ p ∧ h p = h₀ p := by
  have hm := B.mem_middle_of_mem_region hf i hp.1 hn
  have hnow := H.normalization_on_middle hm
  have href := H₀.normalization_on_middle hm
  exact ⟨hnow.1.trans href.1.symm, hnow.2.2.trans href.2.2.symm⟩

end ContinuousFlexibility.Analysis
