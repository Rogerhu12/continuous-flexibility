import ContinuousFlexibility.Analysis.N07aClosedNormalTransmission
import ContinuousFlexibility.Analysis.N07aClosedSmoothGluing

/-!
# Smooth local gluing from the common noncharacteristic equation

The transmission theorem determines the genuine closed jets. Restriction
to an open angular interval preserves these derivatives by uniqueness,
so the two closed radial halves glue smoothly on the entire open rectangle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n07a_closedRectangle_normalTransmission_smooth_gluing
    {l c r a b : ℝ} (hlc : l < c) (hcr : c < r) (hab : a < b)
    {A : Fin 6 → PolarPoint → ℝ} {u v f : PolarPoint → ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (Ioo l r ×ˢ Ioo a b))
    (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ Ioo a b))
    (hu : ContDiffOn ℝ ∞ u (Icc l c ×ˢ Icc a b))
    (hv : ContDiffOn ℝ ∞ v (Icc c r ×ˢ Icc a b))
    (hequ : EqOn (mixedDerivative 2 0 u) (n07aNormalRhs A u f)
      (Ioo l c ×ˢ Ioo a b))
    (heqv : EqOn (mixedDerivative 2 0 v) (n07aNormalRhs A v f)
      (Ioo c r ×ˢ Ioo a b))
    (hvalue : ∀ θ ∈ Ioo a b, u (c, θ) = v (c, θ))
    (hfirst : ∀ θ ∈ Ioo a b,
      fderivWithin ℝ u (Icc l c ×ˢ Icc a b) (c, θ) =
        fderivWithin ℝ v (Icc c r ×ˢ Icc a b) (c, θ)) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint => if p.1 ≤ c then u p else v p)
      (Ioo l r ×ˢ Ioo a b) := by
  have hangular : UniqueDiffOn ℝ (Ioo a b) := isOpen_Ioo.uniqueDiffOn
  have hsubL : Icc l c ×ˢ Ioo a b ⊆ Icc l c ×ˢ Icc a b :=
    Set.prod_mono Subset.rfl Ioo_subset_Icc_self
  have hsubR : Icc c r ×ˢ Ioo a b ⊆ Icc c r ×ˢ Icc a b :=
    Set.prod_mono Subset.rfl Ioo_subset_Icc_self
  have hmatch := n07a_closedRectangle_normalTransmission_matching_jets
    hlc hcr hab hA hf hu hv hequ heqv hvalue hfirst
  have hjets : ∀ n : ℕ, ∀ θ ∈ Ioo a b,
      iteratedFDerivWithin ℝ n u (Icc l c ×ˢ Ioo a b) (c, θ) =
        iteratedFDerivWithin ℝ n v (Icc c r ×ˢ Ioo a b) (c, θ) := by
    intro n θ hθ
    have hL := iteratedFDerivWithin_subset hsubL
      ((uniqueDiffOn_Icc hlc).prod hangular)
      ((uniqueDiffOn_Icc hlc).prod (uniqueDiffOn_Icc hab))
      (hu.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) ⟨⟨hlc.le, le_rfl⟩, hθ⟩
    have hR := iteratedFDerivWithin_subset hsubR
      ((uniqueDiffOn_Icc hcr).prod hangular)
      ((uniqueDiffOn_Icc hcr).prod (uniqueDiffOn_Icc hab))
      (hv.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) ⟨⟨le_rfl, hcr.le⟩, hθ⟩
    exact hL.trans ((hmatch n θ hθ).trans hR.symm)
  exact (n07a_contDiffOn_two_closed_rectangles hlc hcr hangular
    (hu.mono hsubL) (hv.mono hsubR) hjets).mono
      (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)

end ContinuousFlexibility.Analysis
