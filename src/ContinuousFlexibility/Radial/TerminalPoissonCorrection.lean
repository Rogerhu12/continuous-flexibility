import ContinuousFlexibility.Radial.ModeCoreSource

/-!
# The actual inner Poisson correction

Subtracting the solution for the cutoff source gives a homogeneous
Poisson column in the frozen weak equation. The scalar row, outer
support and boundary values are verified on actual representatives.
The correction pairing has one norm factor from each source column.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

theorem terminalBorderRow_representative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {U : RadialModePair D} {u : ℝ → ℝ}
    (hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) :
    (∫ r in D.a..D.b, referenceColumn D r * u r) =
      ⟪U.1, matchingBorderVector D hD hB⟫_ℝ := by
  rw [← matchingColumn_integral_eq_inner hD hB]
  apply matchingInterval_congr_ae hD
  filter_upwards [hrep] with r hr
  rw [hr]

/-- Correction by the actual inner Dirichlet solution preserves the
lift's boundary values and produces the homogeneous scalar row. -/
theorem terminalInnerPoisson_correction {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (M : RadialMatchingData D)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (L F : RadialModePair D) (u : ℝ → ℝ)
    (hL : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) L F)
    (hG : ModeInnerDirichletGraph D M (G F) F)
    (hrep : (L.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (hu : ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight))
    (houtside : ∀ r ∈ matchingOuterRegion D M, u r = 0)
    (hscalar : F.2 = 0)
    (hrow : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * u r) = 0 else L.2 = 0) :
    ∃ p : ℝ → ℝ,
      (((L - G F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p) ∧
      ContDiffOn ℝ 1 p (Icc M.innerLeft M.innerRight) ∧
      (∀ r ∈ matchingOuterRegion D M, p r = 0) ∧
      (∀ i, p (matchingCut D M i) = u (matchingCut D M i)) ∧
      ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (L - G F) 0 ∧
      (if M.frequency = 2 then
        (∫ r in D.a..D.b, referenceColumn D r * p r) = 0 else (L - G F).2 = 0) := by
  rcases hG with ⟨hEqG, hrowG, g, hgrepr, hg, hgout, hgl, hgh⟩
  let p : ℝ → ℝ := fun r => u r - g r
  have hp : ((L - G F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p := by
    change ((L.1 - (G F).1 : RadialModeL2 D) : ℝ → ℝ) =ᵐ[
      radialHilbertMeasure D] p
    filter_upwards [Lp.coeFn_sub L.1 (G F).1, hrep, hgrepr] with r hs hl hr
    simp only [Pi.sub_apply] at hs
    change _ = u r - g r
    rw [hs, hl, hr]
  refine ⟨p, hp, hu.sub hg, ?_, ?_, ?_, ?_⟩
  · intro r hr
    dsimp only [p]
    rw [houtside r hr, hgout r hr, sub_self]
  · intro i
    dsimp only [p]
    unfold matchingCut
    split_ifs <;> simp only [hgl, hgh, sub_zero]
  · simpa only [sub_self] using modeLocalEquation_sub hD hL hEqG
  · by_cases hj : M.frequency = 2
    · simp only [hj, ite_true]
      rw [terminalBorderRow_representative hD hB hp]
      change ⟪L.1 - (G F).1, matchingBorderVector D hD hB⟫_ℝ = 0
      rw [inner_sub_left]
      have hLrow : ⟪L.1, matchingBorderVector D hD hB⟫_ℝ = 0 := by
        rw [← terminalBorderRow_representative hD hB hrep]
        simpa only [hj, ite_true] using hrow
      have hGrow : ⟪(G F).1, matchingBorderVector D hD hB⟫_ℝ = 0 := by
        rw [← matchingColumn_integral_eq_inner hD hB]
        simpa only [hj, ite_true, hscalar] using hrowG
      rw [hLrow, hGrow, sub_self]
    · have hLrow : L.2 = 0 := by simpa only [if_neg hj] using hrow
      have hGrow : (G F).2 = 0 := (by
        simpa only [if_neg hj] using hrowG : (G F).2 = 0 ∧ F.2 = 0).1
      simpa only [if_neg hj, Prod.snd_sub, hLrow, hGrow, sub_self]

/-- The genuine pairing in the product norm, using the zero scalar of
the cutoff source. No Hilbert structure on the max-norm product is used. -/
theorem terminalPoisson_correction_pairing_bound {D : ReferenceData}
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (F H : RadialModePair D) (hH : H.2 = 0) :
    |modePairing D (G F) H| ≤ ‖G‖ * ‖F‖ * ‖H‖ := by
  have hfst (U : RadialModePair D) : ‖U.1‖ ≤ ‖U‖ := by
    change ‖U.1‖ ≤ max ‖U.1‖ ‖U.2‖
    exact le_max_left _ _
  have hG : ‖(G F).1‖ ≤ ‖G‖ * ‖F‖ := (hfst (G F)).trans (G.le_opNorm F)
  simp only [modePairing, hH, mul_zero, add_zero]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul hG (hfst H) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

theorem terminalPoisson_correction_two_attenuations {D : ReferenceData}
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (F H : RadialModePair D) (hH : H.2 = 0)
    {A B σ τ : ℝ}
    (hF : ‖F‖ ≤ A * exp (-σ)) (hHnorm : ‖H‖ ≤ B * exp (-τ)) :
    |modePairing D (G F) H| ≤ (‖G‖ * A * B) * exp (-σ - τ) := by
  have hA : 0 ≤ A * exp (-σ) := (norm_nonneg F).trans hF
  calc
    _ ≤ ‖G‖ * ‖F‖ * ‖H‖ := terminalPoisson_correction_pairing_bound G F H hH
    _ ≤ ‖G‖ * (A * exp (-σ)) * (B * exp (-τ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (norm_nonneg _)) hHnorm
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) hA)
    _ = _ := by rw [show -σ - τ = -σ + -τ by ring, exp_add]; ring

end ContinuousFlexibility.Radial
