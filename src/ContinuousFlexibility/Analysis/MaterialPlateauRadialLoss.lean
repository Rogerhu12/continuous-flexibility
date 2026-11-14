module

public import ContinuousFlexibility.Analysis.MaterialPlateauIndexBand
public import ContinuousFlexibility.Analysis.MaterialEndpointComparison
public import ContinuousFlexibility.Analysis.MaterialSampleShift

/-!
# Radial losses at every point of an expanded support

The reverse endpoint band transfers a fixed radial power of the actual
containing cell to a fixed coefficient weight at each support point.
This is the input needed to combine interval packing with local energy.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem materialCell_plateau_radial_weight_bound
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        radialE (D.cellIndex j) ^ R ≤ K * T.E0 t ^ A := by
  obtain ⟨B, hB, hindex⟩ := materialCell_plateau_index_endpointX_bound hD
  obtain ⟨d₀, hd₀, hcompare⟩ := materialWeightProduct_endpoint_comparison hT
  let L : ℝ := B + Real.sqrt |Real.log d₀|
  have hL : 0 ≤ L := add_nonneg hB.le (Real.sqrt_nonneg _)
  obtain ⟨K₁, A, hK₁, hA, hshift⟩ := materialE0_rpow_oneSided_shift hR hL
  obtain ⟨K₂, hK₂, hweights⟩ := hcompare 0 A 0
  refine ⟨K₁ * K₂, A, mul_pos hK₁ hK₂, hA, ?_⟩
  intro j l r hl hlr hr hcell t ht
  have hcore := endpointPlateau_support_subset hl hr ht
  have hd := endpointDistance_positive hcore
  have hscale := (abs_le.mp (endpointX_scale_comparison hd₀ hd)).1
  have hi := hindex j l r hl hlr hr hcell t ht
  have hi' : (D.cellIndex j : ℝ) ≤ endpointX d₀ (endpointDistance D t) + L := by
    dsimp only [L]
    linarith only [hi, hscale]
  have hE : materialE0 (endpointX d₀ (endpointDistance D t)) ^ A ≤ K₂ * T.E0 t ^ A := by
    simpa only [materialWeightProduct, materialEndpointProduct,
      Real.rpow_zero, one_mul, mul_one] using (hweights t hcore).2
  calc
    _ ≤ materialE0 (D.cellIndex j : ℝ) ^ R := radialE_rpow_le_materialE0_natCast _ hR
    _ ≤ K₁ * materialE0 (endpointX d₀ (endpointDistance D t)) ^ A :=
      hshift _ _ (Nat.cast_nonneg _) (Real.sqrt_nonneg _) hi'
    _ ≤ K₁ * (K₂ * T.E0 t ^ A) := mul_le_mul_of_nonneg_left hE hK₁.le
    _ = _ := by ring

end ContinuousFlexibility.Statements
