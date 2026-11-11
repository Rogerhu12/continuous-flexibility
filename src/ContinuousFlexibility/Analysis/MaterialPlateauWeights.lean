import ContinuousFlexibility.Analysis.MaterialEndpointComparison
import ContinuousFlexibility.Analysis.MaterialWeightShift
import ContinuousFlexibility.Analysis.MaterialMScale

/-!
# Actual sample weights on a full plateau support

The expanded support may leave its original cell. Its proven endpoint
band bound nevertheless controls the inverse height weight by the exact
same sample exponent, and any fixed material order by an arbitrarily
small positive extra order. The remaining loss is a fixed coefficient
power at the sample of the actual containing cell.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
  (endpointX materialH materialE0 materialM materialH_pos materialE0_pos materialM_pos
    materialH_neg_rpow_oneSided_shift materialM_rpow_oneSided_shift)

set_option backward.isDefEq.respectTransparency false

theorem materialPlateau_sample_weight_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    {β p σ : ℝ} (hβ : 0 ≤ β) (hp : 0 ≤ p) (hσ : 0 < σ) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        T.H t ^ (-β) * T.M t ^ p ≤
          K * T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
            T.M (T.sample j) ^ (p + σ) := by
  obtain ⟨d₀, hd₀, hcompare⟩ := materialWeightProduct_endpoint_comparison hT
  obtain ⟨L, hL, hband⟩ := materialCell_plateau_scaled_endpointX_bound hT hD hd₀
  obtain ⟨A, hA, hHshift⟩ := materialH_neg_rpow_oneSided_shift hβ hL.le
  obtain ⟨Km, hKm, hMshift⟩ := materialM_rpow_oneSided_shift hp hσ hL.le
  obtain ⟨K₁, hK₁, hcompare₁⟩ := hcompare (-β) 0 p
  obtain ⟨K₂, hK₂, hcompare₂⟩ := hcompare (-β) A (p + σ)
  have hsamp : ∀ j, T.sample j ∈ Ioo D.a D.b := by
    obtain ⟨_, hbounds⟩ := hD
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _⟩ := hT
    exact fun j => hbounds.2.1.2.2.2.1 j (hsamp j)
  refine ⟨K₁ * Km * K₂, mul_pos (mul_pos hK₁ hKm) hK₂, hA, ?_⟩
  intro j l r hl hlr hr hcell t ht
  let X : ℝ := endpointX d₀ (endpointDistance D t)
  let Y : ℝ := endpointX d₀ (endpointDistance D (T.sample j))
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hXY : X ≤ Y + L := hband j l r hl hlr hr hcell t ht
  have hmodel : materialH X ^ (-β) * materialM X ^ p ≤
      Km * materialEndpointProduct D d₀ (-β) A (p + σ) (T.sample j) := by
    have hmul := mul_le_mul (hHshift X Y hX hY hXY) (hMshift X Y hX hY hXY)
      (Real.rpow_nonneg (materialM_pos X).le p)
      (mul_nonneg (Real.rpow_nonneg (materialH_pos Y).le (-β))
        (Real.rpow_nonneg (materialE0_pos Y).le A))
    apply hmul.trans_eq
    dsimp only [materialEndpointProduct, Y]
    ring
  have hphysical : T.H t ^ (-β) * T.M t ^ p ≤
      K₁ * (materialH X ^ (-β) * materialM X ^ p) := by
    simpa only [materialWeightProduct, materialEndpointProduct, Real.rpow_zero, mul_one, X] using
      (hcompare₁ t (endpointPlateau_support_subset hl hr ht)).1
  have hsample := (hcompare₂ (T.sample j) (hsamp j)).2
  calc
    T.H t ^ (-β) * T.M t ^ p ≤
        K₁ * (Km * materialEndpointProduct D d₀ (-β) A (p + σ) (T.sample j)) :=
      hphysical.trans (mul_le_mul_of_nonneg_left hmodel hK₁.le)
    _ ≤ K₁ * (Km * (K₂ * materialWeightProduct T (-β) A (p + σ) (T.sample j))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsample hKm.le) hK₁.le
    _ = _ := by dsimp only [materialWeightProduct]; ring

end ContinuousFlexibility.Statements
