module

public import ContinuousFlexibility.Analysis.PositiveComponentMaterialCell
public import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Positive height decay at one genuine component sample

The actual midpoint cell is chosen once. A smaller positive height power
at that same sample absorbs every fixed pointwise coefficient cost. The
proof uses the material envelope already present in `IsMaterialData`;
the whole component is never required to lie in a single cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- A polynomial point-to-sample height ratio preserves every strictly
smaller positive height exponent after absorbing the coefficient cost. -/
theorem material_height_residual_of_polynomial_ratio
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {K A γ β : ℝ} (hK : 0 < K) (hβ : 0 < β) (hβγ : β < γ) (R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      T.H r / T.H s ≤ K * T.E0 r ^ A →
      T.H r ^ γ * T.E0 r ^ R ≤ B * T.H s ^ β := by
  obtain ⟨C, hC, hbound⟩ := material_height_coefficient_power_bounded hT
    (R + A * β) (sub_pos.mpr hβγ)
  refine ⟨K ^ β * C, mul_pos (Real.rpow_pos_of_pos hK _) hC, ?_⟩
  intro r s hr hs hrs
  have hHr : 0 < T.H r := (hT.2.1 r hr).2.1
  have hHs : 0 < T.H s := (hT.2.1 s hs).2.1
  have hEr : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
  have hraise : T.H r ^ β ≤ K ^ β * T.E0 r ^ (A * β) * T.H s ^ β := by
    have hu : T.H r ^ β ≤ ((K * T.E0 r ^ A) * T.H s) ^ β :=
      Real.rpow_le_rpow hHr.le ((div_le_iff₀ hHs).mp hrs) hβ.le
    rw [Real.mul_rpow (mul_nonneg hK.le (Real.rpow_nonneg hEr.le _)) hHs.le,
      Real.mul_rpow hK.le (Real.rpow_nonneg hEr.le _),
      ← Real.rpow_mul hEr.le A β] at hu
    exact hu
  have hsplit : T.H r ^ γ = T.H r ^ (γ - β) * T.H r ^ β := by
    simpa only [sub_add_cancel] using Real.rpow_add hHr (γ - β) β
  have hnon : 0 ≤ T.H r ^ (γ - β) * T.E0 r ^ R :=
    mul_nonneg (Real.rpow_nonneg hHr.le _) (Real.rpow_nonneg hEr.le _)
  calc
    T.H r ^ γ * T.E0 r ^ R =
        (T.H r ^ (γ - β) * T.E0 r ^ R) * T.H r ^ β := by
      rw [hsplit]
      ring
    _ ≤ (T.H r ^ (γ - β) * T.E0 r ^ R) *
        (K ^ β * T.E0 r ^ (A * β) * T.H s ^ β) :=
      mul_le_mul_of_nonneg_left hraise hnon
    _ = (K ^ β * (T.H r ^ (γ - β) * T.E0 r ^ (R + A * β))) * T.H s ^ β := by
      rw [Real.rpow_add hEr]
      ring
    _ ≤ (K ^ β * C) * T.H s ^ β :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound r hr) (Real.rpow_nonneg hK.le _))
        (Real.rpow_nonneg hHs.le _)

/-- One reference-only cell simultaneously supplies the actual height
normalizer, all sample coefficient comparisons, and positive height decay.
Every constant is chosen before the component and its physical point. -/
theorem exists_wholePositive_midpoint_material_decay
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ,
      (∀ i, n04PositiveMidpoint i ∈ D.cells (cell i)) ∧
      (∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ i r,
        r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) → r ∈ Ioo D.a D.b →
        T.H r / T.H (T.sample (cell i)) ≤ B * T.E0 r ^ A) ∧
      (∀ R : ℝ, 0 ≤ R → ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ i r,
        r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) → r ∈ Ioo D.a D.b →
        T.E0 (T.sample (cell i)) ^ R ≤ B * T.E0 r ^ A) ∧
      ∀ γ β R : ℝ, 0 < β → β < γ → ∃ B : ℝ, 0 < B ∧ ∀ i r,
        r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) → r ∈ Ioo D.a D.b →
        T.H r ^ γ * T.E0 r ^ R ≤ B * T.H (T.sample (cell i)) ^ β := by
  obtain ⟨cell, hcell, ⟨K, A, hK, hA, hheight⟩, hcoefficient⟩ :=
    exists_wholePositive_midpoint_material_cells hT hRef
  refine ⟨cell, hcell, ⟨K, A, hK, hA, hheight⟩, hcoefficient, ?_⟩
  intro γ β R hβ hβγ
  obtain ⟨B, hB, hbound⟩ := material_height_residual_of_polynomial_ratio
    (A := A) hT hK hβ hβγ R
  exact ⟨B, hB, fun i r hr hrcore => hbound r (T.sample (cell i)) hrcore
    (materialSample_mem_interval hRef hT (cell i)) (hheight i r hr hrcore)⟩

end ContinuousFlexibility.Analysis
