module

public import ContinuousFlexibility.Analysis.MaterialPlateauIndexBand
public import ContinuousFlexibility.Analysis.MaterialPlateauWeights
public import ContinuousFlexibility.Analysis.MaterialSampleGlobalModels

/-!
# Moving actual sample weights into the expanded plateau

The reverse endpoint band bounds the sample coordinate by the coordinate
of every point in the expanded support. The inverse height exponent is
preserved. Its fixed endpoint loss costs one material order, and the
material comparison costs one more, uniformly in the requested order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem materialCell_plateau_scaled_reverse_endpointX_bound
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {d₀ : ℝ} (hd₀ : 0 < d₀) :
    ∃ L : ℝ, 0 < L ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        endpointX d₀ (endpointDistance D (T.sample j)) ≤
          endpointX d₀ (endpointDistance D t) + L := by
  obtain ⟨B, hB, hband⟩ := materialCell_plateau_index_endpointX_bound hD
  have hdata := hT
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _, hcomp⟩
  obtain ⟨C, _, hC, _, hcompare⟩ := hcomp
  refine ⟨C + B + 2 * Real.sqrt |Real.log d₀|,
    add_pos_of_pos_of_nonneg (add_pos hC hB) (by positivity), ?_⟩
  intro j l r hl hlr hr hcell t ht
  have hsampleCore := materialSample_mem_radialCore hT hD.choose_spec.2.1 j
  have htCore := endpointPlateau_support_subset hl hr ht
  have hs := (abs_le.mp (endpointX_scale_comparison hd₀
    (endpointDistance_positive hsampleCore))).2
  have ht' := (abs_le.mp (endpointX_scale_comparison hd₀
    (endpointDistance_positive htCore))).1
  have hj := (abs_le.mp (hcompare j (T.sample j) (hsamp j)).1).2
  have hb := hband j l r hl hlr hr hcell t ht
  linarith only [hs, ht', hj, hb]

/-- The extra order is exactly two, independent of the order `s` and
of the actual cell or component whose plateau is used. -/
theorem materialCell_plateau_sample_weight_bound
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {β : ℝ} (hβ : 0 ≤ β) :
    ∀ s : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        T.H (T.sample j) ^ (-β) * T.M (T.sample j) ^ s ≤
          K * T.H t ^ (-β) * T.M t ^ (s + 2) := by
  obtain ⟨d₀, hd₀, hcompare⟩ := materialWeightProduct_endpoint_comparison hT
  obtain ⟨L, hL, hband⟩ := materialCell_plateau_scaled_reverse_endpointX_bound hD hT hd₀
  obtain ⟨A, _, hHshift⟩ := materialH_neg_rpow_oneSided_shift hβ hL.le
  have hdata := hT
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, hE, _, _, _, _, _, _⟩
  obtain ⟨KE, hKE, hendpoint⟩ := hE A
  intro s
  obtain ⟨KM, hKM, hMshift⟩ := materialM_rpow_oneSided_shift
    (Nat.cast_nonneg (α := ℝ) s) (by norm_num : (0 : ℝ) < 1) hL.le
  obtain ⟨K1, hK1, hcompare1⟩ := hcompare (-β) 0 (s : ℝ)
  obtain ⟨K2, hK2, hcompare2⟩ := hcompare (-β) A ((s : ℝ) + 1)
  refine ⟨K1 * KM * K2 * KE, mul_pos (mul_pos (mul_pos hK1 hKM) hK2) hKE, ?_⟩
  intro j l r hl hlr hr hcell t ht
  let X : ℝ := endpointX d₀ (endpointDistance D (T.sample j))
  let Y : ℝ := endpointX d₀ (endpointDistance D t)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hXY : X ≤ Y + L := hband j l r hl hlr hr hcell t ht
  have hsampleCore := materialSample_mem_radialCore hT hD.choose_spec.2.1 j
  have htCore := endpointPlateau_support_subset hl hr ht
  have hHt : 0 < T.H t := (hT.2.1 t htCore).2.1
  have hMt : 0 < T.M t := zero_lt_one.trans_le (hT.2.1 t htCore).2.2.2
  have hmodel : materialH X ^ (-β) * materialM X ^ (s : ℝ) ≤
      KM * materialEndpointProduct D d₀ (-β) A ((s : ℝ) + 1) t := by
    have hh := mul_le_mul (hHshift X Y hX hY hXY) (hMshift X Y hX hY hXY)
      (Real.rpow_nonneg (materialM_pos X).le _)
      (mul_nonneg (Real.rpow_nonneg (materialH_pos Y).le _)
        (Real.rpow_nonneg (materialE0_pos Y).le _))
    exact hh.trans_eq (by dsimp only [materialEndpointProduct, Y]; ring)
  have hsample : T.H (T.sample j) ^ (-β) * T.M (T.sample j) ^ (s : ℝ) ≤
      K1 * (materialH X ^ (-β) * materialM X ^ (s : ℝ)) := by
    simpa only [materialWeightProduct, materialEndpointProduct, Real.rpow_zero, mul_one, X]
      using (hcompare1 (T.sample j) hsampleCore).1
  have hpoint := (hcompare2 t htCore).2
  have hraw : T.H (T.sample j) ^ (-β) * T.M (T.sample j) ^ (s : ℝ) ≤
      (K1 * KM * K2) * T.H t ^ (-β) * T.E0 t ^ A * T.M t ^ ((s : ℝ) + 1) := by
    calc
      _ ≤ K1 * (KM * materialEndpointProduct D d₀ (-β) A ((s : ℝ) + 1) t) :=
        hsample.trans (mul_le_mul_of_nonneg_left hmodel hK1.le)
      _ ≤ K1 * (KM * (K2 * materialWeightProduct T (-β) A ((s : ℝ) + 1) t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpoint hKM.le) hK1.le
      _ = _ := by dsimp only [materialWeightProduct]; ring
  have hresult : T.H (T.sample j) ^ (-β) * T.M (T.sample j) ^ (s : ℝ) ≤
      (K1 * KM * K2 * KE) * T.H t ^ (-β) * T.M t ^ (((s + 2 : ℕ) : ℝ)) := by
    calc
      _ ≤ (K1 * KM * K2) * T.H t ^ (-β) * T.E0 t ^ A *
          T.M t ^ ((s : ℝ) + 1) := hraw
      _ ≤ (K1 * KM * K2) * T.H t ^ (-β) * (KE * T.M t) *
          T.M t ^ ((s : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hendpoint t htCore)
            (mul_nonneg (mul_pos (mul_pos hK1 hKM) hK2).le (Real.rpow_nonneg hHt.le _)))
          (Real.rpow_nonneg hMt.le _)
      _ = _ := by
        have horder : ((s + 2 : ℕ) : ℝ) = ((s : ℝ) + 1) + 1 := by push_cast; ring
        rw [horder, Real.rpow_add hMt ((s : ℝ) + 1) 1, Real.rpow_one]
        ring
  simpa only [Real.rpow_natCast] using hresult

end ContinuousFlexibility.Statements
