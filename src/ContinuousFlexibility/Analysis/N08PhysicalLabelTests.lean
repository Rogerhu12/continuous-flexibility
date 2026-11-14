module

public import ContinuousFlexibility.Analysis.N08PhysicalLabelWeights
public import ContinuousFlexibility.Analysis.N08RadialForcingLowerBound
public import ContinuousFlexibility.Analysis.N08NormalizedCellHeight

/-!
# Reading the physical cell from uniformly bounded positive height tests

The same radial test family is used in the actual N01 second derivative.
Its positive slope and the return margin force a comparison between the
physical cell weight and N01's assigned control label. No placement of a
control interval in its assigned cell is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_physical_label_comparison_of_tests
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (α : ℝ) (test : ℕ → HeightPair S) (profile slope : ℕ → ℝ → ℝ)
    (hderiv : ∀ j r, HasDerivAt (profile j) (slope j r) r)
    (hslope : ∀ j r, r ∈ D.cells j → slope j r = T.H (T.sample j) ^ α)
    (hdecode : ∀ j r, r ∈ D.cells j → ∀ θ,
      heightPairField S (test j) (r, θ) = profile j r)
    (hbound : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ j, heightPairGrading S s (test j) ≤ K) :
    ∃ physical : ℕ → ℕ,
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (physical m)) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ m,
        T.H (T.sample (physical m)) ^ (α + 1) ≤
          K * T.H (T.sample (C.cell m)) ^ (3 / 8 : ℝ) := by
  classical
  obtain ⟨parameterLoss, A, B, hA, hB, hmargin⟩ :=
    n08_radialHeight_positive_slope_bound hT hS hN
  choose physical hcell c hc hcE hforcing using hmargin
  obtain ⟨K0, hK0, hK0b⟩ := hbound base
  obtain ⟨K1, hK1, hK1b⟩ := hbound (loss + parameterLoss)
  let Q : ℝ := 2 * K0 + K1 + 1
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hnorm (j : ℕ) :
      2 * heightPairGrading S base (test j) + heightPairGrading S (loss + parameterLoss) (test j) ≤ Q := by
    dsimp only [Q]
    linarith only [hK0b j, hK1b j]
  have hsample (j : ℕ) : 0 < T.H (T.sample j) ∧ 0 < T.E0 (T.sample j) := by
    have hp := hT.2.1 (T.sample j)
      (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)
    exact ⟨hp.2.1, hp.2.2.1⟩
  have hcompare (m : ℕ) :
      T.H (T.sample (physical m)) ^ α ≤
        (B * Q) * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B * radialE (D.cellIndex (physical m)) ^ A := by
    let a : ℝ := T.H (T.sample (physical m)) ^ α
    let W : ℝ := T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B
    have ha : 0 ≤ a := Real.rpow_nonneg (hsample (physical m)).1.le _
    have hW : 0 ≤ W := mul_nonneg
      (Real.rpow_nonneg (hsample (C.cell m)).1.le _)
      (Real.rpow_nonneg (hsample (C.cell m)).2.le _)
    have hlow : a * c m ≤ B * W * Q := by
      have hf := hforcing m (test (physical m)) (profile (physical m))
        (slope (physical m)) a ha (hderiv (physical m))
        (fun r hr => hslope (physical m) r (hcell m hr))
        (fun r hr θ => hdecode (physical m) r (hcell m hr) θ)
      calc
        a * c m ≤ B * W *
            (2 * heightPairGrading S base (test (physical m)) +
              heightPairGrading S (loss + parameterLoss) (test (physical m))) := by
          simpa only [W, mul_assoc] using hf
        _ ≤ _ := mul_le_mul_of_nonneg_left (hnorm (physical m)) (mul_nonneg hB.le hW)
    calc
      a = (a * c m) * (c m)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ (hc m).ne', mul_one]
      _ ≤ (B * W * Q) * (c m)⁻¹ := mul_le_mul_of_nonneg_right hlow (inv_nonneg.mpr (hc m).le)
      _ ≤ (B * W * Q) * radialE (D.cellIndex (physical m)) ^ A :=
        mul_le_mul_of_nonneg_left (hcE m) (mul_nonneg (mul_nonneg hB.le hW) hQ.le)
      _ = _ := by dsimp only [W]; ring
  obtain ⟨K, hK, hKb⟩ := n08_physical_label_height_comparison hN.1.1 hT physical C.cell
    (by norm_num : (0 : ℝ) < 3 / 4) hA.le (mul_pos hB hQ) hcompare
  refine ⟨physical, hcell, K, hK, fun m => ?_⟩
  convert hKb m using 1 <;> norm_num

/-- The actual positive cell tests remove the test-family hypothesis. -/
theorem n08_physical_label_comparison
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ physical : ℕ → ℕ,
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (physical m)) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ m,
        T.H (T.sample (physical m)) ^ (33 : ℝ) ≤
          K * T.H (T.sample (C.cell m)) ^ (3 / 8 : ℝ) := by
  obtain ⟨test, profile, slope, hderiv, hdecode, hslope, hbound⟩ :=
    n08_exists_normalized_cell_tests hN.1.1 hT hS
  simpa only [show (32 : ℝ) + 1 = 33 by norm_num] using
    n08_physical_label_comparison_of_tests hT hS hN 32 test profile slope hderiv hslope
      (fun j r _ θ => hdecode j (r, θ)) hbound

/-- The physical cells are chosen once. Every requested control-label
envelope order is paid by some fixed order in those same cells. -/
theorem n08_control_physical_cells
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ physical : ℕ → ℕ,
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (physical m)) ∧
      (∃ K : ℝ, 0 < K ∧ ∀ m,
        T.H (T.sample (physical m)) ^ (33 : ℝ) ≤
          K * T.H (T.sample (C.cell m)) ^ (3 / 8 : ℝ)) ∧
      ∀ A : ℝ, ∃ K N : ℝ, 0 < K ∧ 0 ≤ N ∧ ∀ m,
        T.M (T.sample m) ^ A ≤ K * T.M (T.sample (physical m)) ^ N := by
  obtain ⟨physical, hcell, K, hK, hcompare⟩ := n08_physical_label_comparison hT hS hN
  obtain ⟨B, hB, hindex⟩ := hN.2.2.2.2.1
  refine ⟨physical, hcell, ⟨K, hK, hcompare⟩, fun A => ?_⟩
  exact n08_sample_envelope_transfer hN.1.1 hT physical C.cell hB.le hindex
    (by norm_num : (0 : ℝ) < 33) (by norm_num : (0 : ℝ) < 3 / 8) hK hcompare A

end ContinuousFlexibility.Statements
