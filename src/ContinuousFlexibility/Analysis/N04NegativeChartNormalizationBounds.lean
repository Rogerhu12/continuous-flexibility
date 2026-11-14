module

public import ContinuousFlexibility.Analysis.N04NegativeChartWidths

/-!
# The cost of normalizing both actual coordinate fields

The physical width enters once per radial derivative. The canonical
inverse width enters only in the radial coordinate. Both are controlled
at the same old negative-half sample, with no change to the state loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

private theorem coordinateNormalization_power
    {c d M : ℝ} {i s : ℕ} (hM : 1 ≤ M)
    (hc : |c| ≤ M) (hd : |d⁻¹| ≤ M) (hi : i ≤ s) :
    |c ^ i| * (1 + |d⁻¹|) ≤ 2 * M ^ (s + 1) := by
  have hp : |c| ^ i ≤ M ^ s :=
    (pow_le_pow_left₀ (abs_nonneg c) hc i).trans (pow_le_pow_right₀ hM hi)
  have hs : 1 + |d⁻¹| ≤ 2 * M := by linarith only [hM, hd]
  rw [abs_pow]
  calc
    _ ≤ M ^ s * (2 * M) :=
      mul_le_mul hp hs (by positivity) (pow_nonneg (zero_le_one.trans hM) s)
    _ = _ := by rw [pow_succ]; ring

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- A single coefficient envelope at order `s` pays the fixed affine
pullback for both coordinate projections on every negative half. -/
theorem negativeChart_normalization_material (e : ℕ ≃ N04PieceIndex W.D) (s : ℕ) :
    let K := W.A e
    ∃ B : ℝ, 0 < B ∧ ∀ m side i, i ≤ s →
      let k := e.symm (.inl (m, side))
      |(K.physicalRight k - K.physicalLeft k) ^ i| *
        (1 + |(K.right k - K.left k)⁻¹|) ≤
          B * W.T.E0 (W.T.sample (K.cell k)) ^ B := by
  dsimp only
  obtain ⟨C, P, hC, hP, hl⟩ :=
    n04bActualTypedAtlas_negative_length_material_bounds W.hT W.hS W.through03 W.field e
  obtain ⟨B, hB, hpack⟩ :=
    coefficientEnvelope_pack (2 * (1 + C) ^ (s + 1)) (P * (s + 1 : ℕ))
  refine ⟨B, hB, fun m side i hi => ?_⟩
  let K := W.A e
  let k := e.symm (.inl (m, side))
  let E : ℝ := W.T.E0 (W.T.sample (K.cell k))
  have hE : 1 ≤ E := W.floor _
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hEp : 0 ≤ E ^ P := Real.rpow_nonneg hEpos.le P
  let M : ℝ := (1 + C) * E ^ P
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le
    (by linarith only [hC]) (Real.one_le_rpow hE hP)
  have hCM : C * E ^ P ≤ M :=
    mul_le_mul_of_nonneg_right (by linarith : C ≤ 1 + C) hEp
  have hlength := hl k m side (e.apply_symm_apply _)
  have hA := n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field e
  have hphysical : 0 < K.physicalRight k - K.physicalLeft k :=
    sub_pos.mpr (hA.referenceBounds k).1
  have hcanonical : 0 < K.right k - K.left k :=
    sub_pos.mpr (hA.referenceBounds k).2.1
  have hp : |K.physicalRight k - K.physicalLeft k| ≤ M := by
    rw [abs_of_pos hphysical]
    exact hlength.2.1.trans hCM
  have hc : |(K.right k - K.left k)⁻¹| ≤ M := by
    rw [abs_of_pos (inv_pos.mpr hcanonical)]
    exact hlength.2.2.1.trans hCM
  calc
    _ ≤ 2 * M ^ (s + 1) := coordinateNormalization_power hM hp hc hi
    _ = (2 * (1 + C) ^ (s + 1)) * E ^ (P * (s + 1 : ℕ)) := by
      dsimp only [M]
      rw [mul_pow, ← Real.rpow_mul_natCast hEpos.le P (s + 1)]
      ring
    _ ≤ B * E ^ B := hpack E hE

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeChart_normalization_material' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeChart_normalization_material
