import ContinuousFlexibility.Analysis.N08CellLayerEnvelope
import ContinuousFlexibility.Analysis.N08EndpointDistanceEnvelope
import ContinuousFlexibility.Analysis.N08CellLayerProfileJets
import ContinuousFlexibility.Analysis.N08MaterialFamilyBounds

/-!
# Uniform material jets of sample-scaled tail cutoffs

For each requested sample-envelope power, one material-envelope loss works
for every derivative order. Constants are selected before the cell index.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

theorem n08CellLayerCutoff_jet_zero {D : ReferenceData} {A : ℝ}
    (hA : 0 < A) (m s : ℕ) {r : ℝ} (hr : r ∉ n08CellLayerBand D A m) :
    iteratedDeriv s (n08CellLayerCutoff D A m) r = 0 := by
  by_contra hn
  exact hr (n08CellLayerCutoff_tsupport hA m
    (n08_iteratedDeriv_tsupport _ s (subset_closure hn)))

theorem n08CellLayerCutoff_ordinary_subpower {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {A : ℝ} (hA : 1 ≤ A) (s : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (n08CellLayerCutoff D A m) r| ≤ K * T.M r ^ ε := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  obtain ⟨K, hK, hKb⟩ := n08_intervalLayerCutoff_jet_bound s
  obtain ⟨L, hL, hLb⟩ := n08_distance_power_le_subpowerM hT (8 * s) hε
  let V : ℝ := (32 * A ^ 3 * Real.exp 2) ^ (4 * s)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  refine ⟨K * V * L, mul_nonneg (mul_nonneg hK hV) hL, fun m r hr => ?_⟩
  by_cases hband : r ∈ n08CellLayerBand D A m
  · have hwidth : (n08CellLayerInner A (D.cellIndex m))⁻¹ ^ (4 * s) ≤
        V * (endpointDistance D r)⁻¹ ^ (8 * s) := by
      simpa only [show 2 * (4 * s) = 8 * s by omega, div_eq_mul_inv, inv_pow] using
        n08CellLayerBand_inverseWidth_power hA0 m (4 * s) hband
    calc
      _ ≤ K * (n08CellLayerInner A (D.cellIndex m))⁻¹ ^ (4 * s) :=
        hKb D.a D.b _ _ (n08CellLayerInner_pos hA0 _) (n08CellLayerInner_le_one hA _)
          (n08CellLayerInner_le_outer hA _) r
      _ ≤ K * (V * (endpointDistance D r)⁻¹ ^ (8 * s)) :=
        mul_le_mul_of_nonneg_left hwidth hK
      _ ≤ K * (V * (L * T.M r ^ ε)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hLb r hr) hV) hK
      _ = _ := by ring
  · rw [n08CellLayerCutoff_jet_zero hA0 m s hband, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK hV) hL)
      (Real.rpow_nonneg (zero_le_one.trans (hT.2.1 r hr).2.2.2) _)

def n08ScaledCellCutoff (D : ReferenceData) (T : MaterialData)
    (A N : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  T.M (T.sample m) ^ N * n08CellLayerCutoff D A m r

theorem n08ScaledCellCutoff_contDiff (D : ReferenceData) (T : MaterialData)
    (A N : ℝ) (m : ℕ) : ContDiff ℝ ∞ (n08ScaledCellCutoff D T A N m) :=
  contDiff_const.mul (n08CellLayerCutoff_contDiff D A m)

theorem n08ScaledCellCutoff_ordinary_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {A : ℝ} (hA : 1 ≤ A) (N : ℝ) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (n08ScaledCellCutoff D T A N m) r| ≤ K * T.M r ^ loss := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  obtain ⟨U, R, hU, _, hUb⟩ := n08CellLayerBand_envelope_bound hD hT hA0 N
  obtain ⟨loss, hloss⟩ := exists_nat_ge (R + 1)
  obtain ⟨B, hB⟩ := hD
  have hsample (m : ℕ) : 0 < T.M (T.sample m) :=
    zero_lt_one.trans_le (hT.2.1 _ (materialSample_mem_radialCore hT hB.2.1 m)).2.2.2
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨K, hK, hKb⟩ := n08CellLayerCutoff_ordinary_subpower hT hA s zero_lt_one
  refine ⟨U * K, mul_nonneg hU.le hK, fun m r hr => ?_⟩
  have hM : 1 ≤ T.M r := (hT.2.1 r hr).2.2.2
  have hMp : 0 < T.M r := zero_lt_one.trans_le hM
  change |iteratedDeriv s (fun t => T.M (T.sample m) ^ N * n08CellLayerCutoff D A m t) r| ≤ _
  rw [iteratedDeriv_const_mul_field, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (hsample m) _)]
  by_cases hband : r ∈ n08CellLayerBand D A m
  · calc
      _ ≤ (U * T.M r ^ R) * (K * T.M r ^ (1 : ℝ)) :=
        mul_le_mul (hUb m r hband) (hKb m r hr) (abs_nonneg _)
          (mul_nonneg hU.le (Real.rpow_nonneg hMp.le _))
      _ = (U * K) * T.M r ^ (R + 1) := by rw [Real.rpow_add hMp]; ring
      _ ≤ (U * K) * T.M r ^ (loss : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM hloss)
          (mul_nonneg hU.le hK)
      _ = _ := by rw [Real.rpow_natCast]
  · rw [n08CellLayerCutoff_jet_zero hA0 m s hband, abs_zero, mul_zero]
    exact mul_nonneg (mul_nonneg hU.le hK) (pow_nonneg hMp.le _)

theorem n08ScaledCellCutoff_material_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {A : ℝ} (hA : 1 ≤ A) (N : ℝ) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m x,
      |iteratedDeriv s (fun t => n08ScaledCellCutoff D T A N m (T.radius t)) x| ≤
        K * T.M (T.radius x) ^ loss := by
  obtain ⟨loss, hb⟩ := n08ScaledCellCutoff_ordinary_bound hD hT hA N
  refine ⟨loss, fun s => ?_⟩
  have hb' : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m r, r ∈ Ioo D.a D.b →
      |iteratedDeriv n (n08ScaledCellCutoff D T A N m) r| ≤ K * (1 : ℝ) * T.M r ^ loss := by
    intro n
    obtain ⟨K, hK, hKb⟩ := hb n
    exact ⟨K, hK, fun m r hr => by simpa only [mul_one] using hKb m r hr⟩
  obtain ⟨K, hK, hKb⟩ := n08_comp_materialRadius_majorant hT
    (fun m => (n08ScaledCellCutoff_contDiff D T A N m).contDiffOn)
    (N := fun _ : ℕ => (1 : ℝ)) (W := fun r => T.M r ^ loss)
    (fun _ => zero_le_one)
    (fun r hr => pow_nonneg (zero_le_one.trans (hT.2.1 r hr).2.2.2) _) hb' s
  exact ⟨K, hK, fun m x => by simpa only [mul_one] using hKb m x⟩

end ContinuousFlexibility.Statements
