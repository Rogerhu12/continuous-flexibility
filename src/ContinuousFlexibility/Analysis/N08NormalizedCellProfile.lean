module

public import ContinuousFlexibility.Analysis.N08CellLayerProfileJets
public import ContinuousFlexibility.Analysis.N08CellLayerWeights

/-!
# A fixed normalized family of positive radial cell tests

One sample-height power, chosen before every derivative order, pays for
all cutoff derivatives. On the entire cell the actual radial slope is
exactly that same positive sample weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

def n08NormalizedCellProfile (D : ReferenceData) (T : MaterialData)
    (A : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  T.H (T.sample m) ^ (32 : ℝ) * n08CellLayerProfile D A m r

theorem n08NormalizedCellProfile_contDiff (D : ReferenceData) (T : MaterialData)
    (A : ℝ) (m : ℕ) : ContDiff ℝ ∞ (n08NormalizedCellProfile D T A m) :=
  contDiff_const.mul (n08CellLayerProfile_contDiff D A m)

theorem n08NormalizedCellProfile_hasDerivAt {D : ReferenceData} {T : MaterialData}
    {A r : ℝ} (hA : 0 < A) (m : ℕ)
    (hr : n08CellLayerInner A (D.cellIndex m) < endpointDistance D r ∧
      endpointDistance D r < n08CellLayerOuter A (D.cellIndex m)) :
    HasDerivAt (n08NormalizedCellProfile D T A m) (T.H (T.sample m) ^ (32 : ℝ)) r := by
  apply (hasDerivAt_const_mul (x := r) (T.H (T.sample m) ^ (32 : ℝ))).congr_of_eventuallyEq
  filter_upwards [n08CellLayerCutoff_eventually_one hA m hr] with x hx
  change T.H (T.sample m) ^ (32 : ℝ) * (x * n08CellLayerCutoff D A m x) =
    T.H (T.sample m) ^ (32 : ℝ) * x
  rw [hx, mul_one]

theorem n08NormalizedCellProfile_heightMember {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {A : ℝ} (hA : 0 < A) (m : ℕ) (γ : ℝ) :
    HeightMember D T γ (fun p : PolarPoint => n08NormalizedCellProfile D T A m p.1) := by
  apply spaces_heightMember_of_compact_radial hT (n08NormalizedCellProfile_contDiff D T A m)
    (n08CellLayerCutoff_compact hA m) (n08CellLayerCutoff_tsupport_core hA m)
  intro r hr
  have hz : n08CellLayerCutoff D A m r = 0 := by
    by_contra hn
    exact hr (subset_closure hn)
  simp only [n08NormalizedCellProfile, n08CellLayerProfile, hz, mul_zero]

theorem n08NormalizedCellProfile_jet_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {A : ℝ} (hA : 1 ≤ A) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (n08NormalizedCellProfile D T A m) r| ≤ K * T.H r ^ (3 / 2 : ℝ) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  obtain ⟨K, hK, hKb⟩ := n08CellLayerProfile_jet_bound D s
  obtain ⟨L, hL, hLb⟩ := n08CellLayerBand_height_bound hD hT hA0 (by norm_num : (0 : ℝ) < 32)
  obtain ⟨Q, hQ, hQb⟩ := n08_material_height_distance_bound hT
    (by norm_num : (0 : ℝ) < 1 / 2) (8 * s)
  let V : ℝ := (32 * A ^ 3 * Real.exp 2) ^ (4 * s)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  obtain ⟨C, hC⟩ := hD
  have hsamp (m : ℕ) : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hC.2.1 m)).2.1
  refine ⟨K * L * V * Q, by positivity, fun m r hr => ?_⟩
  change |iteratedDeriv s (fun t => T.H (T.sample m) ^ (32 : ℝ) *
    n08CellLayerProfile D A m t) r| ≤ _
  rw [iteratedDeriv_const_mul_field, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (hsamp m) _)]
  by_cases hband : r ∈ n08CellLayerBand D A m
  · have hH : 0 < T.H r := (hT.2.1 r hr).2.1
    have hd : 0 < endpointDistance D r := lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
    have hsample : T.H (T.sample m) ^ (32 : ℝ) ≤ L * T.H r ^ (2 : ℝ) := by
      simpa only [show (32 : ℝ) / 16 = 2 by norm_num] using hLb m r hband
    have hwidth : (n08CellLayerInner A (D.cellIndex m))⁻¹ ^ (4 * s) ≤
        V / endpointDistance D r ^ (8 * s) := by
      simpa only [show 2 * (4 * s) = 8 * s by omega] using
        n08CellLayerBand_inverseWidth_power hA0 m (4 * s) hband
    have hpow : T.H r ^ (2 : ℝ) = T.H r ^ (1 / 2 : ℝ) * T.H r ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hH]
      norm_num
    calc
      _ ≤ T.H (T.sample m) ^ (32 : ℝ) *
          (K * (n08CellLayerInner A (D.cellIndex m))⁻¹ ^ (4 * s)) :=
        mul_le_mul_of_nonneg_left (hKb A hA m r hr) (Real.rpow_nonneg (hsamp m).le _)
      _ ≤ (L * T.H r ^ (2 : ℝ)) * (K * (V / endpointDistance D r ^ (8 * s))) :=
        mul_le_mul hsample (mul_le_mul_of_nonneg_left hwidth hK)
          (mul_nonneg hK (pow_nonneg (inv_nonneg.mpr (n08CellLayerInner_pos hA0 _).le) _))
          (mul_nonneg hL.le (Real.rpow_nonneg hH.le _))
      _ = (K * L * V) * (T.H r ^ (1 / 2 : ℝ) / endpointDistance D r ^ (8 * s)) *
          T.H r ^ (3 / 2 : ℝ) := by rw [hpow]; ring
      _ ≤ (K * L * V) * Q * T.H r ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hQb r hr) (by positivity)) (Real.rpow_nonneg hH.le _)
  · rw [n08CellLayerProfile_jet_zero hA0 m s hband, abs_zero, mul_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _)

end ContinuousFlexibility.Statements
