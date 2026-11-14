module

public import ContinuousFlexibility.Radial.ProfileScalarSquares
public import ContinuousFlexibility.Radial.ProfileWeightedPartition
public import ContinuousFlexibility.Radial.ProfileLayerOverlap

/-!
# Comparing scalar cell energy with one cutoff energy per index

Finite cell sums are first grouped by their image under the cell index.
The partition square bound is used within each fiber. Thus the resulting
cutoff energy contains one term for each index, even if many profile cells
share that index.
-/

@[expose] public section

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

namespace ContinuousFlexibility.Radial

theorem profile_cell_derivative_finset_le_layers
    {D : ReferenceData} {C : ℕ → ℝ} (h : AccumulatingProfileBounds D C)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (radialCore D))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (s : Finset ℕ) :
    (∑ m ∈ s, w (D.cellIndex m) * profileScalarCellSquare D (deriv u) m) ≤
      ∑ n ∈ s.image D.cellIndex, w n *
        ∫ r in profileEndpointLayer D (C 0) n,
          profileLayerCutoff D (C 0) n r ^ 2 * deriv u r ^ 2 := by
  classical
  let χ : ℕ → ℝ → ℝ := profileLayerCutoff D (C 0)
  have hm (m : ℕ) := profile_memLp_localizer_deriv h hu m
  have hn (n : ℕ) := profile_memLp_layerCutoff_deriv (h.2.2.1 0) hu n
  have hpoint (r : ℝ) :
      (∑ m ∈ s, w (D.cellIndex m) * (D.localizer m r * deriv u r) ^ 2) ≤
        ∑ n ∈ s.image D.cellIndex, w n * (χ n r * deriv u r) ^ 2 := by
    have he (m : ℕ) :
        w (D.cellIndex m) * (D.localizer m r * deriv u r) ^ 2 =
          (w (D.cellIndex m) * (χ (D.cellIndex m) r * deriv u r) ^ 2) *
            D.localizer m r ^ 2 := by
      by_cases hz : D.localizer m r = 0
      · simp only [hz, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero]
      · have hc : χ (D.cellIndex m) r = 1 :=
          profileLayerCutoff_one_on_cell h (h.2.1.2.2.1 m hz)
        rw [hc]
        ring
    simp_rw [he]
    exact profile_finset_index_square_le D.cellIndex s
      (fun m => D.localizer m r) (fun n => w n * (χ n r * deriv u r) ^ 2)
      (fun n => mul_nonneg (hw n) (sq_nonneg _))
      (fun t => profile_localizer_sq_sum_le_one h.2.1 t r)
  have hleft (m : ℕ) : Integrable
      (fun r => w (D.cellIndex m) * (D.localizer m r * deriv u r) ^ 2)
      (volume.restrict (radialCore D)) := (hm m).integrable_sq.const_mul _
  have hright (n : ℕ) : Integrable (fun r => w n * (χ n r * deriv u r) ^ 2)
      (volume.restrict (radialCore D)) := (hn n).integrable_sq.const_mul _
  have hrestrict (n : ℕ) :
      (∫ r in radialCore D, (χ n r * deriv u r) ^ 2) =
        ∫ r in profileEndpointLayer D (C 0) n, χ n r ^ 2 * deriv u r ^ 2 := by
    have he :
        (∫ r in profileEndpointLayer D (C 0) n, (χ n r * deriv u r) ^ 2
          ∂volume.restrict (radialCore D)) =
            ∫ r in radialCore D, (χ n r * deriv u r) ^ 2 := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro r hr
      have hz : χ n r = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hh => hr (tsupport_profileLayerCutoff_subset (h.2.2.1 0) n hh))
      simp only [hz, zero_mul, zero_pow (by decide : 2 ≠ 0)]
    rw [Measure.restrict_restrict_of_subset
      (profileEndpointLayer_subset_core (h.2.2.1 0) n)] at he
    calc
      _ = ∫ r in profileEndpointLayer D (C 0) n, (χ n r * deriv u r) ^ 2 := he.symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun r => mul_pow _ _ _)
  calc
    (∑ m ∈ s, w (D.cellIndex m) * profileScalarCellSquare D (deriv u) m) =
        ∑ m ∈ s, ∫ r in radialCore D,
          w (D.cellIndex m) * (D.localizer m r * deriv u r) ^ 2 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [profileScalarCellSquare, integral_const_mul]
    _ = ∫ r in radialCore D, ∑ m ∈ s,
        w (D.cellIndex m) * (D.localizer m r * deriv u r) ^ 2 :=
      (integral_finsetSum s (fun m _ => hleft m)).symm
    _ ≤ ∫ r in radialCore D, ∑ n ∈ s.image D.cellIndex,
        w n * (χ n r * deriv u r) ^ 2 :=
      integral_mono (integrable_finsetSum s (fun m _ => hleft m))
        (integrable_finsetSum (s.image D.cellIndex) (fun n _ => hright n)) hpoint
    _ = ∑ n ∈ s.image D.cellIndex, w n *
        ∫ r in profileEndpointLayer D (C 0) n, χ n r ^ 2 * deriv u r ^ 2 := by
      rw [integral_finsetSum (s.image D.cellIndex) (fun n _ => hright n)]
      apply Finset.sum_congr rfl
      intro n _
      rw [integral_const_mul, hrestrict]

end ContinuousFlexibility.Radial
