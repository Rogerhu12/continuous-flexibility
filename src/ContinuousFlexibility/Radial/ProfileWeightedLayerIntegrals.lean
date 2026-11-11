import ContinuousFlexibility.Radial.ProfileLayerOverlap
import ContinuousFlexibility.Radial.ProfileScalarSquares
import ContinuousFlexibility.Radial.ProfileWeightedPartition

/-!
# Weighted integrals over endpoint layers

A pointwise weighted partition estimate is integrated against its actual
summable square density. The layer overlap then sums the result with a
uniform constant. The proof never counts profile cells of a fixed index.
-/

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped BigOperators

namespace ContinuousFlexibility.Radial

theorem profile_weighted_layer_integrals_le
    {D : ReferenceData} {C : ℕ → ℝ} (h : AccumulatingProfileBounds D C)
    {N B : ℕ}
    (hN : ∀ n m : ℕ, ∀ r : ℝ,
      r ∈ profileEndpointLayer D (C 0) n → r ∈ D.cells m →
        n ≤ D.cellIndex m + N ∧ D.cellIndex m ≤ n + N)
    (hB : ∀ r, (Function.support (fun m => D.localizer m r)).Finite ∧
      (Function.support (fun m => D.localizer m r)).ncard ≤ B)
    (w v : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hw : ∀ n, 0 ≤ w n) (hv : ∀ n, 0 ≤ v n)
    (hweight : ∀ n k, n ≤ k + N → k ≤ n + N → w n ≤ K * v k)
    {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (radialCore D)))
    (hs : Summable (fun m => v (D.cellIndex m) * profileScalarCellSquare D f m))
    (s : Finset ℕ) :
    (∑ n ∈ s, w n * ∫ r in profileEndpointLayer D (C 0) n, f r ^ 2) ≤
      ((B : ℝ) * K * ((2 * N + 1 : ℕ) : ℝ)) *
        ∑' m, v (D.cellIndex m) * profileScalarCellSquare D f m := by
  let ρ : ℝ → ℝ := fun r =>
    ∑' m, v (D.cellIndex m) * (D.localizer m r * f r) ^ 2
  have hlocal (m : ℕ) := profile_memLp_localizer_mul h.2.1 hf m
  obtain ⟨hρ, hρint⟩ := r11b_integrable_weighted_square_tsum
    (fun m r => D.localizer m r * f r) (fun m => v (D.cellIndex m))
    hlocal (fun m => hv (D.cellIndex m)) hs
  change IntegrableOn ρ (radialCore D) volume at hρ
  change (∫ r in radialCore D, ρ r) =
    ∑' m, v (D.cellIndex m) * profileScalarCellSquare D f m at hρint
  have hρ₀ (r : ℝ) : 0 ≤ ρ r :=
    tsum_nonneg (fun m => mul_nonneg (hv _) (sq_nonneg _))
  have hpoint (n : ℕ) (r : ℝ) (hr : r ∈ profileEndpointLayer D (C 0) n) :
      w n * f r ^ 2 ≤ (B : ℝ) * K * ρ r := by
    apply profile_partition_weighted_square_le
      (fun m => D.localizer m r) (f r) (fun m => v (D.cellIndex m))
      (hw n) (hB r).1 (hB r).2
      ((h.2.1.2.2.2.2.1 r
        (profileEndpointLayer_subset_core (h.2.2.1 0) n hr)).2)
    intro m hm
    have hrm : r ∈ D.cells m := h.2.1.2.2.1 m hm
    obtain ⟨hnm, hmn⟩ := hN n m r hr hrm
    exact hweight n (D.cellIndex m) hnm hmn
  have hbound (n : ℕ) :
      w n * (∫ r in profileEndpointLayer D (C 0) n, f r ^ 2) ≤
        (B : ℝ) * K * ∫ r in profileEndpointLayer D (C 0) n, ρ r := by
    have hsub := profileEndpointLayer_subset_core (D := D) (h.2.2.1 0) n
    have hfi : IntegrableOn (fun r => f r ^ 2) (profileEndpointLayer D (C 0) n) volume :=
      (show IntegrableOn (fun r => f r ^ 2) (radialCore D) volume
        from hf.integrable_sq).mono_set hsub
    have hρi : IntegrableOn ρ (profileEndpointLayer D (C 0) n) volume :=
      hρ.mono_set hsub
    calc
      _ = ∫ r in profileEndpointLayer D (C 0) n, w n * f r ^ 2 :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ r in profileEndpointLayer D (C 0) n, (B : ℝ) * K * ρ r :=
        setIntegral_mono_on (hfi.const_mul _) (hρi.const_mul _)
          (measurableSet_profileEndpointLayer _ _ _) (hpoint n)
      _ = _ := integral_const_mul _ _
  have hover := profileEndpointLayer_integral_sum_le h hN s hρ hρ₀
  calc
    (∑ n ∈ s, w n * ∫ r in profileEndpointLayer D (C 0) n, f r ^ 2) ≤
        ∑ n ∈ s, (B : ℝ) * K * ∫ r in profileEndpointLayer D (C 0) n, ρ r :=
      Finset.sum_le_sum (fun n _ => hbound n)
    _ = (B : ℝ) * K * ∑ n ∈ s, ∫ r in profileEndpointLayer D (C 0) n, ρ r := by
      rw [Finset.mul_sum]
    _ ≤ (B : ℝ) * K *
        (((2 * N + 1 : ℕ) : ℝ) * ∫ r in radialCore D, ρ r) :=
      mul_le_mul_of_nonneg_left hover (mul_nonneg (Nat.cast_nonneg B) hK)
    _ = _ := by rw [hρint]; ring

end ContinuousFlexibility.Radial
