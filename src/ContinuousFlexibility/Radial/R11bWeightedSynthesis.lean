import ContinuousFlexibility.Radial.R11bFiniteSynthesis
import ContinuousFlexibility.Radial.EvenFourierBasis

/-!
# Exact weighted energy of finite synthesis

Finite angular Parseval commutes with the summable cell series. The even
basis includes its normalized constant vector, so the zero mode is retained
without a special coefficient or an extra scalar term.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem r11b_finiteSynthesis_weighted_sum {D : ReferenceData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c e : ι → ℝ → ℝ)
    (hc : ∀ i ∈ s, MemLp (c i) 2 (volume.restrict (radialCore D)))
    (he : ∀ i ∈ s, MemLp (e i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (w : ℕ → ℝ)
    (hs : ∀ i ∈ s, Summable (fun m => w m *
      ∫ r, (D.localizer m r * c i r) ^ 2 ∂volume.restrict (radialCore D))) :
    RadialCellIntegrable D (r11bFiniteSynthesis s c e) ∧
      Summable (fun m => w m * referenceCellSquare D m (r11bFiniteSynthesis s c e)) ∧
      (∑' m, w m * referenceCellSquare D m (r11bFiniteSynthesis s c e)) =
        ∑ i ∈ s, ∑' m, w m *
          ∫ r, (D.localizer m r * c i r) ^ 2 ∂volume.restrict (radialCore D) := by
  obtain ⟨hcell, heq⟩ := r11b_finiteSynthesis_cell_parseval hpart hab s c e hc he horth
  refine ⟨hcell, ?_, ?_⟩
  · simpa only [heq, Finset.mul_sum] using summable_sum hs
  · simp only [heq, Finset.mul_sum]
    exact Summable.tsum_finsetSum hs

theorem r11b_even_finiteSynthesis_output {D : ReferenceData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b)
    (J : Finset ℕ) (c : ℕ → ℝ → ℝ) {γ M : ℝ}
    (hc : ∀ n ∈ J, MemLp (c n) 2 (volume.restrict (radialCore D)))
    (hs : ∀ n ∈ J, Summable (fun m =>
      exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        ∫ r, (D.localizer m r * c n r) ^ 2 ∂volume.restrict (radialCore D))) :
    RadialCellIntegrable D (r11bFiniteSynthesis J c evenCosineBasis) ∧
      Summable (outputCellSquare D γ M (r11bFiniteSynthesis J c evenCosineBasis)) ∧
      (∑' m, outputCellSquare D γ M (r11bFiniteSynthesis J c evenCosineBasis) m) =
        ∑ n ∈ J, ∑' m,
          exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
            ∫ r, (D.localizer m r * c n r) ^ 2 ∂volume.restrict (radialCore D) := by
  obtain ⟨hcell, hsum, heq⟩ := r11b_finiteSynthesis_weighted_sum hpart hab J c
    evenCosineBasis hc (fun n _ => evenCosineBasis_memLp_interval n)
    (fun n _ k _ => angularPairing_evenCosineBasis n k)
    (fun m => exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))) hs
  refine ⟨hcell, ?_, ?_⟩
  · change Summable (fun m =>
      exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        referenceCellSquare D m (r11bFiniteSynthesis J c evenCosineBasis))
    exact hsum
  · change (∑' m,
      exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        referenceCellSquare D m (r11bFiniteSynthesis J c evenCosineBasis)) = _
    exact heq

theorem r11b_even_finiteSynthesis_output_norm {D : ReferenceData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b)
    (J : Finset ℕ) (c : ℕ → ℝ → ℝ) {γ M : ℝ}
    (hc : ∀ n ∈ J, MemLp (c n) 2 (volume.restrict (radialCore D)))
    (hs : ∀ n ∈ J, Summable (fun m =>
      exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        ∫ r, (D.localizer m r * c n r) ^ 2 ∂volume.restrict (radialCore D))) :
    OutputRealization D γ M 0 (r11bFiniteSynthesis J c evenCosineBasis, 0) ∧
      outputNormSquare D γ M 0 (r11bFiniteSynthesis J c evenCosineBasis, 0) =
        ∑ n ∈ J, ∑' m,
          exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
            ∫ r, (D.localizer m r * c n r) ^ 2 ∂volume.restrict (radialCore D) := by
  obtain ⟨hcell, hsum, heq⟩ := r11b_even_finiteSynthesis_output hpart hab J c hc hs
  have hrem : outputRemainder D 0 (r11bFiniteSynthesis J c evenCosineBasis, 0) =
      r11bFiniteSynthesis J c evenCosineBasis := by
    funext x
    simp only [outputRemainder, zero_mul, sub_zero]
  have hper : Function.Periodic (r11bFiniteSynthesis J c evenCosineBasis)
      (0, Real.pi) := by
    rintro ⟨r, θ⟩
    change (∑ n ∈ J, c n (r + 0) * evenCosineBasis n (θ + Real.pi)) =
      ∑ n ∈ J, c n r * evenCosineBasis n θ
    simp only [add_zero]
    apply Finset.sum_congr rfl
    intro n _
    rw [evenCosineBasis_periodic n θ]
  have heven (r θ : ℝ) :
      r11bFiniteSynthesis J c evenCosineBasis (r, -θ) =
        r11bFiniteSynthesis J c evenCosineBasis (r, θ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [evenCosineBasis_even n θ]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, hper, heven⟩
    · simpa only [hrem] using hcell
    · simpa only [hrem] using hsum
  · simpa only [outputNormSquare, hrem, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_add] using heq

end ContinuousFlexibility.Radial
