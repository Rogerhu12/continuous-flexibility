import ContinuousFlexibility.Radial.R11bFourierReconstruction
import ContinuousFlexibility.Radial.R11bEvenSeriesRepresentative
import ContinuousFlexibility.Radial.R11bWeakNormalTensor
import ContinuousFlexibility.Radial.R11bWeakNormalFinite
import ContinuousFlexibility.Radial.R11bWeightedCellClosure

/-!
# Reconstruction of the actual weighted normal derivative

Radial C1 mode representatives yield exact weak derivative identities for
finite sums. Physical L² convergence passes those identities to the limit,
and bounded weighted cell sums give the full output realization.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11bEvenPartialSum_weakNormalDerivative
    {D : ReferenceData} (hab : D.a < D.b)
    (c : ℕ → ℝ → ℝ)
    (hc : ∀ n, ContDiffOn ℝ 1 (c n) (radialCore D))
    (hcLp : ∀ n, MemLp (c n) 2 (volume.restrict (radialCore D)))
    (hdLp : ∀ n, MemLp (deriv (c n)) 2 (volume.restrict (radialCore D)))
    (N : ℕ) :
    WeakNormalDerivative D (r11bEvenPartialSum c N)
      (r11bEvenPartialSum (fun n => deriv (c n)) N) := by
  change WeakNormalDerivative D
    (fun x => ∑ n ∈ Finset.range N, c n x.1 * evenCosineBasis n x.2)
    (fun x => ∑ n ∈ Finset.range N, deriv (c n) x.1 * evenCosineBasis n x.2)
  exact r11b_weakNormalDerivative_finsetSum hab.le (Finset.range N)
    (fun n x => c n x.1 * evenCosineBasis n x.2)
    (fun n x => deriv (c n) x.1 * evenCosineBasis n x.2)
    (fun n _ => by
      rw [r11b_radialPhysicalMeasure_eq_prod]
      exact r11b_memLp_tensor (hcLp n) (evenCosineBasis_memLp_interval n))
    (fun n _ => by
      rw [r11b_radialPhysicalMeasure_eq_prod]
      exact r11b_memLp_tensor (hdLp n) (evenCosineBasis_memLp_interval n))
    (fun n _ => r11b_weakNormalDerivative_tensor_of_contDiffOn_one hab (hc n)
      (hcLp n) (hdLp n) (evenCosineBasis_memLp_interval n))

/-- Uniform weighted cell bounds for the original derivative partial sums
produce a genuine weak normal derivative in the full output space. -/
theorem r11b_normal_reconstruction_of_mode_bounds
    {D : ReferenceData} (hpart : RadialPartition D) (hab : D.a < D.b)
    (γ M : ℝ) {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hup : ∀ r, Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (hue : ∀ r, Function.Even (fun θ => u (r, θ)))
    (c : ℕ → ℝ → ℝ)
    (hc : ∀ n, ContDiffOn ℝ 1 (c n) (radialCore D))
    (hcEq : ∀ n, c n =ᵐ[volume.restrict (radialCore D)] evenFourierCoefficient u n)
    (hdLp : ∀ n, MemLp (deriv (c n)) 2 (volume.restrict (radialCore D)))
    (hdSq : Summable (fun n => ∫ r, deriv (c n) r ^ 2
      ∂volume.restrict (radialCore D)))
    {B : ℝ}
    (hcell : ∀ N, Summable (outputCellSquare D γ M
      (r11bEvenPartialSum (fun n => deriv (c n)) N)))
    (hbound : ∀ N, (∑' m, outputCellSquare D γ M
      (r11bEvenPartialSum (fun n => deriv (c n)) N) m) ≤ B) :
    ∃ ur : PolarPoint → ℝ, WeakNormalDerivative D u ur ∧
      OutputRealization D γ M 0 (ur, 0) ∧
      outputNormSquare D γ M 0 (ur, 0) ≤ B := by
  have hcLp : ∀ n, MemLp (c n) 2 (volume.restrict (radialCore D)) := fun n =>
    MemLp.ae_eq (hcEq n).symm
      (evenFourierCoefficient_memLp (r11b_memLp_radial_angularMean hu) n)
  obtain ⟨hP, hlim⟩ :=
    r11b_even_partialSums_tendsto_of_coefficients hu hup hue c hcEq
  obtain ⟨ur, hUr, hD, hper, heven, hDlim⟩ :=
    r11b_evenSeries_symmetric_physical_limit (D := D) (fun n => deriv (c n)) hdLp hdSq
  have hnormal : WeakNormalDerivative D u ur :=
    r11b_weakNormalDerivative_of_L2_tendsto (D := D) hab.le
      hP hD hu hUr hlim hDlim
      (fun N => r11bEvenPartialSum_weakNormalDerivative hab c hc hcLp hdLp N)
  let w : ℕ → ℝ := fun m =>
    Real.exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))
  have hw (m : ℕ) : 0 ≤ w m := (Real.exp_pos _).le
  have hs : ∀ N, Summable (fun m => w m * referenceCellSquare D m
      (r11bEvenPartialSum (fun n => deriv (c n)) N)) := by
    intro N
    simpa only [outputCellSquare, w] using hcell N
  have hb : ∀ N, (∑' m, w m * referenceCellSquare D m
      (r11bEvenPartialSum (fun n => deriv (c n)) N)) ≤ B := by
    intro N
    simpa only [outputCellSquare, w] using hbound N
  obtain ⟨hUrCell, hUrSum, hUrBound⟩ :=
    r11b_weighted_cell_square_closed hpart hab.le w hw hD hUr hDlim hs hb
  have hsum : Summable (outputCellSquare D γ M ur) := by
    simpa only [outputCellSquare, w] using hUrSum
  have hsumBound : (∑' m, outputCellSquare D γ M ur m) ≤ B := by
    simpa only [outputCellSquare, w] using hUrBound
  have hrem : outputRemainder D 0 (ur, 0) = ur := by
    funext x
    simp only [outputRemainder, zero_mul, sub_zero]
  have hreal : OutputRealization D γ M 0 (ur, 0) := by
    unfold OutputRealization
    rw [hrem]
    refine ⟨hUrCell, hsum, ?_, ?_⟩
    · rintro ⟨r, θ⟩
      change ur (r + 0, θ + Real.pi) = ur (r, θ)
      simpa only [add_zero] using hper r θ
    · intro r θ
      exact heven r θ
  refine ⟨ur, hnormal, hreal, ?_⟩
  simpa only [outputNormSquare, hrem, zero_pow (by decide : 2 ≠ 0), zero_add]
    using hsumBound

end

end ContinuousFlexibility.Radial
