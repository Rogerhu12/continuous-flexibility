import ContinuousFlexibility.Radial.R11bWeightedBessel
import ContinuousFlexibility.Radial.R11bFourierCoefficients
import ContinuousFlexibility.Radial.ProfileScalarSquares

/-!
# Weighted bounds for every actual even Fourier coefficient

The normalized constant mode is included. All estimates are made directly
on localized representatives, so neither a zero mean nor a symmetry premise
is needed for the Bessel bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem r11b_evenCoefficient_localized_memLp {D : ReferenceData}
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (n m : ℕ) :
    MemLp (fun r => D.localizer m r * evenFourierCoefficient f n r) 2
      (volume.restrict (radialCore D)) := by
  have h := evenFourierCoefficient_memLp
    (r11b_memLp_radial_angularMean (hf m)) n
  change MemLp (fun r => angularPairing
    (fun θ => D.localizer m r * f (r, θ)) (evenCosineBasis n)) 2
      (volume.restrict (radialCore D)) at h
  simpa only [evenFourierCoefficient, r11b_angularPairing_const_mul] using h

theorem r11b_weighted_evenCoefficient_bounds {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m)
    (hs : Summable (fun m => w m * referenceCellSquare D m f)) :
    (∀ n, Summable (fun m => w m *
      profileScalarCellSquare D (evenFourierCoefficient f n) m)) ∧
      ∀ J : Finset ℕ,
        (∑ n ∈ J, ∑' m, w m *
          profileScalarCellSquare D (evenFourierCoefficient f n) m) ≤
            ∑' m, w m * referenceCellSquare D m f := by
  have hJ (J : Finset ℕ) :
      (∀ n ∈ J, Summable (fun m => w m *
        profileScalarCellSquare D (evenFourierCoefficient f n) m)) ∧
        (∑ n ∈ J, ∑' m, w m *
          profileScalarCellSquare D (evenFourierCoefficient f n) m) ≤
            ∑' m, w m * referenceCellSquare D m f := by
    simpa only [profileScalarCellSquare, evenFourierCoefficient] using
      r11b_weighted_cell_finite_bessel hab J evenCosineBasis hf
        (fun n _ => evenCosineBasis_memLp_interval n)
        (fun n _ k _ => angularPairing_evenCosineBasis n k) w hw hs
  exact ⟨fun n => (hJ {n}).1 n (Finset.mem_singleton_self n), fun J => (hJ J).2⟩

theorem r11b_source_evenCoefficient_bounds {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {F : RadialSource} (hF : SourceMember D γ M F) :
    (∀ n, Summable (fun m =>
      exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        profileScalarCellSquare D (evenFourierCoefficient F.1 n) m)) ∧
      ∀ J : Finset ℕ,
        (∑ n ∈ J, ∑' m,
          exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
            profileScalarCellSquare D (evenFourierCoefficient F.1 n) m) ≤
              sourceNormSquare D γ M F := by
  obtain ⟨hs, hbound⟩ := r11b_weighted_evenCoefficient_bounds hab hF.1
    (fun m => exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))
    (fun m => (exp_pos _).le) hF.2.1
  refine ⟨hs, fun J => (hbound J).trans ?_⟩
  change (∑' m, sourceCellSquare D γ M F.1 m) ≤
    F.2 ^ 2 + ∑' m, sourceCellSquare D γ M F.1 m
  exact le_add_of_nonneg_left (sq_nonneg F.2)

theorem r11b_output_evenCoefficient_bounds {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M a : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M a U) :
    (∀ n, Summable (fun m =>
      exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        profileScalarCellSquare D (evenFourierCoefficient (outputRemainder D a U) n) m)) ∧
      ∀ J : Finset ℕ,
        (∑ n ∈ J, ∑' m,
          exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
            profileScalarCellSquare D
              (evenFourierCoefficient (outputRemainder D a U) n) m) ≤
                outputNormSquare D γ M a U := by
  obtain ⟨hs, hbound⟩ := r11b_weighted_evenCoefficient_bounds hab hU.1
    (fun m => exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))
    (fun m => (exp_pos _).le) hU.2.1
  refine ⟨hs, fun J => (hbound J).trans ?_⟩
  change (∑' m, outputCellSquare D γ M (outputRemainder D a U) m) ≤
    a ^ 2 + U.2 ^ 2 + ∑' m, outputCellSquare D γ M (outputRemainder D a U) m
  exact le_add_of_nonneg_left (add_nonneg (sq_nonneg a) (sq_nonneg U.2))

end ContinuousFlexibility.Radial
