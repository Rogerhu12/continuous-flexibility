import ContinuousFlexibility.Analysis.SpacesComplexLp
import ContinuousFlexibility.Analysis.SpacesTorusReal
import ContinuousFlexibility.Analysis.SpacesTorusWaves

/-!
# Bounded real Fourier jet projections on the normalized torus

Finite coefficient multipliers are constructed as actual continuous
operators. Conjugate symmetry identifies their real parts with the
original complex polynomial, so Parseval gives the exact symbol estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ENNReal BigOperators ComplexConjugate

set_option backward.isDefEq.respectTransparency false

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : DecidableEq SpacesTorusFrequency := Classical.decEq _

abbrev SpacesTorusRealL2 := Lp ℝ 2 (volume : Measure SpacesTorus)

private theorem spacesTorusCutSymbol_bound (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) (j : SpacesTorusFrequency) :
    ‖if j ∈ S then d j else 0‖ ≤ ∑ i ∈ S, ‖d i‖ := by
  by_cases hj : j ∈ S
  · rw [ite_eq_left hj]
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) hj
  · rw [ite_eq_right hj, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- A finite spectral multiplier on the actual coefficient Hilbert space. -/
def spacesTorusCoefficientCut (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) : SpacesTorusCoefficients →L[ℝ] SpacesTorusCoefficients :=
  lpSpectralDiagonal
    (fun j => ContinuousLinearMap.mul ℝ ℂ (if j ∈ S then d j else 0))
    (Finset.sum_nonneg (fun i _ => norm_nonneg (d i)))
    (fun j z => by
      rw [ContinuousLinearMap.mul_apply', norm_mul]
      exact mul_le_mul_of_nonneg_right (spacesTorusCutSymbol_bound S d j) (norm_nonneg z))

theorem spacesTorusCoefficientCut_apply (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) (u : SpacesTorusCoefficients) (j : SpacesTorusFrequency) :
    spacesTorusCoefficientCut S d u j = if j ∈ S then d j * u j else 0 := by
  rw [spacesTorusCoefficientCut, lpSpectralDiagonal_apply, ContinuousLinearMap.mul_apply']
  split_ifs <;> simp only [zero_mul]

theorem spacesTorusCoefficientCut_weighted_norm_le (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) (u : SpacesTorusCoefficients) (w : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hd : ∀ j ∈ S, |w| * ‖d j‖ ≤ C) :
    ‖w • spacesTorusCoefficientCut S d u‖ ≤ C * ‖u‖ := by
  have h : ‖w • spacesTorusCoefficientCut S d u‖ ≤ ‖C • u‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro j
    simp only [lp.coeFn_smul, Pi.smul_apply, spacesTorusCoefficientCut_apply]
    by_cases hj : j ∈ S
    · simp only [ite_eq_left hj, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hd j hj) (norm_nonneg (u j))
    · simp only [ite_eq_right hj, smul_zero, norm_zero, norm_nonneg]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using h

theorem spacesTorusCoefficientCut_mask (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) (u : SpacesTorusCoefficients) :
    lpSpectralMask (S : Set SpacesTorusFrequency) (spacesTorusCoefficientCut S d u) =
      spacesTorusCoefficientCut S d u := by
  apply lp.ext
  funext j
  by_cases hj : j ∈ S
  · simp only [lpSpectralMask_apply, Set.indicator_of_mem hj]
  · simp only [lpSpectralMask_apply, Set.indicator_of_notMem hj,
      spacesTorusCoefficientCut_apply, ite_eq_right hj]

theorem spacesTorusCoefficientCut_one (S : Finset SpacesTorusFrequency)
    (u : SpacesTorusCoefficients) :
    spacesTorusCoefficientCut S (fun _ => 1) u = lpSpectralMask (S : Set SpacesTorusFrequency) u := by
  apply lp.ext
  funext j
  by_cases hj : j ∈ S
  · simp only [spacesTorusCoefficientCut_apply, lpSpectralMask_apply, ite_eq_left hj,
      Set.indicator_of_mem hj, one_mul]
  · simp only [spacesTorusCoefficientCut_apply, lpSpectralMask_apply, ite_eq_right hj,
      Set.indicator_of_notMem hj]

theorem spacesTorusCoefficientCut_inverse_polynomial (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) (u : SpacesTorusCoefficients) :
    spacesTorusFourierInverse (spacesTorusCoefficientCut S d u) =
      ContinuousMap.toLp 2 (volume : Measure SpacesTorus) ℂ
        (spacesTorusPolynomial S (spacesTorusCoefficientCut S d u)) := by
  rw [spacesTorusPolynomial_toLp, spacesTorusCoefficientCut_mask]

/-- Fourier coefficients of a real torus class, with no normalization loss. -/
def spacesTorusRealFourier : SpacesTorusRealL2 →L[ℝ] SpacesTorusCoefficients :=
  spacesTorusFourier.comp (spacesLpComplexification volume)

theorem spacesTorusRealFourier_apply (u : SpacesTorusRealL2) :
    spacesTorusRealFourier u = spacesTorusFourier (spacesLpComplexification volume u) := rfl

theorem spacesTorusRealFourier_norm (u : SpacesTorusRealL2) :
    ‖spacesTorusRealFourier u‖ = ‖u‖ := by
  rw [spacesTorusRealFourier_apply, spacesTorusFourier_norm, spacesLpComplexification_norm]

theorem spacesTorusRealFourier_neg (u : SpacesTorusRealL2) (j : SpacesTorusFrequency) :
    spacesTorusRealFourier u (-j) = conj (spacesTorusRealFourier u j) :=
  spacesTorusFourier_neg_of_real _ (spacesLpComplexification_real volume u) j

def spacesTorusRealCut (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) : SpacesTorusRealL2 →L[ℝ] SpacesTorusRealL2 :=
  (spacesLpRealPart volume).comp
    (spacesTorusFourierInverse.comp ((spacesTorusCoefficientCut S d).comp spacesTorusRealFourier))

theorem spacesTorusRealCut_apply (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) (u : SpacesTorusRealL2) :
    spacesTorusRealCut S d u = spacesLpRealPart volume
      (spacesTorusFourierInverse (spacesTorusCoefficientCut S d (spacesTorusRealFourier u))) := rfl

theorem spacesTorusRealCut_ae (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) (u : SpacesTorusRealL2) :
    (spacesTorusRealCut S d u : SpacesTorus → ℝ) =ᵐ[volume] fun t =>
      (spacesTorusPolynomial S (spacesTorusCoefficientCut S d (spacesTorusRealFourier u)) t).re := by
  rw [spacesTorusRealCut_apply, spacesTorusCoefficientCut_inverse_polynomial]
  filter_upwards [spacesLpRealPart_ae volume
    (ContinuousMap.toLp 2 (volume : Measure SpacesTorus) ℂ
      (spacesTorusPolynomial S (spacesTorusCoefficientCut S d (spacesTorusRealFourier u)))),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure SpacesTorus)
      (spacesTorusPolynomial S (spacesTorusCoefficientCut S d (spacesTorusRealFourier u)))]
    with t hr hp
  exact hr.trans (congrArg Complex.re hp)

theorem spacesTorusRealCut_weighted_norm_le (S : Finset SpacesTorusFrequency)
    (d : SpacesTorusFrequency → ℂ) (u : SpacesTorusRealL2) (w : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hd : ∀ j ∈ S, |w| * ‖d j‖ ≤ C) :
    ‖w • spacesTorusRealCut S d u‖ ≤ C * ‖u‖ := by
  rw [spacesTorusRealCut_apply, ← map_smul, ← map_smul]
  exact (spacesLpRealPart_norm_le volume _).trans ((spacesTorusFourierInverse_norm _).le.trans
    (by simpa only [spacesTorusRealFourier_norm] using
      spacesTorusCoefficientCut_weighted_norm_le S d (spacesTorusRealFourier u) w hC hd))

theorem spacesTorusRealCut_fourier (S : Finset SpacesTorusFrequency)
    (hS : ∀ j : SpacesTorusFrequency, -j ∈ S ↔ j ∈ S)
    (d : SpacesTorusFrequency → ℂ) (hd : ∀ j, d (-j) = conj (d j))
    (u : SpacesTorusRealL2) :
    spacesTorusRealFourier (spacesTorusRealCut S d u) =
      spacesTorusCoefficientCut S d (spacesTorusRealFourier u) := by
  let c := spacesTorusCoefficientCut S d (spacesTorusRealFourier u)
  have hc (j : SpacesTorusFrequency) : c (-j) = conj (c j) := by
    simp only [c, spacesTorusCoefficientCut_apply, hS, hd, spacesTorusRealFourier_neg]
    split_ifs <;> simp only [map_mul, map_zero]
  have hre : (fun t => conj (spacesTorusFourierInverse c t)) =ᵐ[volume]
      spacesTorusFourierInverse c := by
    rw [spacesTorusCoefficientCut_inverse_polynomial S d (spacesTorusRealFourier u)]
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure SpacesTorus)
      (spacesTorusPolynomial S c)] with t ht
    rw [ht]
    exact spacesTorusPolynomial_conj S c hS hc t
  rw [spacesTorusRealFourier_apply, spacesTorusRealCut_apply,
    spacesLpComplexification_realPart _ _ hre, spacesTorusFourier_fourierInverse]

end ContinuousFlexibility.Analysis
