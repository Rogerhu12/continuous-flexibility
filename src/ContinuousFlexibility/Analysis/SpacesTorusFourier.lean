module

public import ContinuousFlexibility.Analysis.SpacesCircleSpectral
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Exact two-dimensional Fourier shell projections

The normalized two-dimensional torus carries its actual Haar `L²` norm.
Fourier analysis is the isometry supplied by the orthonormal exponential
basis. Arbitrary spectral bands therefore give contractive projections
whose sum is the identity. Finite bands are genuine trigonometric
polynomials, represented by the same `L²` classes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ENNReal BigOperators ComplexConjugate Topology

set_option backward.isDefEq.respectTransparency false

local instance spacesTorusFourierMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance spacesTorusFourierProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev SpacesTorus := UnitAddTorus (Fin 2)
abbrev SpacesTorusFrequency := Fin 2 → ℤ
abbrev SpacesTorusL2 := Lp ℂ 2 (volume : Measure SpacesTorus)
abbrev SpacesTorusCoefficients := lp (fun _ : SpacesTorusFrequency => ℂ) 2

local instance spacesTorusFourierDecidableFrequency : DecidableEq SpacesTorusFrequency := Classical.decEq _

/-- The actual two-variable Fourier isometry. -/
def spacesTorusFourierEquiv : SpacesTorusL2 ≃ₗᵢ[ℂ] SpacesTorusCoefficients :=
  UnitAddTorus.mFourierBasis.repr

def spacesTorusFourier : SpacesTorusL2 →L[ℝ] SpacesTorusCoefficients :=
  spacesTorusFourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

def spacesTorusFourierInverse : SpacesTorusCoefficients →L[ℝ] SpacesTorusL2 :=
  spacesTorusFourierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

@[simp] theorem spacesTorusFourier_apply (u : SpacesTorusL2) :
    spacesTorusFourier u = spacesTorusFourierEquiv u := rfl

@[simp] theorem spacesTorusFourierInverse_apply (u : SpacesTorusCoefficients) :
    spacesTorusFourierInverse u = spacesTorusFourierEquiv.symm u := rfl

@[simp] theorem spacesTorusFourierInverse_fourier (u : SpacesTorusL2) :
    spacesTorusFourierInverse (spacesTorusFourier u) = u :=
  spacesTorusFourierEquiv.symm_apply_apply u

@[simp] theorem spacesTorusFourier_fourierInverse (u : SpacesTorusCoefficients) :
    spacesTorusFourier (spacesTorusFourierInverse u) = u :=
  spacesTorusFourierEquiv.apply_symm_apply u

theorem spacesTorusFourier_coefficient (u : SpacesTorusL2) (j : SpacesTorusFrequency) :
    spacesTorusFourier u j = UnitAddTorus.mFourierCoeff u j :=
  UnitAddTorus.mFourierBasis_repr u j

@[simp] theorem spacesTorusFourier_norm (u : SpacesTorusL2) : ‖spacesTorusFourier u‖ = ‖u‖ :=
  spacesTorusFourierEquiv.norm_map u

@[simp] theorem spacesTorusFourierInverse_norm (u : SpacesTorusCoefficients) :
    ‖spacesTorusFourierInverse u‖ = ‖u‖ := spacesTorusFourierEquiv.symm.norm_map u

/-- Projection onto a chosen Fourier band, in the original torus function space. -/
def spacesTorusBand (band : SpacesTorusFrequency → ℕ) (k : ℕ) : SpacesTorusL2 →L[ℝ] SpacesTorusL2 :=
  spacesTorusFourierInverse.comp ((lpSpectralBand band k).comp spacesTorusFourier)

theorem spacesTorusBand_apply (band : SpacesTorusFrequency → ℕ) (k : ℕ) (u : SpacesTorusL2) :
    spacesTorusBand band k u = spacesTorusFourierInverse (lpSpectralBand band k (spacesTorusFourier u)) :=
  rfl

theorem spacesTorusBand_norm_le (band : SpacesTorusFrequency → ℕ) (k : ℕ) (u : SpacesTorusL2) :
    ‖spacesTorusBand band k u‖ ≤ ‖u‖ := by
  rw [spacesTorusBand_apply, spacesTorusFourierInverse_norm, ← spacesTorusFourier_norm u]
  exact lpSpectralBand_norm_le band k _

theorem spacesTorusBand_coefficient (band : SpacesTorusFrequency → ℕ) (k : ℕ)
    (u : SpacesTorusL2) (j : SpacesTorusFrequency) :
    spacesTorusFourier (spacesTorusBand band k u) j =
      if band j = k then spacesTorusFourier u j else 0 := by
  rw [spacesTorusBand_apply, spacesTorusFourier_fourierInverse, lpSpectralBand_apply]

/-- All bands sum to the original function in its actual `L²` norm. -/
theorem spacesTorusBand_hasSum (band : SpacesTorusFrequency → ℕ) (u : SpacesTorusL2) :
    HasSum (fun k => spacesTorusBand band k u) u := by
  simpa only [spacesTorusBand_apply, spacesTorusFourierInverse_fourier] using
    spacesTorusFourierInverse.hasSum (hasSum_lpSpectralBand band (spacesTorusFourier u))

theorem spacesTorusBand_idempotent (band : SpacesTorusFrequency → ℕ) (k : ℕ)
    (u : SpacesTorusL2) : spacesTorusBand band k (spacesTorusBand band k u) = spacesTorusBand band k u := by
  apply spacesTorusFourierEquiv.injective
  apply lp.ext
  funext j
  change spacesTorusFourier (spacesTorusBand band k (spacesTorusBand band k u)) j =
    spacesTorusFourier (spacesTorusBand band k u) j
  simp only [spacesTorusBand_coefficient]
  split_ifs <;> rfl

/-- The actual finite Fourier polynomial with prescribed coefficients. -/
def spacesTorusPolynomial (S : Finset SpacesTorusFrequency) (u : SpacesTorusCoefficients) :
    C(SpacesTorus, ℂ) :=
  ∑ j : S, u j.val • UnitAddTorus.mFourier j.val

private theorem spacesTorusFourierInverse_single (j : SpacesTorusFrequency) (c : ℂ) :
    spacesTorusFourierEquiv.symm (lp.single 2 j c) = c • UnitAddTorus.mFourierLp 2 j := by
  classical
  have he : (lp.single 2 j c : SpacesTorusCoefficients) =
      c • (lp.single 2 j (1 : ℂ) : SpacesTorusCoefficients) := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
    by_cases hi : i = j
    · subst i
      simp only [Pi.single_eq_same, smul_eq_mul, mul_one]
    · simp only [Pi.single_eq_of_ne hi, smul_zero]
  rw [he, map_smul]
  have hb : UnitAddTorus.mFourierBasis j = UnitAddTorus.mFourierLp 2 j :=
    congrFun UnitAddTorus.coe_mFourierBasis j
  simpa only [spacesTorusFourierEquiv, hb] using
    congrArg (c • ·) (UnitAddTorus.mFourierBasis.repr_symm_single j)

/-- Finite coefficient masks represent exactly their trigonometric polynomials. -/
theorem spacesTorusPolynomial_toLp (S : Finset SpacesTorusFrequency) (u : SpacesTorusCoefficients) :
    (spacesTorusPolynomial S u).toLp 2 volume ℂ =
      spacesTorusFourierInverse (lpSpectralMask (S : Set SpacesTorusFrequency) u) := by
  classical
  have hmask := (lpSpectralMask_hasSum_single (S : Set SpacesTorusFrequency) u).tsum_eq
  rw [tsum_fintype] at hmask
  rw [spacesTorusFourierInverse_apply, ← hmask, map_sum]
  simp only [spacesTorusPolynomial, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact (spacesTorusFourierInverse_single j.val (u j.val)).symm

/-- A band supported on a finite frequency set is an actual finite Fourier polynomial. -/
theorem spacesTorusBand_eq_polynomial (band : SpacesTorusFrequency → ℕ) (k : ℕ)
    (S : Finset SpacesTorusFrequency) (hS : ∀ j, band j = k → j ∈ S) (u : SpacesTorusL2) :
    spacesTorusBand band k u =
      (spacesTorusPolynomial S (lpSpectralBand band k (spacesTorusFourier u))).toLp 2 volume ℂ := by
  rw [spacesTorusPolynomial_toLp, spacesTorusBand_apply]
  congr 1
  apply lp.ext
  funext j
  rw [lpSpectralMask_apply, lpSpectralBand_apply]
  by_cases hj : j ∈ S
  · rw [indicator_of_mem hj, lpSpectralBand_apply]
  · have hk : band j ≠ k := fun h => hj (hS j h)
    rw [indicator_of_notMem hj, ite_eq_right hk]

end ContinuousFlexibility.Analysis
