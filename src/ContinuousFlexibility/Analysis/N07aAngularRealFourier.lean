import ContinuousFlexibility.Analysis.N07aAngularFourier
import ContinuousFlexibility.Analysis.N07aAngularCharacters

/-!
# Real inversion for arbitrary canonical Fourier bands

Conjugate-symmetric square-summable coefficients reconstruct a real
function even when a band contains infinitely many radial frequencies.
The proof uses the full Fourier isometry and conjugation on actual `L²`
classes; no finite radial cutoff is part of the construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ComplexConjugate ENNReal

set_option backward.isDefEq.respectTransparency false

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def n07aTorusConjugation : SpacesTorusL2 →L[ℝ] SpacesTorusL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume

theorem n07aTorusConjugation_ae (u : SpacesTorusL2) :
    (n07aTorusConjugation u : SpacesTorus → ℂ) =ᵐ[volume] fun t => conj (u t) := by
  simpa only [n07aTorusConjugation, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using
    Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL u

theorem n07aTorusConjugation_fourier (u : SpacesTorusL2) (j : SpacesTorusFrequency) :
    spacesTorusFourier (n07aTorusConjugation u) j = conj (spacesTorusFourier u (-j)) := by
  rw [spacesTorusFourier_coefficient, spacesTorusFourier_coefficient,
    n07a_mFourierCoeff_integral, n07a_mFourierCoeff_integral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [n07aTorusConjugation_ae u] with t ht
  rw [ht, map_mul, neg_neg, ← UnitAddTorus.mFourier_neg]

theorem n07aTorusFourierInverse_real (u : SpacesTorusCoefficients)
    (hu : ∀ j, u (-j) = conj (u j)) :
    (fun t => conj (spacesTorusFourierInverse u t)) =ᵐ[volume] spacesTorusFourierInverse u := by
  have he : n07aTorusConjugation (spacesTorusFourierInverse u) = spacesTorusFourierInverse u := by
    apply spacesTorusFourierEquiv.injective
    apply lp.ext
    funext j
    rw [← spacesTorusFourier_apply, ← spacesTorusFourier_apply,
      n07aTorusConjugation_fourier, spacesTorusFourier_fourierInverse, hu,
      starRingEnd_self_apply]
  exact (n07aTorusConjugation_ae (spacesTorusFourierInverse u)).symm.trans
    (Filter.EventuallyEq.of_eq (congrArg (fun v : SpacesTorusL2 => (v : SpacesTorus → ℂ)) he))

def n07aTorusRealFourierInverse : SpacesTorusCoefficients →L[ℝ] SpacesTorusRealL2 :=
  (spacesLpRealPart volume).comp spacesTorusFourierInverse

@[simp] theorem n07aTorusRealFourierInverse_apply (u : SpacesTorusCoefficients) :
    n07aTorusRealFourierInverse u = spacesLpRealPart volume (spacesTorusFourierInverse u) :=
  ContinuousLinearMap.comp_apply _ _ u

theorem n07aTorusRealFourierInverse_norm_le (u : SpacesTorusCoefficients) :
    ‖n07aTorusRealFourierInverse u‖ ≤ ‖u‖ := by
  rw [n07aTorusRealFourierInverse_apply, ← spacesTorusFourierInverse_norm u]
  exact spacesLpRealPart_norm_le _ _

theorem n07aTorusRealFourierInverse_fourier (u : SpacesTorusRealL2) :
    n07aTorusRealFourierInverse (spacesTorusRealFourier u) = u := by
  rw [n07aTorusRealFourierInverse_apply, spacesTorusRealFourier_apply,
    spacesTorusFourierInverse_fourier, spacesLpRealPart_complexification]

theorem n07aTorusRealFourier_inverse (u : SpacesTorusCoefficients)
    (hu : ∀ j, u (-j) = conj (u j)) :
    spacesTorusRealFourier (n07aTorusRealFourierInverse u) = u := by
  rw [spacesTorusRealFourier_apply, n07aTorusRealFourierInverse_apply,
    spacesLpComplexification_realPart _ _ (n07aTorusFourierInverse_real u hu),
    spacesTorusFourier_fourierInverse]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ComplexConjugate

variable {S : PhysicalSpacesData} {K : CanonicalData S}

def n07aAngularFourierInverse (m : ℕ) (hm : K.left m < K.right m) :
    SpacesTorusCoefficients →L[ℝ] CanonicalL2 S K m :=
  (n07aAngularPhysicalTorusEquiv m hm).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    n07aTorusRealFourierInverse

@[simp] theorem n07aAngularFourierInverse_apply (m : ℕ) (hm : K.left m < K.right m)
    (u : SpacesTorusCoefficients) :
    n07aAngularFourierInverse m hm u =
      (n07aAngularPhysicalTorusEquiv m hm).symm (n07aTorusRealFourierInverse u) :=
  ContinuousLinearMap.comp_apply _ _ u

theorem n07aAngularFourierInverse_norm_le (m : ℕ) (hm : K.left m < K.right m)
    (u : SpacesTorusCoefficients) : ‖n07aAngularFourierInverse m hm u‖ ≤ ‖u‖ := by
  rw [n07aAngularFourierInverse_apply, LinearIsometryEquiv.norm_map]
  exact n07aTorusRealFourierInverse_norm_le u

theorem n07aAngularFourierInverse_fourier (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) : n07aAngularFourierInverse m hm (n07aAngularFourier m hm u) = u := by
  rw [n07aAngularFourierInverse_apply, n07aAngularFourier_apply,
    n07aTorusRealFourierInverse_fourier, LinearIsometryEquiv.symm_apply_apply]

theorem n07aAngularFourier_inverse (m : ℕ) (hm : K.left m < K.right m)
    (u : SpacesTorusCoefficients) (hu : ∀ j, u (-j) = conj (u j)) :
    n07aAngularFourier m hm (n07aAngularFourierInverse m hm u) = u := by
  rw [n07aAngularFourier_apply, n07aAngularFourierInverse_apply,
    LinearIsometryEquiv.apply_symm_apply, n07aTorusRealFourier_inverse u hu]

end ContinuousFlexibility.Statements
