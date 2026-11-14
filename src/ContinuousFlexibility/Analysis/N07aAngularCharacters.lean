module

public import ContinuousFlexibility.Analysis.SpacesTorusFourier
public import ContinuousFlexibility.Analysis.SpacesCircleFourierJets

/-!
# Public character identities for the two-dimensional angular Fourier model

The product formula is derived from the public character laws rather
than unfolding the torus character implementation. It separates the
unrestricted radial Fourier index from the genuine period-`π` angular
frequency.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory ContinuousFlexibility.Statements
open scoped ComplexConjugate BigOperators

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem n07a_mFourier_single (i : Fin 2) (n : ℤ) (t : SpacesTorus) :
    UnitAddTorus.mFourier (Pi.single i n) t = fourier n (t i) := by
  induction n using Int.induction_on with
  | zero =>
    rw [Pi.single_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, fourier_zero]
  | succ n ih =>
    rw [Pi.single_add, UnitAddTorus.mFourier_add, ih,
      UnitAddTorus.mFourier_single, fourier_add]
  | pred n ih =>
    rw [sub_eq_add_neg, Pi.single_add, UnitAddTorus.mFourier_add, ih,
      Pi.single_neg, UnitAddTorus.mFourier_neg, UnitAddTorus.mFourier_single,
      fourier_add, fourier_neg, fourier_neg]

theorem n07a_mFourier_finTwo (j : SpacesTorusFrequency) (t : SpacesTorus) :
    UnitAddTorus.mFourier j t = fourier (j 0) (t 0) * fourier (j 1) (t 1) := by
  have hj : j = Pi.single 0 (j 0) + Pi.single 1 (j 1) := by
    funext i
    fin_cases i <;> simp
  conv_lhs => rw [hj, UnitAddTorus.mFourier_add, n07a_mFourier_single, n07a_mFourier_single]

theorem n07a_mFourier_norm (j : SpacesTorusFrequency) (t : SpacesTorus) :
    ‖UnitAddTorus.mFourier j t‖ = 1 := by
  rw [n07a_mFourier_finTwo, norm_mul]
  simp only [fourier_apply, Circle.norm_coe, one_mul]

/-- The torus coefficient as its actual Haar integral, using the public
coordinate integral and change-of-fundamental-domain theorem. -/
theorem n07a_mFourierCoeff_integral (f : SpacesTorus → ℂ) (j : SpacesTorusFrequency) :
    UnitAddTorus.mFourierCoeff f j = ∫ t, UnitAddTorus.mFourier (-j) t * f t := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral f j (fun _ => 0)]
  simpa only [smul_eq_mul] using
    (UnitAddTorus.integral_preimage
      (fun t : SpacesTorus => UnitAddTorus.mFourier (-j) t • f t) (fun _ => 0)).symm

theorem n07a_unitFourier_pi (n : ℤ) (θ : ℝ) :
    fourier n ((θ / Real.pi : ℝ) : UnitAddCircle) = circleFourierWave n θ := by
  rw [circleFourierWave, fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

end ContinuousFlexibility.Analysis
