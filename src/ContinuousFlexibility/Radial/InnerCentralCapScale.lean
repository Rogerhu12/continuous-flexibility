import ContinuousFlexibility.Radial.CentralRadiusGrowth
import ContinuousFlexibility.Radial.PositiveBufferGeometry

/-!
# The central buffer scale in the actual Liouville coordinate

The same mass and action are used at both cuts. The mass controls the
actual central potential and the logarithmic derivative of the actual
integral-defined radius. The available length includes the six extra
mass units in the R09 buffer convention.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

def innerCentralCapMass (j X₀ : ℝ) : ℝ := j * X₀ / 4

def innerCentralCapAction (j X₀ : ℝ) : ℝ := j * X₀ ^ 2 / 16

theorem innerCentralCapMass_pos {j X₀ : ℝ} (hj : 0 < j) (hX : 0 < X₀) :
    0 < innerCentralCapMass j X₀ := by
  unfold innerCentralCapMass
  positivity

theorem innerCentralCapAction_pos {j X₀ : ℝ} (hj : 0 < j) (hX : 0 < X₀) :
    0 < innerCentralCapAction j X₀ := by
  unfold innerCentralCapAction
  positivity

/-- A lower barrier for the actual quadratic central potential, on
either far cap and its exterior. -/
theorem innerCentralCap_potential_lower {j X₀ x : ℝ}
    (hX : 0 ≤ X₀) (hfar : 8 * centralOscillatorA ≤ X₀ ^ 2)
    (hx : X₀ / 2 ≤ |x|) :
    innerCentralCapMass j X₀ ^ 2 ≤ centralPotential j x := by
  have hsq : (X₀ / 2) ^ 2 ≤ |x| ^ 2 :=
    (sq_le_sq₀ (by positivity : 0 ≤ X₀ / 2) (abs_nonneg x)).mpr hx
  rw [sq_abs] at hsq
  have hbase : X₀ ^ 2 / 16 ≤ x ^ 2 - centralOscillatorA := by
    nlinarith only [hsq, hfar, sq_nonneg X₀]
  have hmul := mul_le_mul_of_nonneg_left hbase (sq_nonneg j)
  unfold innerCentralCapMass centralPotential
  nlinarith only [hmul, sq_nonneg centralRadiusA]

/-- A uniform layer constant for the actual potential. Its value does
not depend on the cut, its orientation, or the frequency. -/
theorem innerCentralCap_potential_upper {j X₀ x : ℝ}
    (hj : 1 ≤ j) (hX : 1 ≤ X₀) (hx : |x| ≤ 2 * X₀) :
    centralPotential j x ≤
      (64 + 16 * centralRadiusA ^ 2) * innerCentralCapMass j X₀ ^ 2 := by
  have hj₂ : 1 ≤ j ^ 2 := by nlinarith only [hj, sq_nonneg (j - 1)]
  have hX₂ : 1 ≤ X₀ ^ 2 := by nlinarith only [hX, sq_nonneg (X₀ - 1)]
  have hprod : 1 ≤ j ^ 2 * X₀ ^ 2 := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ j ^ 2 * X₀ ^ 2 := mul_le_mul hj₂ hX₂ (by norm_num) (sq_nonneg j)
  have hsq : |x| ^ 2 ≤ (2 * X₀) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg x) (by linarith : 0 ≤ 2 * X₀)).mpr hx
  rw [sq_abs] at hsq
  have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg j)
  have hconst := mul_le_mul_of_nonneg_left hprod (sq_nonneg centralRadiusA)
  have hA := mul_nonneg (sq_nonneg j) centralOscillatorA_pos.le
  unfold centralPotential innerCentralCapMass
  nlinarith only [hmul, hconst, hA]

/-- The true physical velocity divided by the central barrier mass has
the required frequency decay. The constant is independent of X₀. -/
theorem innerCentral_cap_upsilon_over_mass {j X₀ x : ℝ}
    (hj : 0 < j) (hX : 1 ≤ X₀) (hx : |x| ≤ X₀) :
    |deriv centralRadius x / centralRadius x| / innerCentralCapMass j X₀ ≤
      (8 * centralRadiusWeightConstant) / j := by
  have hXpos : 0 < X₀ := by linarith
  have hm := innerCentralCapMass_pos hj hXpos
  have hυ : |deriv centralRadius x / centralRadius x| ≤
      centralRadiusWeightConstant * (1 + |x|) := by
    simpa only [centralRadiusLogDerivative, Real.norm_eq_abs] using
      centralRadiusLogDerivative_norm_le_linear x
  have hlinear : 1 + |x| ≤ 2 * X₀ := by linarith
  have hbound := hυ.trans (mul_le_mul_of_nonneg_left hlinear
    centralRadiusWeightConstant_pos.le)
  apply (div_le_iff₀ hm).mpr
  calc
    _ ≤ centralRadiusWeightConstant * (2 * X₀) := hbound
    _ = ((8 * centralRadiusWeightConstant) / j) * innerCentralCapMass j X₀ := by
      unfold innerCentralCapMass
      field_simp [hj.ne'] <;> ring

/-- The R09 action leaves room for its additional six mass units. -/
theorem innerCentralCap_buffer_fits {j X₀ : ℝ} (hj : 2 ≤ j) (hX : 8 ≤ X₀) :
    (innerCentralCapAction j X₀ + 6) / innerCentralCapMass j X₀ ≤ X₀ / 2 := by
  have hX₂ : 64 ≤ X₀ ^ 2 := by nlinarith only [hX, sq_nonneg (X₀ - 8)]
  have hprod : 128 ≤ j * X₀ ^ 2 := by
    calc
      128 = (2 : ℝ) * 64 := by norm_num
      _ ≤ j * X₀ ^ 2 := mul_le_mul hj hX₂ (by norm_num) (by linarith)
  apply (div_le_iff₀ (innerCentralCapMass_pos (by linarith) (by linarith))).mpr
  unfold innerCentralCapAction innerCentralCapMass
  nlinarith only [hprod]

/-- Both oriented buffers stay outside the central half interval. This
also holds along their full exteriors, where the inward parameter is negative. -/
theorem innerCentralCap_oriented_abs_lower {j X₀ t : ℝ}
    (hj : 2 ≤ j) (hX : 8 ≤ X₀) (i : Fin 2)
    (ht : t ≤ innerCentralCapAction j X₀ + 6) :
    X₀ / 2 ≤ |bufferSign i * X₀ - bufferSign i * t / innerCentralCapMass j X₀| := by
  have hm := innerCentralCapMass_pos (by linarith : 0 < j) (by linarith : 0 < X₀)
  have hdiv : t / innerCentralCapMass j X₀ ≤ X₀ / 2 :=
    (div_le_div_of_nonneg_right ht hm.le).trans (innerCentralCap_buffer_fits hj hX)
  have hpos : 0 ≤ X₀ - t / innerCentralCapMass j X₀ := by linarith
  rw [show bufferSign i * X₀ - bufferSign i * t / innerCentralCapMass j X₀ =
    bufferSign i * (X₀ - t / innerCentralCapMass j X₀) by ring,
    abs_mul, abs_bufferSign, one_mul, abs_of_nonneg hpos]
  linarith

theorem innerCentralCap_oriented_abs_upper {j X₀ t : ℝ}
    (hj : 2 ≤ j) (hX : 8 ≤ X₀) (i : Fin 2)
    (ht : 0 ≤ t) (htop : t ≤ innerCentralCapAction j X₀ + 6) :
    |bufferSign i * X₀ - bufferSign i * t / innerCentralCapMass j X₀| ≤ X₀ := by
  have hm := innerCentralCapMass_pos (by linarith : 0 < j) (by linarith : 0 < X₀)
  have hdiv : t / innerCentralCapMass j X₀ ≤ X₀ / 2 :=
    (div_le_div_of_nonneg_right htop hm.le).trans (innerCentralCap_buffer_fits hj hX)
  have hnonneg := div_nonneg ht hm.le
  have hpos : 0 ≤ X₀ - t / innerCentralCapMass j X₀ := by linarith
  rw [show bufferSign i * X₀ - bufferSign i * t / innerCentralCapMass j X₀ =
    bufferSign i * (X₀ - t / innerCentralCapMass j X₀) by ring,
    abs_mul, abs_bufferSign, one_mul, abs_of_nonneg hpos]
  linarith

/-- One far-cut condition controls the density drift for every j ≥ 2. -/
theorem innerCentral_far_cut_mass {C j X₀ : ℝ}
    (hj : 2 ≤ j) (hX : 0 ≤ X₀) (hfar : 4 * C * centralRadiusA ≤ X₀) :
    2 * C * centralRadiusA ≤ innerCentralCapMass j X₀ := by
  have hm := mul_le_mul_of_nonneg_right hj hX
  unfold innerCentralCapMass
  nlinarith only [hfar, hm]

/-- The cut may be taken beyond any previously imposed threshold, while
preserving all frequencies and both endpoints simultaneously. -/
theorem exists_innerCentral_far_cut (C initial : ℝ) :
    ∃ X₀ : ℝ, initial ≤ X₀ ∧ 8 ≤ X₀ ∧
      8 * centralOscillatorA ≤ X₀ ^ 2 ∧
      ∀ j : ℝ, 2 ≤ j → 2 * C * centralRadiusA ≤ innerCentralCapMass j X₀ := by
  let X₀ : ℝ := max initial (max 8 (max (sqrt (8 * centralOscillatorA))
    (4 * C * centralRadiusA)))
  have hinit : initial ≤ X₀ := le_max_left _ _
  have h8 : 8 ≤ X₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hs : sqrt (8 * centralOscillatorA) ≤ X₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hd : 4 * C * centralRadiusA ≤ X₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hsq : 8 * centralOscillatorA ≤ X₀ ^ 2 := by
    have h := (sq_le_sq₀ (sqrt_nonneg (8 * centralOscillatorA))
      (by linarith : 0 ≤ X₀)).mpr hs
    rwa [sq_sqrt (mul_nonneg (by norm_num) centralOscillatorA_pos.le)] at h
  exact ⟨X₀, hinit, h8, hsq, fun j hj => innerCentral_far_cut_mass hj (by linarith) hd⟩

end ContinuousFlexibility.Radial
