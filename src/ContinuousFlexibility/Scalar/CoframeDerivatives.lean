module

public import ContinuousFlexibility.Scalar.Coframe
public import ContinuousFlexibility.Scalar.ConnectionVariation

/-!
# Actual derivatives of the displayed orthonormal coframe

Section 3 writes `η₁ = A dr` and `η₂ = B dr + C dθ`. This module
differentiates the actual coefficients along arbitrary scalar curves.
The spatial Cartan structure equations are proved after binding these
one-parameter identities to spatial directional derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

def coframeAValue (E k p : ℝ) : ℝ :=
  Real.sqrt (heightDiscriminant E k p) / Real.sqrt (1 - p ^ 2)

def coframeBValue (k p : ℝ) : ℝ := -k * p / Real.sqrt (1 - p ^ 2)

def coframeCValue (r p : ℝ) : ℝ := r * Real.sqrt (1 - p ^ 2)

def coframeAVariation (E k p dE dk dp : ℝ) : ℝ :=
  discriminantVariation E k p dE dk dp /
      (2 * Real.sqrt (heightDiscriminant E k p) * Real.sqrt (1 - p ^ 2)) +
    Real.sqrt (heightDiscriminant E k p) * p * dp /
      ((1 - p ^ 2) * Real.sqrt (1 - p ^ 2))

def coframeBVariation (k p dk dp : ℝ) : ℝ :=
  -(dk * p + k * dp) / Real.sqrt (1 - p ^ 2) -
    k * p ^ 2 * dp / ((1 - p ^ 2) * Real.sqrt (1 - p ^ 2))

def coframeCVariation (r p dr dp : ℝ) : ℝ :=
  dr * Real.sqrt (1 - p ^ 2) - r * p * dp / Real.sqrt (1 - p ^ 2)

theorem coframeOne_eq_AValue (E k p x : ℝ) :
    coframeOne E k p x = coframeAValue E k p * x := rfl

theorem coframeTwo_eq_BCValue (r k p x y : ℝ) :
    coframeTwo r k p x y = coframeBValue k p * x + coframeCValue r p * y := by
  unfold coframeTwo coframeBValue coframeCValue
  ring

/-- The exact determinant of the triangular coframe matrix. -/
theorem coframeAValue_mul_CValue {r E k p : ℝ} (hc : 0 < 1 - p ^ 2) :
    coframeAValue E k p * coframeCValue r p =
      r * Real.sqrt (heightDiscriminant E k p) := by
  unfold coframeAValue coframeCValue
  field_simp [(Real.sqrt_pos.mpr hc).ne']

/-- The angular diagonal factor differentiated along a genuine curve. -/
theorem hasDerivAt_angularFactor {p : ℝ → ℝ} {dp x : ℝ}
    (hp : HasDerivAt p dp x) :
    HasDerivAt (fun y => 1 - p y ^ 2) (-2 * p x * dp) x := by
  convert (hasDerivAt_const x (1 : ℝ)).sub (hp.pow 2) using 1
  ring

/-- Actual one-parameter derivative of `A = √D / √(1-p²)`. -/
theorem hasDerivAt_coframeAValue
    {E k p : ℝ → ℝ} {dE dk dp x : ℝ}
    (hE : HasDerivAt E dE x) (hk : HasDerivAt k dk x)
    (hp : HasDerivAt p dp x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x))
    (hc : 0 < 1 - p x ^ 2) :
    HasDerivAt (fun y => coframeAValue (E y) (k y) (p y))
      (coframeAVariation (E x) (k x) (p x) dE dk dp) x := by
  have hds := (hasDerivAt_heightDiscriminant hE hk hp).sqrt hD.ne'
  have hci := hasDerivAt_inverse_sqrt (hasDerivAt_angularFactor hp) hc
  have ha := hds.mul hci
  have hcoeff :
      discriminantVariation (E x) (k x) (p x) dE dk dp /
          (2 * Real.sqrt (heightDiscriminant (E x) (k x) (p x))) *
          (1 / Real.sqrt (1 - p x ^ 2)) +
        Real.sqrt (heightDiscriminant (E x) (k x) (p x)) *
          (-(-2 * p x * dp) * inverseDThreeHalves (1 - p x ^ 2) / 2) =
      coframeAVariation (E x) (k x) (p x) dE dk dp := by
    unfold coframeAVariation inverseDThreeHalves
    field_simp [hc.ne', (Real.sqrt_pos.mpr hc).ne', (Real.sqrt_pos.mpr hD).ne']
  convert ha.congr_deriv hcoeff using 1
  funext y
  change Real.sqrt (heightDiscriminant (E y) (k y) (p y)) /
      Real.sqrt (1 - p y ^ 2) =
    Real.sqrt (heightDiscriminant (E y) (k y) (p y)) * (1 / Real.sqrt (1 - p y ^ 2))
  ring

/-- Actual one-parameter derivative of `B = -k p / √(1-p²)`. -/
theorem hasDerivAt_coframeBValue
    {k p : ℝ → ℝ} {dk dp x : ℝ}
    (hk : HasDerivAt k dk x) (hp : HasDerivAt p dp x)
    (hc : 0 < 1 - p x ^ 2) :
    HasDerivAt (fun y => coframeBValue (k y) (p y))
      (coframeBVariation (k x) (p x) dk dp) x := by
  have hci := hasDerivAt_inverse_sqrt (hasDerivAt_angularFactor hp) hc
  have hb := (hk.mul hp).neg.mul hci
  have hcoeff :
      -(dk * p x + k x * dp) * (1 / Real.sqrt (1 - p x ^ 2)) +
        -(k x * p x) * (-(-2 * p x * dp) * inverseDThreeHalves (1 - p x ^ 2) / 2) =
      coframeBVariation (k x) (p x) dk dp := by
    unfold coframeBVariation inverseDThreeHalves
    field_simp [hc.ne', (Real.sqrt_pos.mpr hc).ne']
    ring
  convert hb.congr_deriv hcoeff using 1
  funext y
  change -k y * p y / Real.sqrt (1 - p y ^ 2) =
    -(k y * p y) * (1 / Real.sqrt (1 - p y ^ 2))
  ring

/-- Actual one-parameter derivative of `C = r √(1-p²)`. -/
theorem hasDerivAt_coframeCValue
    {r p : ℝ → ℝ} {dr dp x : ℝ}
    (hr : HasDerivAt r dr x) (hp : HasDerivAt p dp x)
    (hc : 0 < 1 - p x ^ 2) :
    HasDerivAt (fun y => coframeCValue (r y) (p y))
      (coframeCVariation (r x) (p x) dr dp) x := by
  have hcs := (hasDerivAt_angularFactor hp).sqrt hc.ne'
  have h := hr.mul hcs
  apply h.congr_deriv
  unfold coframeCVariation
  field_simp [(Real.sqrt_pos.mpr hc).ne']
  ring

end ContinuousFlexibility
