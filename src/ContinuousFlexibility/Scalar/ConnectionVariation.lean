module

public import ContinuousFlexibility.Scalar.Determinant
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Convert

/-!
# Actual parameter derivatives of the height connection

Section 3, immediately before `eq:conn-exact-variation`. All derivative
statements below concern actual one-parameter curves and use `HasDerivAt`.
The spatial Cartan equations and their exterior derivatives are separate
from these parameter differentiation rules.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

/-- The inverse square-root factor in the connection one-form. -/
def connectionInverseRoot (E k p : ℝ) : ℝ :=
  1 / Real.sqrt (heightDiscriminant E k p)

/-- The coefficient `B₁ = k / ((1-p²) √D)` in the connection one-form. -/
def connectionB1 (E k p : ℝ) : ℝ :=
  k / ((1 - p ^ 2) * Real.sqrt (heightDiscriminant E k p))

/-- The variation of the discriminant along three scalar curves. -/
def discriminantVariation (E k p dE dk dp : ℝ) : ℝ :=
  dE * (1 - p ^ 2) - 2 * E * p * dp - 2 * k * dk

/-- The total parameter derivative of `B₁`, with the common `D^(-3/2)`
factor made explicit. -/
def connectionB1Variation (E k p dE dk dp : ℝ) : ℝ :=
  E * inverseDThreeHalves (heightDiscriminant E k p) * dk -
    k * inverseDThreeHalves (heightDiscriminant E k p) * dE / 2 +
    k * p * (2 * heightDiscriminant E k p + E * (1 - p ^ 2)) *
      inverseDThreeHalves (heightDiscriminant E k p) / (1 - p ^ 2) ^ 2 * dp

/-- The radial coefficient `B₁ p_r` of the connection one-form. -/
def connectionRadialValue (E k p pr : ℝ) : ℝ := connectionB1 E k p * pr

/-- The angular coefficient `D^(-1/2) + B₁ p_θ` of the connection one-form. -/
def connectionAngularValue (E k p pθ : ℝ) : ℝ :=
  connectionInverseRoot E k p + connectionB1 E k p * pθ

/-- A positive discriminant rules out the angular denominator being zero,
even without a separate sign hypothesis on `E`. -/
theorem angular_factor_ne_zero_of_discriminant_pos {E k p : ℝ}
    (hD : 0 < heightDiscriminant E k p) : 1 - p ^ 2 ≠ 0 := by
  intro hp
  have heq : heightDiscriminant E k p = -(k ^ 2) := by
    simp [heightDiscriminant, hp]
  rw [heq] at hD
  exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg k))) hD

/-- Actual differentiation of the discriminant along arbitrary scalar curves. -/
theorem hasDerivAt_heightDiscriminant
    {E k p : ℝ → ℝ} {dE dk dp x : ℝ}
    (hE : HasDerivAt E dE x) (hk : HasDerivAt k dk x)
    (hp : HasDerivAt p dp x) :
    HasDerivAt (fun y => heightDiscriminant (E y) (k y) (p y))
      (discriminantVariation (E x) (k x) (p x) dE dk dp) x := by
  have hc := (hasDerivAt_const x (1 : ℝ)).sub (hp.pow 2)
  have hd := (hE.mul hc).sub (hk.pow 2)
  convert hd using 1
  · funext y
    rfl
  · simp only [discriminantVariation, Pi.sub_apply, Pi.pow_apply]
    ring

/-- The genuine derivative of `1 / √f`, with its removable algebra already
normalized to the factor used in the manuscript. -/
theorem hasDerivAt_inverse_sqrt {f : ℝ → ℝ} {df x : ℝ}
    (hf : HasDerivAt f df x) (hfpos : 0 < f x) :
    HasDerivAt (fun y => 1 / Real.sqrt (f y))
      (-df * inverseDThreeHalves (f x) / 2) x := by
  have hs : Real.sqrt (f x) ≠ 0 := (Real.sqrt_pos.mpr hfpos).ne'
  have hi := (hf.sqrt hfpos.ne').inv hs
  have heq : -(df / (2 * Real.sqrt (f x))) / Real.sqrt (f x) ^ 2 =
      -df * inverseDThreeHalves (f x) / 2 := by
    rw [Real.sq_sqrt hfpos.le]
    unfold inverseDThreeHalves
    field_simp [hfpos.ne', hs]
  convert hi.congr_deriv heq using 1
  funext y
  simp only [Pi.inv_apply, one_div]

/-- Total derivative of the connection's inverse square-root factor. -/
theorem hasDerivAt_connectionInverseRoot
    {E k p : ℝ → ℝ} {dE dk dp x : ℝ}
    (hE : HasDerivAt E dE x) (hk : HasDerivAt k dk x)
    (hp : HasDerivAt p dp x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) :
    HasDerivAt (fun y => connectionInverseRoot (E y) (k y) (p y))
      (-discriminantVariation (E x) (k x) (p x) dE dk dp *
        inverseDThreeHalves (heightDiscriminant (E x) (k x) (p x)) / 2) x := by
  exact hasDerivAt_inverse_sqrt (hasDerivAt_heightDiscriminant hE hk hp) hD

/-- Expressing the inverse square root through the common scale factor. -/
theorem connectionInverseRoot_eq_discriminant_mul_scale {E k p : ℝ}
    (hD : 0 < heightDiscriminant E k p) :
    connectionInverseRoot E k p =
      heightDiscriminant E k p * inverseDThreeHalves (heightDiscriminant E k p) := by
  unfold connectionInverseRoot inverseDThreeHalves
  field_simp [hD.ne', (Real.sqrt_pos.mpr hD).ne']

/-- The full actual derivative of `B₁` for three independently varying curves. -/
theorem hasDerivAt_connectionB1
    {E k p : ℝ → ℝ} {dE dk dp x : ℝ}
    (hE : HasDerivAt E dE x) (hk : HasDerivAt k dk x)
    (hp : HasDerivAt p dp x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) :
    HasDerivAt (fun y => connectionB1 (E y) (k y) (p y))
      (connectionB1Variation (E x) (k x) (p x) dE dk dp) x := by
  have hc : 1 - p x ^ 2 ≠ 0 := angular_factor_ne_zero_of_discriminant_pos hD
  have hpc := (hasDerivAt_const x (1 : ℝ)).sub (hp.pow 2)
  have hf := hasDerivAt_connectionInverseRoot hE hk hp hD
  have hb := (hk.div hpc hc).mul hf
  have hcoeff :
      (dk * (1 - p x ^ 2) - k x * (0 - 2 * p x ^ (2 - 1) * dp)) /
          (1 - p x ^ 2) ^ 2 * connectionInverseRoot (E x) (k x) (p x) +
        k x / (1 - p x ^ 2) *
          (-discriminantVariation (E x) (k x) (p x) dE dk dp *
            inverseDThreeHalves (heightDiscriminant (E x) (k x) (p x)) / 2) =
      connectionB1Variation (E x) (k x) (p x) dE dk dp := by
    rw [connectionInverseRoot_eq_discriminant_mul_scale hD]
    unfold connectionB1Variation discriminantVariation heightDiscriminant
    field_simp [hc]
    ring
  convert hb.congr_deriv hcoeff using 1
  funext y
  simp only [connectionB1, connectionInverseRoot, Pi.mul_apply, Pi.inv_apply,
    Pi.sub_apply, Pi.pow_apply, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The manuscript's partial derivative `(B₁)_k = E D^(-3/2)`. -/
theorem hasDerivAt_connectionB1_k {E k p : ℝ}
    (hD : 0 < heightDiscriminant E k p) :
    HasDerivAt (fun y => connectionB1 E y p)
      (E * inverseDThreeHalves (heightDiscriminant E k p)) k := by
  have h := hasDerivAt_connectionB1 (hasDerivAt_const k E)
    (hasDerivAt_id k) (hasDerivAt_const k p) hD
  simpa [connectionB1Variation] using h

/-- The manuscript's partial derivative `(B₁)_E = -k D^(-3/2) / 2`. -/
theorem hasDerivAt_connectionB1_E {E k p : ℝ}
    (hD : 0 < heightDiscriminant E k p) :
    HasDerivAt (fun y => connectionB1 y k p)
      (-k * inverseDThreeHalves (heightDiscriminant E k p) / 2) E := by
  have h := hasDerivAt_connectionB1 (hasDerivAt_id E)
    (hasDerivAt_const E k) (hasDerivAt_const E p) hD
  simpa [connectionB1Variation, neg_mul, neg_div] using h

/-- The remaining partial derivative, needed when the angular height jet varies. -/
theorem hasDerivAt_connectionB1_p {E k p : ℝ}
    (hD : 0 < heightDiscriminant E k p) :
    HasDerivAt (fun y => connectionB1 E k y)
      (k * p * (2 * heightDiscriminant E k p + E * (1 - p ^ 2)) *
        inverseDThreeHalves (heightDiscriminant E k p) / (1 - p ^ 2) ^ 2) p := by
  have h := hasDerivAt_connectionB1 (hasDerivAt_const p E)
    (hasDerivAt_const p k) (hasDerivAt_id p) hD
  simpa [connectionB1Variation] using h

/-- Actual parameter variation of the radial connection coefficient, allowing
the spatial jet `p_r` to vary independently as a differentiable scalar curve. -/
theorem hasDerivAt_connectionRadialValue
    {E k p pr : ℝ → ℝ} {dE dk dp dpr x : ℝ}
    (hE : HasDerivAt E dE x) (hk : HasDerivAt k dk x)
    (hp : HasDerivAt p dp x) (hpr : HasDerivAt pr dpr x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) :
    HasDerivAt (fun y => connectionRadialValue (E y) (k y) (p y) (pr y))
      (connectionB1Variation (E x) (k x) (p x) dE dk dp * pr x +
        connectionB1 (E x) (k x) (p x) * dpr) x := by
  exact (hasDerivAt_connectionB1 hE hk hp hD).mul hpr

/-- Actual parameter variation of the angular connection coefficient. -/
theorem hasDerivAt_connectionAngularValue
    {E k p pθ : ℝ → ℝ} {dE dk dp dpθ x : ℝ}
    (hE : HasDerivAt E dE x) (hk : HasDerivAt k dk x)
    (hp : HasDerivAt p dp x) (hpθ : HasDerivAt pθ dpθ x)
    (hD : 0 < heightDiscriminant (E x) (k x) (p x)) :
    HasDerivAt (fun y => connectionAngularValue (E y) (k y) (p y) (pθ y))
      (-discriminantVariation (E x) (k x) (p x) dE dk dp *
          inverseDThreeHalves (heightDiscriminant (E x) (k x) (p x)) / 2 +
        (connectionB1Variation (E x) (k x) (p x) dE dk dp * pθ x +
          connectionB1 (E x) (k x) (p x) * dpθ)) x := by
  exact (hasDerivAt_connectionInverseRoot hE hk hp hD).add
    ((hasDerivAt_connectionB1 hE hk hp hD).mul hpθ)

end ContinuousFlexibility
