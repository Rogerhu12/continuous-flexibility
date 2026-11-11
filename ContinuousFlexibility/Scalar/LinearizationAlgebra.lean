import ContinuousFlexibility.Scalar.HeightVariation

/-!
# Algebra used after expanding the actual divergence

These are intermediate scalar identities. `Linearization.lean` supplies
their arguments from actual spatial derivatives of the height and profile.
-/

namespace ContinuousFlexibility

theorem linearization_radial_drift_algebra
    (r E Er k p kr pr pt T : ℝ) (hD : heightDiscriminant E k p ≠ 0) :
    (kr + Er * pt) * T + heightQ E k pt *
        (-3 * discriminantVariation E k p Er kr pr * T / (2 * heightDiscriminant E k p)) -
      E * pr * (-3 * discriminantVariation E k p 0 (p + r * pr) pt * T /
        (2 * heightDiscriminant E k p)) =
      (kr - Er * pt / 2 + 3 * darbouxNumerator r E Er k p kr pr pt * k /
        heightDiscriminant E k p) * T := by
  field_simp [hD]
  simp only [discriminantVariation, heightDiscriminant, darbouxNumerator, heightQ]
  ring

theorem linearization_angular_drift_algebra
    (r E Er k p kr pr pt T : ℝ) (hD : heightDiscriminant E k p ≠ 0) :
    (2 * E * pr - r * Er * pr - Er * (p + r * pr) / 2) * T -
        r * E * pr * (-3 * discriminantVariation E k p Er kr pr * T /
          (2 * heightDiscriminant E k p)) +
      (E * kr - Er * k / 2) *
        (-3 * discriminantVariation E k p 0 (p + r * pr) pt * T /
          (2 * heightDiscriminant E k p)) =
      (Er * p + 2 * E * pr + 3 * darbouxNumerator r E Er k p kr pr pt * E * p /
        heightDiscriminant E k p) * T := by
  field_simp [hD]
  simp only [discriminantVariation, heightDiscriminant, darbouxNumerator, heightQ]
  ring

theorem linearization_expanded_algebra
    (r E Er k p kr pr pt T dk dp dkr dpr dpt : ℝ)
    (hr : r ≠ 0) (hD : heightDiscriminant E k p ≠ 0) :
    linearRadial E k pt T * dkr +
        2 * linearMixed E pr T * (dp + r * dpr) +
        linearAngular r E Er k kr T * (r * dpt) +
        (kr - Er * pt / 2 + 3 * darbouxNumerator r E Er k p kr pr pt * k /
          heightDiscriminant E k p) * T * dk +
        ((Er * p + 2 * E * pr + 3 * darbouxNumerator r E Er k p kr pr pt * E * p /
          heightDiscriminant E k p) * T / r) * (r * dp) =
      darbouxNumeratorVariation r E Er k p kr pr pt dk dp dkr dpr dpt * T -
        3 * darbouxNumerator r E Er k p kr pr pt *
          (-2 * E * p * dp - 2 * k * dk) * T / (2 * heightDiscriminant E k p) := by
  unfold linearRadial linearMixed linearAngular darbouxNumeratorVariation
  field_simp [hr, hD]
  simp only [darbouxNumerator, heightQ]
  ring

end ContinuousFlexibility
