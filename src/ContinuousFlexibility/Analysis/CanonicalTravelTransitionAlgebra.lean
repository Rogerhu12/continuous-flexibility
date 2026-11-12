import ContinuousFlexibility.Analysis.N04bConstructedRootDensity
import ContinuousFlexibility.Analysis.N04bRootInteriorRegularity

/-!
# Cancellation of the common root reparametrization in physical transport

Both actual negative charts use the same travel width and the same signed
root reparametrization. Their reference-to-current transition therefore
reduces to the smooth travel transition, including across its middle cut.
The common root factor also cancels in the height ratio. These identities
use the actual defined functions and do not assume a transport certificate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

theorem n04Coordinates_rootPhysical_transition
    (X F : PolarPoint → PolarPoint) (T : ℝ) (side : Bool) (p : PolarPoint)
    (hp : 0 ≤ n04bTravelOrientation T side (F p).1) :
    n04bRootPhysicalInverse X T side (n04bRootPhysicalChart F T side p) =
      X (F p) := by
  change X (n04bRootStripInverse T side (n04bRootStripChart T side (F p))) = X (F p)
  rw [n04bRootStripInverse_chart_of_oriented_nonneg T side hp]

private theorem inverse_sqrt_quotient_cancel
    {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    (Real.sqrt (a / s))⁻¹ / (Real.sqrt (b / s))⁻¹ = Real.sqrt (b / a) := by
  rw [Real.sqrt_div' _ hs.le, Real.sqrt_div' _ hs.le, Real.sqrt_div' _ ha.le]
  field_simp [ne_of_gt (Real.sqrt_pos.2 ha), ne_of_gt (Real.sqrt_pos.2 hb),
    ne_of_gt (Real.sqrt_pos.2 hs)]

theorem n04Coordinates_rootPhysical_height_ratio
    (A₀ A : SymmetricCoefficients) (v₀ v : PolarPoint → ℝ)
    (F₀ F : PolarPoint → PolarPoint) (T : ℝ) (side : Bool)
    (p x : PolarPoint) (heq : F x = F₀ p)
    (ha₀ : 0 < A₀.a p) (hv₀ : 0 < v₀ p) (ha : 0 < A.a x) (hv : 0 < v x)
    (hp : 0 < n04bTravelOrientation T side (F₀ p).1) :
    n04bRootPhysicalHeight A₀ v₀ F₀ T side p /
        n04bRootPhysicalHeight A v F T side x =
      Real.sqrt ((A.a x * v x) / (A₀.a p * v₀ p)) := by
  have hroot : n04bRootPhysicalChart F T side x = n04bRootPhysicalChart F₀ T side p :=
    congrArg (n04bRootStripChart T side) heq
  have hs : 0 < Real.sqrt (n04bRootPhysicalChart F₀ T side p).1 :=
    Real.sqrt_pos.2 (n04bRootPhysicalChart_fst_pos hp)
  unfold n04bRootPhysicalHeight
  rw [hroot]
  exact inverse_sqrt_quotient_cancel (mul_pos ha₀ hv₀) (mul_pos ha hv) hs

end ContinuousFlexibility.Analysis
