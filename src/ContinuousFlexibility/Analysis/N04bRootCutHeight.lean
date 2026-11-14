module

public import ContinuousFlexibility.Analysis.N04bRootCutPowers
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Transmission for the actual root height and physical pullback

X is the inverse of a travel chart, and A is its positive travel density.
The height is (sqrt(A / sqrt ξ))⁻¹, exactly as in the canonical root
construction. The proof identifies u / h with the gauged travel pullback
on a neighborhood of the positive cut radius and uses its actual
Fréchet derivative. The physical cut is X(T/2, θ).
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n04bRootHeightInTravel (T s : ℝ) (A : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  (Real.sqrt (A (n04bSignedTravel T s n04bRootTravel p) /
    Real.sqrt p.1))⁻¹

def n04bRootUnknown (T s : ℝ) (X : PolarPoint → PolarPoint)
    (A u : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  u (X (n04bSignedTravel T s n04bRootTravel p)) /
    n04bRootHeightInTravel T s A p

def n04bTravelUnknown (X : PolarPoint → PolarPoint)
    (A u : PolarPoint → ℝ) (q : PolarPoint) : ℝ :=
  Real.sqrt (A q) * u (X q)

theorem n04bRootHeightInTravel_pos
    (T s : ℝ) (A : PolarPoint → ℝ) {p : PolarPoint}
    (hp : 0 < p.1)
    (hA : 0 < A (n04bSignedTravel T s n04bRootTravel p)) :
    0 < n04bRootHeightInTravel T s A p := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (div_pos hA (Real.sqrt_pos.2 hp)))

/-- This is an identity of the actual height quotient, not a prescribed
value or derivative at the cut. -/
theorem n04bRootUnknown_eq_gauged
    (T s : ℝ) (X : PolarPoint → PolarPoint) (A u : PolarPoint → ℝ)
    {p : PolarPoint} (hp : 0 < p.1) :
    n04bRootUnknown T s X A u p =
      n04bGaugedTravel T s n04bRootTravel n04bRootGauge
        (n04bTravelUnknown X A u) p := by
  dsimp only [n04bRootUnknown, n04bRootHeightInTravel,
    n04bGaugedTravel, n04bTravelUnknown]
  rw [div_inv_eq_mul, Real.sqrt_div' _ (Real.sqrt_nonneg _),
    n04b_rootGauge_eq_inv_sqrt_sqrt hp]
  ring

theorem n04bTravelUnknown_differentiableAt
    {X : PolarPoint → PolarPoint} {A u : PolarPoint → ℝ} {q : PolarPoint}
    (hX : DifferentiableAt ℝ X q) (hA : DifferentiableAt ℝ A q)
    (hA0 : 0 < A q) (hu : DifferentiableAt ℝ u (X q)) :
    DifferentiableAt ℝ (n04bTravelUnknown X A u) q := by
  have hs : DifferentiableAt ℝ (fun y => Real.sqrt (A y)) q := by
    simpa only [Real.sqrt_eq_rpow] using
      hA.rpow_const (p := (1 / 2 : ℝ)) (Or.inl (ne_of_gt hA0))
  exact hs.mul (hu.comp q hX)

/-- The manuscript's transmission matrix for the two genuine physical
pullbacks and the explicit root height. It holds on the moving travel cut. -/
theorem n04b_root_unknown_transmission
    {T : ℝ} (hT : 0 < T) (θ : ℝ)
    (X : PolarPoint → PolarPoint) (A u : PolarPoint → ℝ)
    (hX : DifferentiableAt ℝ X (T / 2, θ))
    (hA : DifferentiableAt ℝ A (T / 2, θ))
    (hA0 : 0 < A (T / 2, θ))
    (hu : DifferentiableAt ℝ u (X (T / 2, θ))) :
    n04bRootUnknown T (-1) X A u (n04bRootCutRadius T, θ) =
        n04bRootUnknown T 1 X A u (n04bRootCutRadius T, θ) ∧
      radialPartial (n04bRootUnknown T (-1) X A u) (n04bRootCutRadius T, θ) =
        -radialPartial (n04bRootUnknown T 1 X A u) (n04bRootCutRadius T, θ) -
          n04bRootUnknown T 1 X A u (n04bRootCutRadius T, θ) /
            (2 * n04bRootCutRadius T) := by
  have hp : ∀ᶠ p : PolarPoint in 𝓝 (n04bRootCutRadius T, θ), 0 < p.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds
      (n04bRootCutRadius_pos hT)
  have he (s : ℝ) : n04bRootUnknown T s X A u =ᶠ[𝓝 (n04bRootCutRadius T, θ)]
      n04bGaugedTravel T s n04bRootTravel n04bRootGauge (n04bTravelUnknown X A u) := by
    filter_upwards [hp] with p hp
    exact n04bRootUnknown_eq_gauged T s X A u hp
  have hv (s : ℝ) := (he s).self_of_nhds
  have hd (s : ℝ) :
      radialPartial (n04bRootUnknown T s X A u) (n04bRootCutRadius T, θ) =
        radialPartial
          (n04bGaugedTravel T s n04bRootTravel n04bRootGauge (n04bTravelUnknown X A u))
          (n04bRootCutRadius T, θ) := by
    unfold radialPartial
    rw [(he s).fderiv_eq]
  simpa only [hv (-1), hv 1, hd (-1), hd 1] using
    (n04b_root_gauged_transmission hT θ (n04bTravelUnknown X A u)
      (n04bTravelUnknown_differentiableAt hX hA hA0 hu))

end ContinuousFlexibility.Analysis
