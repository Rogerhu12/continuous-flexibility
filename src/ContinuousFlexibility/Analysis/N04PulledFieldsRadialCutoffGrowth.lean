module

public import ContinuousFlexibility.Analysis.N04PulledFieldsActualTransportGrowth
public import ContinuousFlexibility.Analysis.JointMixedRadialScalar

/-!
# The actual radial cutoff in fixed-base transport

The cutoff contributes only its material coefficient bounds. Its
parameter-independent joint tower therefore has zero parameter charge.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

private def n04PulledFields_radialCutoffTower
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (χ : I → ℝ → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) :
    ∀ i, SmoothDirections (U ×ˢ V i) (fun x : E × PolarPoint => deriv (χ i) x.2.1) := by
  intro i
  let L : E × PolarPoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  have hd : ContDiff ℝ ∞ (deriv (χ i)) := (contDiff_infty_iff_deriv.mp (hχ i)).2
  exact (smoothDirectionsOfContDiffOn isOpen_univ hd.contDiffOn).compLinear L
    (hU.prod (hV i)) (fun _ _ => mem_univ _)

/-- The cutoff, genuine transport identities and three primitive power
families imply the fixed-base growth of the actual velocity. -/
theorem n04PulledFields_radialCutoff_fixedBase_growth
    (p : ℕ → Seminorm ℝ E) (W H : I → ℝ)
    (hp : Monotone p) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    (KH : ℝ) (hKH : 0 ≤ KH) (hheight : ∀ i, H i ≤ KH)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (χ : I → ℝ → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hcutoff : ∀ k : ℕ, ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧ ∀ i r,
      |iteratedDeriv k (χ i) r| ≤ C * W i ^ P)
    {fL fA fZ fV : I → E × PolarPoint → ℝ}
    (JL : ∀ i, SmoothDirections (U ×ˢ V i) (fL i))
    (JA : ∀ i, SmoothDirections (U ×ˢ V i) (fA i))
    (JZ : ∀ i, SmoothDirections (U ×ˢ V i) (fZ i))
    (JV : ∀ i, SmoothDirections (U ×ˢ V i) (fV i))
    (hL : ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsMixedPowerGrowth p W (fun _ => 1) JL K B highLoss shift)
    (hA : ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsAngularPowerGrowth p W (fun _ => 1) JA K B highLoss shift)
    (hZ : ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsAngularPowerGrowth p W H JZ K B highLoss shift)
    (hAr : ∀ i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fA i (x, q)) y =
        angularPartial (fun q => fL i (x, q)) y * fA i (x, y) -
          fL i (x, y) * angularPartial (fun q => fA i (x, q)) y)
    (hZr : ∀ i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fZ i (x, q)) y =
        -((fL i (x, y) + deriv (χ i) y.1 * fA i (x, y) * fZ i (x, y)) *
          angularPartial (fun q => fZ i (x, q)) y))
    (hVeq : ∀ i, EqOn (fun x => deriv (χ i) x.2.1 * fA i x * fZ i x)
      (fV i) (U ×ˢ V i)) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ loss : ℕ, FlatMixedDiagonalGrowth p W H JV K B loss := by
  let fC : I → E × PolarPoint → ℝ := fun i x => deriv (χ i) x.2.1
  let JC : ∀ i, SmoothDirections (U ×ˢ V i) (fC i) :=
    n04PulledFields_radialCutoffTower hU hV χ hχ
  have hC (n a b : ℕ) : ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U → ∀ w, ∀ y ∈ V i,
        |jointMixedDiagonal (JC i) n a b x w y| ≤ C * W i ^ P := by
    obtain ⟨C, P, hC, hP, hb⟩ := hcutoff (a + 1)
    exact ⟨C, P, hC, hP, fun i x hx w y hy =>
      jointMixedDiagonal_radial_deriv_abs_le
        (E := E) (U := U) (V := V i) (χ := χ i) (p := y)
        (K := C) (W := W i) (P := P) (JC i) hU (hV i) (hc i)
        n a b x w hx hy hC (zero_le_one.trans (hW i)) (hb i y.1)⟩
  exact n04PulledFields_actualTransport_fixedBase_growth
    p W H hp hW hH KH hKH hheight hU hV hc JL JC JA JZ JV
    hL hC hA hZ hAr hZr hVeq

end ContinuousFlexibility.Analysis
