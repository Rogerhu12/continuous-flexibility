module

public import ContinuousFlexibility.Analysis.N04PulledFieldsJointTransportPower
public import ContinuousFlexibility.Analysis.N04PulledFieldsPowerGrowthMono

/-!
# Fixed-base growth of the actual transported velocity

The transported displacement is used twice in the radial system. Its
bounded height is absorbed in the drift, while the second copy retains
one full height factor in the velocity. Three independent low orders
are combined before any parameter order is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

/-- Actual radial transport preserves the height-weighted mixed growth
with one common low grading for all parameter orders. -/
theorem n04PulledFields_actualTransport_fixedBase_growth
    (p : ℕ → Seminorm ℝ E) (W H : I → ℝ)
    (hp : Monotone p) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    (KH : ℝ) (hKH : 0 ≤ KH) (hheight : ∀ i, H i ≤ KH)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    {fL fC fA fZ fV : I → E × PolarPoint → ℝ}
    (JL : ∀ i, SmoothDirections (U ×ˢ V i) (fL i))
    (JC : ∀ i, SmoothDirections (U ×ˢ V i) (fC i))
    (JA : ∀ i, SmoothDirections (U ×ˢ V i) (fA i))
    (JZ : ∀ i, SmoothDirections (U ×ˢ V i) (fZ i))
    (JV : ∀ i, SmoothDirections (U ×ˢ V i) (fV i))
    (hL : ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsMixedPowerGrowth p W (fun _ => 1) JL K B highLoss shift)
    (hC : ∀ n a b, ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U → ∀ w, ∀ y ∈ V i,
        |jointMixedDiagonal (JC i) n a b x w y| ≤ C * W i ^ P)
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
        -((fL i (x, y) + fC i (x, y) * fA i (x, y) * fZ i (x, y)) *
          angularPartial (fun q => fZ i (x, q)) y))
    (hVeq : ∀ i, EqOn (fun x => fC i x * fA i x * fZ i x) (fV i) (U ×ˢ V i)) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ loss : ℕ, FlatMixedDiagonalGrowth p W H JV K B loss := by
  obtain ⟨BL, hL⟩ := hL
  obtain ⟨BA, hA⟩ := hA
  obtain ⟨BZ, hZ⟩ := hZ
  let B := BL + BA + BZ
  refine ⟨B, fun K => ?_⟩
  obtain ⟨LL, sL, hL⟩ := hL K
  obtain ⟨LA, sA, hA⟩ := hA K
  obtain ⟨LZ, sZ, hZ⟩ := hZ K
  let highLoss := LL + LA + LZ
  let shift := sL + sA + sZ
  have hL' : N04PulledFieldsMixedPowerGrowth p W (fun _ => 1)
      JL K B highLoss shift :=
    hL.mono hp hW (fun _ => zero_le_one) (by dsimp only [B]; omega)
      (by dsimp only [highLoss]; omega) (by dsimp only [shift]; omega)
  have hA' : N04PulledFieldsAngularPowerGrowth p W (fun _ => 1)
      JA K B highLoss shift :=
    hA.mono hp hW (fun _ => zero_le_one) (by dsimp only [B]; omega)
      (by dsimp only [highLoss]; omega) (by dsimp only [shift]; omega)
  have hZ' : N04PulledFieldsAngularPowerGrowth p W H JZ K B highLoss shift :=
    hZ.mono hp hW hH (by dsimp only [B]; omega)
      (by dsimp only [highLoss]; omega) (by dsimp only [shift]; omega)
  have hZ0 := hZ'.unweight hW hKH hheight
  let Jpair : ∀ (_ : Fin 2) i, SmoothDirections (U ×ˢ V i) (fZ i) := fun _ => JZ
  have hpair (c : Fin 2) : N04PulledFieldsAngularPowerGrowth p W
      (fun i => H i ^ c.val) (Jpair c) K B highLoss shift := by
    fin_cases c
    · simpa only [Fin.val_zero, pow_zero, Jpair] using hZ0
    · simpa only [Fin.val_one, pow_one, Jpair] using hZ'
  have hvel := n04PulledFields_jointTransport_parameterPowerGrowth
    (fZ := fun _ => fZ) p W H hW hH hU hV hc JL JC JA Jpair
    K B highLoss shift hL' hC hA' hpair hAr (fun _ => hZr) (1 : Fin 2)
  have hflat : FlatMixedDiagonalGrowth p W H
      (fun i => ((JC i).mul (JA i)).mul (JZ i))
      K B (highLoss + shift * K) := by
    simpa only [Fin.val_one, pow_one, Jpair] using
      hvel.flat hW (fun i => pow_nonneg (hH i) (1 : Fin 2).val)
  exact ⟨highLoss + shift * K, hflat.congr JV hV hVeq⟩

end ContinuousFlexibility.Analysis
