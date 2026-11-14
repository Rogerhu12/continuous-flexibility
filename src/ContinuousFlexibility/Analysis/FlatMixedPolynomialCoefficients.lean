module

public import ContinuousFlexibility.Analysis.FlatMixedDiagonalOperations
public import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition

/-!
# The division-free correction polynomial retains the flat factor

Each monomial contains one independent-residual velocity. The other
factors have unweighted mixed tame growth. Exact mixed products and
linear reconstruction preserve the flat weight, while allowing a fixed
loss at each fixed parameter arity. The output towers are arbitrary
genuine towers of the original two coefficient functions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

def scalarLinearCombinationDirections
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {f g : X → ℝ}
    (α β : ℝ) (J : SmoothDirections U f) (K : SmoothDirections U g) :
    SmoothDirections U (fun x => α * f x + β * g x) :=
  smoothDirectionsPostContinuousLinear (smoothDirectionsProd J K)
    (α • ContinuousLinearMap.fst ℝ ℝ ℝ + β • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem flatMixed_polynomial_coefficient_growth
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (W F : I → ℝ) (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    {a b q ed ev rd rv outB outC : I → E × PolarPoint → ℝ}
    (Ja : ∀ i, SmoothDirections (U ×ˢ V i) (a i))
    (Jb : ∀ i, SmoothDirections (U ×ˢ V i) (b i))
    (Jq : ∀ i, SmoothDirections (U ×ˢ V i) (q i))
    (Jed : ∀ i, SmoothDirections (U ×ˢ V i) (ed i))
    (Jev : ∀ i, SmoothDirections (U ×ˢ V i) (ev i))
    (Jrd : ∀ i, SmoothDirections (U ×ˢ V i) (rd i))
    (Jrv : ∀ i, SmoothDirections (U ×ˢ V i) (rv i))
    (JB : ∀ i, SmoothDirections (U ×ˢ V i) (outB i))
    (JC : ∀ i, SmoothDirections (U ×ˢ V i) (outC i))
    (hB : ∀ i x, x ∈ U → ∀ y ∈ V i,
      outB i (x, y) = -a i (x, y) * rd i (x, y))
    (hC : ∀ i x, x ∈ U → ∀ y ∈ V i,
      outC i (x, y) =
        -2 * b i (x, y) * rd i (x, y) - a i (x, y) * ed i (x, y) * rd i (x, y) +
          2 * q i (x, y) * rv i (x, y) + a i (x, y) * ev i (x, y) * rv i (x, y))
    (ha : HasFlatMixedTameGrowth p W (fun _ => 1) Ja)
    (hb : HasFlatMixedTameGrowth p W (fun _ => 1) Jb)
    (hq : HasFlatMixedTameGrowth p W (fun _ => 1) Jq)
    (hed : HasFlatMixedTameGrowth p W (fun _ => 1) Jed)
    (hev : HasFlatMixedTameGrowth p W (fun _ => 1) Jev)
    (hrd : HasFlatMixedTameGrowth p W F Jrd)
    (hrv : HasFlatMixedTameGrowth p W F Jrv) :
    HasFlatMixedTameGrowth p W F JB ∧ HasFlatMixedTameGrowth p W F JC := by
  let Ta := fun i => (Ja i).mul (Jrd i)
  let T₀ := fun i => (Jb i).mul (Jrd i)
  let Tad := fun i => (Ja i).mul (Jed i)
  let Tav := fun i => (Ja i).mul (Jev i)
  let T₁ := fun i => (Tad i).mul (Jrd i)
  let T₂ := fun i => (Jq i).mul (Jrv i)
  let T₃ := fun i => (Tav i).mul (Jrv i)
  have hTa : HasFlatMixedTameGrowth p W F Ta := by
    simpa only [one_mul] using
      HasFlatMixedTameGrowth.mul hp hI hW (fun _ => zero_le_one) hF Ta
        hU hV hc (fun _ _ _ _ _ => rfl) ha hrd
  have hT₀ : HasFlatMixedTameGrowth p W F T₀ := by
    simpa only [one_mul] using
      HasFlatMixedTameGrowth.mul hp hI hW (fun _ => zero_le_one) hF T₀
        hU hV hc (fun _ _ _ _ _ => rfl) hb hrd
  have hTad : HasFlatMixedTameGrowth p W (fun _ => 1) Tad := by
    simpa only [one_mul] using
      HasFlatMixedTameGrowth.mul hp hI hW (fun _ => zero_le_one) (fun _ => zero_le_one)
        Tad hU hV hc (fun _ _ _ _ _ => rfl) ha hed
  have hTav : HasFlatMixedTameGrowth p W (fun _ => 1) Tav := by
    simpa only [one_mul] using
      HasFlatMixedTameGrowth.mul hp hI hW (fun _ => zero_le_one) (fun _ => zero_le_one)
        Tav hU hV hc (fun _ _ _ _ _ => rfl) ha hev
  have hT₁ : HasFlatMixedTameGrowth p W F T₁ := by
    simpa only [one_mul] using
      HasFlatMixedTameGrowth.mul hp hI hW (fun _ => zero_le_one) hF T₁
        hU hV hc (fun _ _ _ _ _ => rfl) hTad hrd
  have hT₂ : HasFlatMixedTameGrowth p W F T₂ := by
    simpa only [one_mul] using
      HasFlatMixedTameGrowth.mul hp hI hW (fun _ => zero_le_one) hF T₂
        hU hV hc (fun _ _ _ _ _ => rfl) hq hrv
  have hT₃ : HasFlatMixedTameGrowth p W F T₃ := by
    simpa only [one_mul] using
      HasFlatMixedTameGrowth.mul hp hI hW (fun _ => zero_le_one) hF T₃
        hU hV hc (fun _ _ _ _ _ => rfl) hTav hrv
  constructor
  · apply HasFlatMixedTameGrowth.linear_combination hp hW hF JB hV (-1) 0
      (hJ := hTa) (hK := hTa)
    intro i x hx y hy
    rw [hB i x hx y hy]
    ring
  · let T₀₁ := fun i => scalarLinearCombinationDirections (-2) (-1) (T₀ i) (T₁ i)
    let T₂₃ := fun i => scalarLinearCombinationDirections 2 1 (T₂ i) (T₃ i)
    have hT₀₁ : HasFlatMixedTameGrowth p W F T₀₁ :=
      HasFlatMixedTameGrowth.linear_combination hp hW hF T₀₁ hV (-2) (-1)
        (fun _ _ _ _ _ => rfl) hT₀ hT₁
    have hT₂₃ : HasFlatMixedTameGrowth p W F T₂₃ :=
      HasFlatMixedTameGrowth.linear_combination hp hW hF T₂₃ hV 2 1
        (fun _ _ _ _ _ => rfl) hT₂ hT₃
    apply HasFlatMixedTameGrowth.linear_combination hp hW hF JC hV 1 1
      (hJ := hT₀₁) (hK := hT₂₃)
    intro i x hx y hy
    rw [hC i x hx y hy]
    ring

end ContinuousFlexibility.Analysis
