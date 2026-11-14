module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowTranslationBounds
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp

/-!
# Uniform constants for circle flow families

The explicit constants in the actual circle-flow estimates are continuous
functions of their low integrated speed norms. A compact range of those
low norms therefore gives one constant for every member of a family.
The high-order norm remains a linear factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

private theorem n04_continuous_circleFlowJetBound (n : ℕ) :
    Continuous (circleFlowJetBound n) := by
  induction n with
  | zero =>
      simpa only [circleFlowJetBound] using
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  | succ n ih =>
      simp only [circleFlowJetBound]
      fun_prop

private theorem n04_continuous_circleLiftCompositionLowConstant
    {X : Type*} [TopologicalSpace X] (P : ℝ) (s : ℕ) {c M : X → ℝ}
    (hc : Continuous c) (hM : Continuous M) (hpos : ∀ x, 0 < c x) :
    Continuous (fun x => circleLiftCompositionLowConstant P s (c x) (M x)) := by
  have hi : Continuous (fun x => (Real.sqrt (c x))⁻¹) :=
    (Real.continuous_sqrt.comp hc).inv₀
      (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  simp only [circleLiftCompositionLowConstant, circleLiftLowBound]
  fun_prop

private theorem n04_continuous_circleLiftCompositionStepConstant
    {X : Type*} [TopologicalSpace X] (P : ℝ) (r : ℕ) {c M K : X → ℝ}
    (hc : Continuous c) (hM : Continuous M) (hK : Continuous K)
    (hpos : ∀ x, 0 < c x) :
    Continuous (fun x => circleLiftCompositionStepConstant P r (c x) (M x) (K x)) := by
  have hi : Continuous (fun x => (Real.sqrt (c x))⁻¹) :=
    (Real.continuous_sqrt.comp hc).inv₀
      (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  have hl := n04_continuous_circleLiftCompositionLowConstant P 1 hc hM hpos
  simp only [circleLiftCompositionStepConstant, circleLiftLowBound]
  fun_prop

private theorem n04_continuous_circleLiftCompositionConstant
    {X : Type*} [TopologicalSpace X] (P : ℝ) (s : ℕ) {c M : X → ℝ}
    (hc : Continuous c) (hM : Continuous M) (hpos : ∀ x, 0 < c x) :
    Continuous (fun x => circleLiftCompositionConstant P (c x) (M x) s) := by
  induction s with
  | zero =>
      simpa only [circleLiftCompositionConstant] using
        n04_continuous_circleLiftCompositionLowConstant P 0 hc hM hpos
  | succ n ih =>
      by_cases hn : n ≤ 2
      · simpa only [circleLiftCompositionConstant, if_pos hn] using
          n04_continuous_circleLiftCompositionLowConstant P (n + 1) hc hM hpos
      · simp only [circleLiftCompositionConstant, if_neg hn]
        exact continuous_const.max
          (n04_continuous_circleLiftCompositionStepConstant P (n - 3) hc hM ih hpos)

private theorem n04_continuous_circleFlowSourceConstant
    {X : Type*} [TopologicalSpace X] (P : ℝ) (s : ℕ) {c M : X → ℝ}
    (hc : Continuous c) (hM : Continuous M) (hpos : ∀ x, 0 < c x) :
    Continuous (fun x => circleFlowSourceConstant P (c x) (M x) s) := by
  have hs := n04_continuous_circleLiftCompositionConstant P s hc hM hpos
  have h1 := n04_continuous_circleLiftCompositionConstant P 1 hc hM hpos
  simp only [circleFlowSourceConstant]
  fun_prop

private theorem n04_continuous_circleFlowLowGeometryBound (P : ℝ) :
    Continuous (circleFlowLowGeometryBound P) := by
  have hj := (n04_continuous_circleFlowJetBound 4).comp
    (show Continuous (fun L : ℝ => circleSobolevEmbeddingConstant P * L) by fun_prop)
  change Continuous (fun L : ℝ =>
    16 * (circleFlowJetBound 4 (circleSobolevEmbeddingConstant P * L) + 1))
  fun_prop

/-- The actual all-order flow estimate has a continuous dependence on
the one low integrated angular speed norm appearing in its constant. -/
theorem continuous_circleFlowSobolevConstant (P : ℝ) (s : ℕ) :
    Continuous (fun L => circleFlowSobolevConstant P L s) := by
  have hc : Continuous (fun L : ℝ =>
      Real.exp (-(circleFlowEmbeddingConstant P * L))) := by fun_prop
  have hM := n04_continuous_circleFlowLowGeometryBound P
  have hs := n04_continuous_circleFlowSourceConstant P s hc hM
    (fun _ => Real.exp_pos _)
  simp only [circleFlowSobolevConstant]
  fun_prop

/-- The reference-translation estimate also depends continuously on its
two low integrated norms. The mean reference rotation is absent. -/
theorem continuous_circleFlowTranslationConstant (P : ℝ) (s : ℕ) :
    Continuous (fun z : ℝ × ℝ => circleFlowTranslationConstant P z.1 z.2 s) := by
  have hc : Continuous (fun z : ℝ × ℝ =>
      Real.exp (-(circleFlowEmbeddingConstant P * z.1))) := by fun_prop
  have hM : Continuous (fun z : ℝ × ℝ => circleFlowLowGeometryBound P z.1) :=
    (n04_continuous_circleFlowLowGeometryBound P).comp continuous_fst
  have hs := n04_continuous_circleLiftCompositionConstant P s hc hM
    (fun _ => Real.exp_pos _)
  have hh : Continuous (fun L : ℝ => circleFlowTranslationHighFactor P L s) := by
    cases s with
    | zero => simpa only [circleFlowTranslationHighFactor] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    | succ n => exact continuous_circleFlowSobolevConstant P n
  have hh' : Continuous (fun z : ℝ × ℝ => circleFlowTranslationHighFactor P z.1 s) :=
    hh.comp continuous_fst
  simp only [circleFlowTranslationConstant]
  fun_prop

/-- One constant works for every actual nonnegative low norm below the
same prescribed upper bound. -/
theorem exists_uniform_circleFlowSobolevConstant (P Lmax : ℝ) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → L ≤ Lmax →
      circleFlowSobolevConstant P L s ≤ C := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) Lmax)).bddAbove_image
    (continuous_circleFlowSobolevConstant P s).continuousOn
  refine ⟨max 1 B, le_max_left _ _, fun L hL hLm => ?_⟩
  exact (hB ⟨L, ⟨hL, hLm⟩, rfl⟩).trans (le_max_right _ _)

/-- One translation constant works on a prescribed compact rectangle
of actual low speed and low reference-difference norms. -/
theorem exists_uniform_circleFlowTranslationConstant
    (P Lmax Jmax : ℝ) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L J : ℝ, 0 ≤ L → L ≤ Lmax → 0 ≤ J → J ≤ Jmax →
      circleFlowTranslationConstant P L J s ≤ C := by
  have hcompact : IsCompact (Icc (0 : ℝ) Lmax ×ˢ Icc (0 : ℝ) Jmax) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image
    (continuous_circleFlowTranslationConstant P s).continuousOn
  refine ⟨max 1 B, le_max_left _ _, fun L J hL hLm hJ hJm => ?_⟩
  exact (hB ⟨(L, J), ⟨⟨hL, hLm⟩, ⟨hJ, hJm⟩⟩, rfl⟩).trans (le_max_right _ _)

end ContinuousFlexibility.Analysis
