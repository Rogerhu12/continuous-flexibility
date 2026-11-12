import ContinuousFlexibility.Analysis.OneHighCircleFlowSobolevBounds
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform numerical constants for bounded circle-flow geometry

The explicit constants depend continuously on their scalar geometry
parameter. Their values on a fixed compact interval therefore have one
positive upper bound, independently of the state or component.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

private theorem n01c_continuous_inverse_sqrt
    {X : Type*} [TopologicalSpace X] {c : X → ℝ}
    (hc : Continuous c) (hcpos : ∀ x, 0 < c x) :
    Continuous (fun x => (Real.sqrt (c x))⁻¹) :=
  (Real.continuous_sqrt.comp hc).inv₀ (fun x => (Real.sqrt_pos.mpr (hcpos x)).ne')

private theorem n01c_continuous_liftLowBound
    {X : Type*} [TopologicalSpace X] (P : ℝ) {M : X → ℝ}
    (hM : Continuous M) :
    Continuous (fun x => circleLiftLowBound P (M x)) :=
  continuous_const.mul (continuous_const.add hM)

private theorem n01c_continuous_liftCompositionLowConstant
    {X : Type*} [TopologicalSpace X] (P : ℝ) (s : ℕ) {c M : X → ℝ}
    (hc : Continuous c) (hM : Continuous M) (hcpos : ∀ x, 0 < c x) :
    Continuous (fun x => circleLiftCompositionLowConstant P s (c x) (M x)) := by
  have hlow := n01c_continuous_liftLowBound P hM
  have hsum : Continuous (fun x => ∑ q : OrderedFinpartition s,
      circleLiftLowBound P (M x) ^ q.length) :=
    continuous_finsetSum _ (fun q _ => hlow.pow q.length)
  exact continuous_const.max
    ((continuous_const.mul (n01c_continuous_inverse_sqrt hc hcpos)).mul
      (continuous_const.add hsum))

private theorem n01c_continuous_liftCompositionStepConstant
    {X : Type*} [TopologicalSpace X] (P : ℝ) (r : ℕ) {c M K : X → ℝ}
    (hc : Continuous c) (hM : Continuous M) (hK : Continuous K)
    (hcpos : ∀ x, 0 < c x) :
    Continuous (fun x => circleLiftCompositionStepConstant P r (c x) (M x) (K x)) := by
  have hlow := n01c_continuous_liftLowBound P hM
  have hcomp := n01c_continuous_liftCompositionLowConstant P 1 hc hM hcpos
  exact continuous_const.mul
    ((n01c_continuous_inverse_sqrt hc hcpos).add
      (continuous_const.mul
        (((hK.mul hlow).mul (continuous_const.add hM)).add
          (continuous_const.mul hcomp))))

private theorem n01c_continuous_liftCompositionConstant
    {X : Type*} [TopologicalSpace X] (P : ℝ) {c M : X → ℝ}
    (hc : Continuous c) (hM : Continuous M) (hcpos : ∀ x, 0 < c x) (s : ℕ) :
    Continuous (fun x => circleLiftCompositionConstant P (c x) (M x) s) := by
  induction s with
  | zero =>
      exact n01c_continuous_liftCompositionLowConstant P 0 hc hM hcpos
  | succ n ih =>
      by_cases hn : n ≤ 2
      · simpa only [circleLiftCompositionConstant, if_pos hn] using
          n01c_continuous_liftCompositionLowConstant P (n + 1) hc hM hcpos
      · simpa only [circleLiftCompositionConstant, if_neg hn] using
          (continuous_const.max
            (n01c_continuous_liftCompositionStepConstant P (n - 3) hc hM ih hcpos))

private theorem n01c_continuous_flowSourceConstant
    {X : Type*} [TopologicalSpace X] (P : ℝ) {c M : X → ℝ}
    (hc : Continuous c) (hM : Continuous M) (hcpos : ∀ x, 0 < c x) (s : ℕ) :
    Continuous (fun x => circleFlowSourceConstant P (c x) (M x) s) := by
  have hs := n01c_continuous_liftCompositionConstant P hc hM hcpos s
  have h1 := n01c_continuous_liftCompositionConstant P hc hM hcpos 1
  exact continuous_const.max
    (((continuous_const.add (continuous_const.mul hM)).mul hs).add
      ((continuous_const.mul h1).mul (continuous_const.add hM)))

theorem n01c_continuous_circleFlowJetBound (n : ℕ) :
    Continuous (circleFlowJetBound n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      exact ih.add
        ((continuous_const.add
          ((continuous_const.mul (ih.pow (n + 1))).mul continuous_id)).mul
            (Real.continuous_exp.comp (continuous_const.mul continuous_id)))

theorem n01c_continuous_circleFlowLowGeometryBound (P : ℝ) :
    Continuous (circleFlowLowGeometryBound P) := by
  have hJ : Continuous (fun L : ℝ =>
      circleFlowJetBound 4 (circleSobolevEmbeddingConstant P * L)) :=
    (n01c_continuous_circleFlowJetBound 4).comp (continuous_const.mul continuous_id)
  exact continuous_const.mul (hJ.add continuous_const)

theorem n01c_continuous_circleFlowSobolevConstant (P : ℝ) (s : ℕ) :
    Continuous (fun L => circleFlowSobolevConstant P L s) := by
  let c : ℝ → ℝ := fun L => Real.exp (-(circleFlowEmbeddingConstant P * L))
  let M : ℝ → ℝ := circleFlowLowGeometryBound P
  have hc : Continuous c :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hM : Continuous M := n01c_continuous_circleFlowLowGeometryBound P
  have hcpos : ∀ L, 0 < c L := fun L => Real.exp_pos _
  let K : ℝ → ℝ := fun L => (2 : ℝ) ^ (s + 1) *
    circleFlowSourceConstant P (c L) (M L) s
  have hK : Continuous K :=
    continuous_const.mul (n01c_continuous_flowSourceConstant P hc hM hcpos s)
  exact hK.mul (Real.continuous_exp.comp (hK.mul continuous_id))

private theorem n01c_exists_uniform_bound_on_Icc
    {f : ℝ → ℝ} (hf : Continuous f) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ L ∈ Icc (0 : ℝ) M, f L ≤ K := by
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) M)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), fun L hL => ?_⟩
  have hb : |f L| ≤ B := by simpa only [Real.norm_eq_abs] using hB L hL
  exact (le_abs_self (f L)).trans (hb.trans (le_max_right _ _))

/-- The flow Sobolev constant is uniform for all low geometry in one
fixed compact range; the bound may depend on the spatial order. -/
theorem exists_circleFlowSobolevConstant_uniform (P M : ℝ) (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ L ∈ Icc (0 : ℝ) M,
      circleFlowSobolevConstant P L s ≤ K :=
  n01c_exists_uniform_bound_on_Icc (n01c_continuous_circleFlowSobolevConstant P s) M

theorem exists_circleFlowLowGeometryBound_uniform (P M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ L ∈ Icc (0 : ℝ) M,
      circleFlowLowGeometryBound P L ≤ K :=
  n01c_exists_uniform_bound_on_Icc (n01c_continuous_circleFlowLowGeometryBound P) M

end ContinuousFlexibility.Analysis
