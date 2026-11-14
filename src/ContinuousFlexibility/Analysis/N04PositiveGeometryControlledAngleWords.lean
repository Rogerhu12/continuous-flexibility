import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledAngularKernel
import ContinuousFlexibility.Analysis.N04PositiveGeometrySampledPlaneKernel

/-!
# Saved positive words of the actual angular interpolation

The bounded packet contains the angular defect, while the unwrapped
angle is added through its fixed linear tower. Every estimate refers to
the selected width and the original component sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

variable {V : Type*}
  [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem n04PositiveGeometry_controlledAngle_saved_word_bound
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (N : ℕ) (A RH : ℝ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (U : Set V), IsOpen U →
      ∀ state : V → AnnularState W.S × ℝ,
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      ∀ J : SmoothDirections (U ×ˢ univ)
        (fun z : V × ℝ => G.toN04PositiveGeometryControlData.angularCoefficients
          (state z.1) i z.2),
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun z : V × PolarPoint => G.toN04PositiveGeometryControlData.angle (state z.1) i z.2),
      ∀ (p q : Seminorm ℝ V) (R H t : ℝ), 0 ≤ R → 0 ≤ H → H ≤ RH → 1 ≤ t →
      ∀ (K s shift : ℕ) (x : V), x ∈ U → ∀ y : PolarPoint, y.1 ∈ Icc W.D.a W.D.b →
      N04BoundaryWordBounds J K (s + K) 1 x y.2
        (fun a => p a ≤ 1 ∧ q a ≤ R) (A * W.U.E0 (W.U.sample (X.cell i)) ^ A) H t shift →
      ∀ j : ℕ, 0 < j → j ≤ N → j ≤ K + s + 1 →
      ∀ w : StateAngleWord j, w.stateArity ≤ K →
      ∀ v : Fin j → V × PolarPoint,
      (∀ k, if w.isState k then (v k).2 = 0 else (v k).1 = 0) →
      (∀ k, p (v k).1 ≤ 1 ∧ q (v k).1 ≤ R ∧ ‖(v k).2‖ ≤ 1) →
        ‖Q.D j (x, y) v‖ ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
          parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) := by
  let I := N04PositiveComponent W.D.a W.D.b (deriv W.D.w)
  let E : I → ℝ := fun i => W.U.E0 (W.U.sample (X.cell i))
  have hE (i : I) : 1 ≤ E i := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  let Ω : I → Set (N04PositiveRadialCoefficients (n + 1) × ℝ) :=
    fun i => {z | ‖z.1‖ ≤ A * E i ^ A ∧ z.2 ∈ Icc W.D.a W.D.b}
  let g := G.toN04PositiveGeometryControlData.angularKernel
  have hg (i : I) : ContDiff ℝ ∞ (g i) :=
    n04PositiveGeometry_angularKernel_contDiff _ _ _ _
  have hkernel (j : ℕ) (_hj : j ≤ N) : ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧
      ∀ i z, z ∈ Ω i → ‖iteratedFDeriv ℝ j (g i) z‖ ≤ C * E i ^ P := by
    obtain ⟨C, P, hC, hP, hb⟩ := n04PositiveGeometry_controlled_angularKernel_bounds G hA j
    exact ⟨C, P, hC.le, hP, fun i z hz => hb i z.1 hz.1 z.2 hz.2⟩
  obtain ⟨B₀, hB₀, hbound⟩ := n04PositiveGeometry_sampledPlaneKernel_saved_prefix
    (E := V) E hE (fun _ => univ) Ω g (fun _ => isOpen_univ) (fun i => (hg i).contDiffOn)
    N A RH hA hkernel
  let B : ℝ := 2 * B₀
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hB₀]
  have hB₀B : B₀ ≤ B := by dsimp only [B]; linarith only [hB₀]
  refine ⟨B, hB, ?_⟩
  intro U hU state i J Q p q R H t hR hH hHR ht K s shift x hx y hy hraw
    j hj hjN hjs w hw v hpure hbox
  let f : V × ℝ → N04PositiveRadialCoefficients (n + 1) :=
    fun z => G.toN04PositiveGeometryControlData.angularCoefficients (state z.1) i z.2
  have hvalue : ‖f (x, y.2)‖ ≤ A * E i ^ A := by
    have hh := hraw 0 .nil (Nat.zero_le _) (Nat.zero_le _) Fin.elim0
      ⟨fun k => k.elim0, fun k => k.elim0⟩ (fun k => k.elim0)
    simpa only [J.zero (x, y.2) ⟨hx, mem_univ _⟩, StateAngleWord.stateArity,
      StateAngleWord.angleArity, Nat.zero_sub, Nat.mul_zero, Nat.add_zero,
      parameterHeightWeight, ite_true, pow_zero, mul_one] using hh
  let JP := n04PositiveGeometry_coefficientPacketDirections hU J
  let JK := smoothDirections_contDiff_comp JP isOpen_univ (hg i).contDiffOn
    (fun _ _ => mem_univ _)
  have hk := hbound U hU f J i (fun _ _ => mem_univ _) JK p q R H t hR hH hHR ht
    K s shift x hx y ⟨hvalue, hy⟩ hraw j hj hjN hjs w hw v hpure hbox
  let L : (V × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ V PolarPoint)
  let Jθ : SmoothDirections (U ×ˢ univ) (fun z : V × PolarPoint => z.2.2) :=
    (smoothDirectionsLinearOn L (hU.prod isOpen_univ)).congrOn
      (fun z _ => by simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'])
  have hM : 1 ≤ B₀ * E i ^ B₀ := one_le_mul_of_one_le_of_one_le hB₀
    (Real.one_le_rpow (hE i) (zero_le_one.trans hB₀))
  have hθ := n04PositiveGeometry_spatialLinear_saved_word_bound (hU.prod isOpen_univ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) Jθ hM
    ((ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ).trans hM) hH ht hj w (shift + 1)
    (x, y) ⟨hx, mem_univ _⟩ v (fun k => (hbox k).2.2)
    (fun k h => by simpa only [h, ite_true] using hpure k)
  have hh := n04PositiveGeometry_jointAdd_word_bound Jθ JK Q
    (fun z _ => G.toN04PositiveGeometryControlData.angle_eq_angularKernel (state z.1) i z.2)
    j (x, y) ⟨hx, mem_univ _⟩ v hθ hk
  have hcost : 2 * (B₀ * E i ^ B₀) ≤ B * E i ^ B := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hE i) hB₀B) (zero_le_one.trans hB)
  calc
    ‖Q.D j (x, y) v‖ ≤
        (2 * (B₀ * E i ^ B₀)) * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) := hh.trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _)

end ContinuousFlexibility.Analysis
