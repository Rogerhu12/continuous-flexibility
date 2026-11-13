import ContinuousFlexibility.Analysis.N04NegativeHeightCurrentData
import ContinuousFlexibility.Analysis.N04RealizationPotentialRegularity

/-! Scalar identities used by the selected height-data linear operations. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

/-- Sum two coefficient-envelope bounds while preserving one common
height factor and one common state weight. -/
theorem n04NegativeHeight_add_cost {A B E H X Y W u v : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 1 ≤ E) (hH : 0 ≤ H)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXW : X ≤ W) (hYW : Y ≤ W)
    (hu : |u| ≤ A * E ^ A * H * X) (hv : |v| ≤ B * E ^ B * H * Y) :
    |u + v| ≤ (A + B) * E ^ (A + B) * H * W := by
  have hEp : 0 ≤ E ^ (A + B) := Real.rpow_nonneg (zero_le_one.trans hE) _
  have hu' : |u| ≤ A * E ^ (A + B) * H * W :=
    hu.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hB)) hA) hH)
      hXW hX (mul_nonneg (mul_nonneg hA hEp) hH))
  have hv' : |v| ≤ B * E ^ (A + B) * H * W :=
    hv.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hA)) hB) hH)
      hYW hY (mul_nonneg (mul_nonneg hB hEp) hH))
  exact ((abs_add_le u v).trans (add_le_add hu' hv')).trans_eq (by ring)

/-- The derivative of a periodic smooth field is periodic on the same
unit strip.  Only local smoothness on that strip is used. -/
theorem n04NegativeHeight_angularPartial_periodic
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f unitStrip)
    (hperiod : ∀ q ∈ unitStrip, f (q + (0, Real.pi)) = f q)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    angularPartial f (q + (0, Real.pi)) = angularPartial f q := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hs : q + (0, Real.pi) ∈ unitStrip :=
    ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
  have he : (fun y => f (y + (0, Real.pi))) =ᶠ[𝓝 q] f := by
    filter_upwards [hU.mem_nhds hq] with y hy
    exact hperiod y hy
  have hd := ((hf _ hs).contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp q ((hasFDerivAt_id q).add_const (0, Real.pi))
  have hder : fderiv ℝ f (q + (0, Real.pi)) = fderiv ℝ f q := by
    have h := hc.fderiv.symm.trans he.fderiv_eq
    simpa only [ContinuousLinearMap.comp_id] using h
  exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) hder

theorem n04NegativeHeight_angularPartial_smooth {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f unitStrip) :
    ContDiffOn ℝ ∞ (angularPartial f) unitStrip := by
  change ContDiffOn ℝ ∞ (fun p : PolarPoint => fderiv ℝ f p (0, 1)) unitStrip
  have hd : ContDiffOn ℝ ∞ (fun _ : PolarPoint => ((0, 1) : PolarPoint)) unitStrip :=
    contDiffOn_const
  exact (hf.fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) (by simp)).clm_apply hd

theorem n04NegativeHeight_mixed_add_difference
    {f g f₀ g₀ : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f unitStrip) (hg : ContDiffOn ℝ ∞ g unitStrip)
    (hf₀ : ContDiffOn ℝ ∞ f₀ unitStrip) (hg₀ : ContDiffOn ℝ ∞ g₀ unitStrip)
    (i j : ℕ) {q : PolarPoint} (hq : q ∈ unitStrip) :
    mixedDerivative i j (fun y => (f y + g y) - (f₀ y + g₀ y)) q =
      mixedDerivative i j (fun y => f y - f₀ y) q +
        mixedDerivative i j (fun y => g y - g₀ y) q := by
  have heq : (fun y => (f y + g y) - (f₀ y + g₀ y)) =
      (fun y => (f y - f₀ y) + (g y - g₀ y)) := by
    funext y
    ring
  rw [heq]
  exact n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
    (hf.sub hf₀) (hg.sub hg₀) i j hq

theorem n04NegativeHeight_mixed_angular_difference
    {f f₀ : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f unitStrip) (hf₀ : ContDiffOn ℝ ∞ f₀ unitStrip)
    (i j : ℕ) {q : PolarPoint} (hq : q ∈ unitStrip) :
    mixedDerivative i j (fun y => angularPartial f y - angularPartial f₀ y) q =
      mixedDerivative i (j + 1) (fun y => f y - f₀ y) q := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  calc
    _ = mixedDerivative i j (angularPartial f) q -
        mixedDerivative i j (angularPartial f₀) q :=
      mixedDerivative_sub_of_contDiffOn hU
        (n04NegativeHeight_angularPartial_smooth hf) (n04NegativeHeight_angularPartial_smooth hf₀) i j hq
    _ = mixedDerivative i (j + 1) f q - mixedDerivative i (j + 1) f₀ q :=
      congrArg₂ (fun x y : ℝ => x - y)
        (mixedDerivative_angularPartial hU hf i j hq)
        (mixedDerivative_angularPartial hU hf₀ i j hq)
    _ = _ := (mixedDerivative_sub_of_contDiffOn hU hf hf₀ i (j + 1) hq).symm

/-- Reassociate the one angular derivative in a scalar weight index. -/
theorem n04NegativeHeight_angular_loss_bound
    (w : ℕ → ℝ) (C : ℝ) (s loss : ℕ) {x : ℝ}
    (h : |x| ≤ C * w ((s + 1) + loss)) :
    |x| ≤ C * w (s + (loss + 1)) := by
  have he : (s + 1) + loss = s + (loss + 1) := by omega
  simpa only [he] using h

theorem n04NegativeHeight_mixed_self_sub_zero
    (f : PolarPoint → ℝ) (i j : ℕ) (q : PolarPoint) :
    mixedDerivative i j (fun y => f y - f y) q = 0 := by
  simp only [sub_self, mixedDerivative_fun_zero]

theorem n04NegativeHeight_zero_bound {x B : ℝ} (hx : x = 0) (hB : 0 ≤ B) :
    |x| ≤ B := (congrArg abs hx).trans_le (abs_zero.trans_le hB)

/-- The chosen zero tower vanishes at every parameter order. -/
theorem n04NegativeHeight_zeroTower_apply
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} (hU : IsOpen U) (k : ℕ) (z : X) (hz : z ∈ U)
    (v : Fin k → X) :
    (smoothDirections_constant hU (0 : ℝ)).D k z v = 0 := by
  by_cases hk : k = 0
  · subst k
    exact smoothDirections_D_zero_apply _ hz v
  · exact smoothDirections_D_constant _ (Nat.pos_of_ne_zero hk) hz v

end ContinuousFlexibility.Analysis
