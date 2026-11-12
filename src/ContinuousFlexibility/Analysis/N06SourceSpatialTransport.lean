import ContinuousFlexibility.Analysis.N06NuSpatialCalculus
import ContinuousFlexibility.Analysis.N06CurrentSourceJets

/-!
# Quantitative transport by the actual inverse-chart vector field

The source recursion already used by CurrentSourceJets is estimated from
spatial derivatives of its two genuine geometric coefficients:
H / |det DF| and adj(DF) e_theta / det DF. No derivative or boundary value
of a totalized inverse chart is involved. A uniform bound for these
coefficients is an explicit geometric input; qualitative N04 smoothness
alone does not assert such a bound before the current state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

theorem n06_norm_iteratedFDeriv_vectorField_le
    {U : Set PolarPoint} {f : PolarPoint → ℝ} {X : PolarPoint → PolarPoint}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hX : ContDiffOn ℝ ∞ X U)
    (n : ℕ) {x : PolarPoint} (hx : x ∈ U) {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hfbound : ∀ k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k f x‖ ≤ R)
    (hXbound : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k X x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (X y)) x‖ ≤ (2 : ℝ) ^ n * B * R := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  let A : (PolarPoint →L[ℝ] ℝ) →L[ℝ] PolarPoint →L[ℝ] ℝ :=
    ContinuousLinearMap.id ℝ (PolarPoint →L[ℝ] ℝ)
  have hA : ‖A‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h := A.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hd hX hU.uniqueDiffOn
    hx (n := n) (by simp) hA
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at h
  change ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (X y)) x‖ ≤
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fderiv ℝ f) x‖ * ‖iteratedFDeriv ℝ (n - i) X x‖ at h
  refine h.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * R * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hdf : ‖iteratedFDeriv ℝ i (fderiv ℝ f) x‖ ≤ R := by
        rw [norm_iteratedFDeriv_fderiv]
        exact hfbound (i + 1) (by have := Finset.mem_range.mp hi; omega)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hdf (Nat.cast_nonneg _))
        (hXbound (n - i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hR)
    _ = (2 : ℝ) ^ n * B * R := by
      have hs : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [← Finset.sum_mul, ← Finset.sum_mul, hs]
      ring

def n06SpatialSourceTransportCost (n : ℕ) (B : ℝ) : ℝ :=
  (1 + (2 : ℝ) ^ n * B) ^ (n + 1)

theorem n06SpatialSourceTransportCost_nonneg (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ n06SpatialSourceTransportCost n B := by
  exact pow_nonneg (add_nonneg zero_le_one (mul_nonneg (by positivity) hB)) _

/-- At a fixed physical point the existing actual source recursion
preserves the source's linear small factor. Its geometric inputs are
ordinary spatial jets of the forward-chart weight and adjugate field. -/
theorem n06PhysicalSourceAngularJet_spatial_bound
    {U : Set PolarPoint} {F : PolarPoint → PolarPoint} {H f : PolarPoint → ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hH : ContDiffOn ℝ ∞ H U)
    (hJ : ∀ x ∈ U, planeJacobian F x ≠ 0) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {x : PolarPoint} (hx : x ∈ U) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hweight : ∀ k, k ≤ n →
      ‖iteratedFDeriv ℝ k (fun y => H y / |planeJacobian F y|) x‖ ≤ B)
    (hvector : ∀ k, k ≤ n →
      ‖iteratedFDeriv ℝ k (n06InverseChartVector F (0, 1)) x‖ ≤ B)
    (hsource : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ R) :
    ∀ j, j ≤ n → |n06PhysicalSourceAngularJet F H f j x| ≤
      n06SpatialSourceTransportCost n B * R := by
  let A : PolarPoint → ℝ := fun y => H y / |planeJacobian F y|
  let X : PolarPoint → PolarPoint := n06InverseChartVector F (0, 1)
  let C : ℝ := 1 + (2 : ℝ) ^ n * B
  have hC : 1 ≤ C := le_add_of_nonneg_right (mul_nonneg (by positivity) hB)
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hAs : ContDiffOn ℝ ∞ A U := by
    intro y hy
    have h : ContDiffWithinAt ℝ ∞
        (n06PhysicalSourceAngularJet F H (fun _ => (1 : ℝ)) 0) U y :=
      (n06PhysicalSourceAngularJet_contDiffAt
      (hF.contDiffAt (hU.mem_nhds hy)) (hH.contDiffAt (hU.mem_nhds hy))
      (hJ y hy) (contDiffAt_const (c := (1 : ℝ))) 0).contDiffWithinAt
    simpa only [A, n06PhysicalSourceAngularJet, mul_one] using h
  have hXs : ContDiffOn ℝ ∞ X U := by
    intro y hy
    exact (n06InverseChartVector_contDiffAt (0, 1)
      (hF.contDiffAt (hU.mem_nhds hy)) (hJ y hy)).contDiffWithinAt
  have hjet (j : ℕ) : ContDiffOn ℝ ∞ (n06PhysicalSourceAngularJet F H f j) U := by
    intro y hy
    exact (n06PhysicalSourceAngularJet_contDiffAt
      (hF.contDiffAt (hU.mem_nhds hy)) (hH.contDiffAt (hU.mem_nhds hy))
      (hJ y hy) (hf.contDiffAt (hU.mem_nhds hy)) j).contDiffWithinAt
  have hpower (k : ℕ) (hk : k ≤ n) : (2 : ℝ) ^ k * B ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hB).trans
      (le_add_of_nonneg_left zero_le_one)
  have hbound (j : ℕ) : ∀ k, j + k ≤ n →
      ‖iteratedFDeriv ℝ k (n06PhysicalSourceAngularJet F H f j) x‖ ≤ C ^ (j + 1) * R := by
    induction j with
    | zero =>
      intro k hk
      have he : n06PhysicalSourceAngularJet F H f 0 = (fun y => A y * f y) := by
        funext y
        simp only [n06PhysicalSourceAngularJet, A, div_eq_mul_inv]
        ring
      rw [he]
      have hk' : k ≤ n := by omega
      have h := n06_norm_iteratedFDeriv_mul_le hU hAs hf k hx hB hR
        (fun i hi => hweight i (hi.trans hk')) (fun i hi => hsource i (hi.trans hk'))
      simpa only [zero_add, pow_one] using h.trans
        (mul_le_mul_of_nonneg_right (hpower k hk') hR)
    | succ j ih =>
      intro k hk
      have hk' : k ≤ n := by omega
      have hsize : 0 ≤ C ^ (j + 1) * R := mul_nonneg (pow_nonneg hC₀ _) hR
      have h := n06_norm_iteratedFDeriv_vectorField_le hU (hjet j) hXs k hx hsize hB
        (fun i hi => ih i (by omega)) (fun i hi => hvector i (hi.trans hk'))
      change ‖iteratedFDeriv ℝ k (n06PhysicalSourceAngularJet F H f (j + 1)) x‖ ≤
        (2 : ℝ) ^ k * B * (C ^ (j + 1) * R) at h
      exact h.trans ((mul_le_mul_of_nonneg_right (hpower k hk') hsize).trans_eq (by
        rw [pow_succ C (j + 1)]
        ring))
  intro j hj
  have h := hbound j 0 (by simpa only [add_zero] using hj)
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  change |n06PhysicalSourceAngularJet F H f j x| ≤ C ^ (n + 1) * R
  exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (by omega)) hR)

end ContinuousFlexibility.Analysis
