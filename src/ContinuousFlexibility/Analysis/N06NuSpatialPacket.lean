import ContinuousFlexibility.Analysis.N06NuSpatialCalculus
import ContinuousFlexibility.Analysis.N06NuPhysicalSmooth

/-!
# The genuine polar height packet in full spatial jets

The state-dependent part of the twelve nu coordinates is linear in the
physical height and in the two scalar parameters. Its full spatial jets
cost exactly two derivatives of that height. All reciprocal-radius
factors are controlled on the original fixed positive radial interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff BigOperators Topology

def n06NuSpatialLinearPacket (f : PolarPoint → ℝ) (q ν : ℝ)
    (p : PolarPoint) : N06NuJetCoordinates :=
  ![0, 0, 0, 0, 0, radialPartial f p, radialPartial (radialPartial f) p,
    heightAngular f p, radialPartial (heightAngular f) p,
    angularPartial (heightAngular f) p, q, ν]

theorem n06_spatial_directional_contDiffOn
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (d : PolarPoint) :
    ContDiffOn ℝ ∞ (fun p => fderiv ℝ f p d) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem n06_heightAngular_contDiffOn
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hr : ∀ p ∈ U, p.1 ≠ 0) : ContDiffOn ℝ ∞ (heightAngular f) U :=
  (n06_spatial_directional_contDiffOn hU hf (0, 1)).div contDiffOn_fst hr

theorem n06NuSpatialLinearPacket_contDiffOn
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hr : ∀ p ∈ U, p.1 ≠ 0) (q ν : ℝ) :
    ContDiffOn ℝ ∞ (n06NuSpatialLinearPacket f q ν) U := by
  have hfr := n06_spatial_directional_contDiffOn hU hf (1, 0)
  have hfrr := n06_spatial_directional_contDiffOn hU hfr (1, 0)
  have hft := n06_heightAngular_contDiffOn hU hf hr
  have hfrt := n06_spatial_directional_contDiffOn hU hft (1, 0)
  have hftt := n06_spatial_directional_contDiffOn hU hft (0, 1)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i <;>
    simp only [n06NuSpatialLinearPacket, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first
  | exact contDiffOn_const
  | exact hfr
  | exact hfrr
  | exact hft
  | exact hfrt
  | exact hftt

/-- This is the actual linearity of the five polar derivatives, on the
open set where the radius is nonzero. -/
theorem n06_polar_height_jet_sub
    {U : Set PolarPoint} {f g : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hr : ∀ p ∈ U, p.1 ≠ 0) {p : PolarPoint} (hp : p ∈ U) :
    radialPartial (fun x => f x - g x) p = radialPartial f p - radialPartial g p ∧
    radialPartial (radialPartial (fun x => f x - g x)) p =
      radialPartial (radialPartial f) p - radialPartial (radialPartial g) p ∧
    heightAngular (fun x => f x - g x) p = heightAngular f p - heightAngular g p ∧
    radialPartial (heightAngular (fun x => f x - g x)) p =
      radialPartial (heightAngular f) p - radialPartial (heightAngular g) p ∧
    angularPartial (heightAngular (fun x => f x - g x)) p =
      angularPartial (heightAngular f) p - angularPartial (heightAngular g) p := by
  have hfa (x : PolarPoint) (hx : x ∈ U) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hga (x : PolarPoint) (hx : x ∈ U) : DifferentiableAt ℝ g x :=
    (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hrad : EqOn (radialPartial (fun x => f x - g x))
      (fun x => radialPartial f x - radialPartial g x) U :=
    fun x hx => radialPartial_sub (hfa x hx) (hga x hx)
  have hangle : EqOn (heightAngular (fun x => f x - g x))
      (fun x => heightAngular f x - heightAngular g x) U := by
    intro x hx
    simp only [heightAngular, angularPartial_sub (hfa x hx) (hga x hx), sub_div]
  have her : radialPartial (fun x => f x - g x) =ᶠ[𝓝 p]
      (fun x => radialPartial f x - radialPartial g x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact hrad hx
  have het : heightAngular (fun x => f x - g x) =ᶠ[𝓝 p]
      (fun x => heightAngular f x - heightAngular g x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact hangle hx
  have hfr := ((n06_spatial_directional_contDiffOn hU hf (1, 0)).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hgr := ((n06_spatial_directional_contDiffOn hU hg (1, 0)).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hft := ((n06_heightAngular_contDiffOn hU hf hr).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hgt := ((n06_heightAngular_contDiffOn hU hg hr).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  refine ⟨hrad hp, ?_, hangle hp, ?_, ?_⟩
  · exact (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
      (her.fderiv_eq (𝕜 := ℝ))).trans (radialPartial_sub hfr hgr)
  · exact (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
      (het.fderiv_eq (𝕜 := ℝ))).trans (radialPartial_sub hft hgt)
  · exact (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1))
      (het.fderiv_eq (𝕜 := ℝ))).trans (angularPartial_sub hft hgt)

private theorem n06_norm_iteratedFDeriv_const_le
    (c : ℝ) (k : ℕ) {R : ℝ} (hR : 0 ≤ R) (hc : |c| ≤ R) (p : PolarPoint) :
    ‖iteratedFDeriv ℝ k (fun _ : PolarPoint => c) p‖ ≤ R := by
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hc
  | succ k => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using hR

private theorem n06_norm_iteratedFDeriv_radialPartial_le
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (radialPartial f) p‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f p‖ := by
  change ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ f q (1, 0)) p‖ ≤
    ‖iteratedFDeriv ℝ (n + 1) f p‖
  simpa [Prod.norm_def] using
    n06_norm_iteratedFDeriv_directional_le hU hf (1, 0) n hp

private theorem n06_norm_iteratedFDeriv_angularPartial_le
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (angularPartial f) p‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f p‖ := by
  change ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ f q (0, 1)) p‖ ≤
    ‖iteratedFDeriv ℝ (n + 1) f p‖
  simpa [Prod.norm_def] using
    n06_norm_iteratedFDeriv_directional_le hU hf (0, 1) n hp

/-- The physical packet loses exactly two spatial derivatives. All
constants are independent of the height and of its small size R. -/
theorem n06NuSpatialLinearPacket_frechet_bound
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hr : ∀ p ∈ U, p.1 ≠ 0) (n : ℕ) {p : PolarPoint} (hp : p ∈ U)
    {B R q ν : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hrecip : ∀ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun x : PolarPoint => x.1⁻¹) p‖ ≤ B)
    (hheight : ∀ k, k ≤ n + 2 → ‖iteratedFDeriv ℝ k f p‖ ≤ R)
    (hq : |q| ≤ R) (hν : |ν| ≤ R) :
    ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k (n06NuSpatialLinearPacket f q ν) p‖ ≤
      (1 + (2 : ℝ) ^ (n + 1) * B) * R := by
  have hfr : ContDiffOn ℝ ∞ (radialPartial f) U :=
    n06_spatial_directional_contDiffOn hU hf (1, 0)
  have hfa : ContDiffOn ℝ ∞ (angularPartial f) U :=
    n06_spatial_directional_contDiffOn hU hf (0, 1)
  have hft := n06_heightAngular_contDiffOn hU hf hr
  have hi : ContDiffOn ℝ ∞ (fun x : PolarPoint => x.1⁻¹) U :=
    contDiffOn_fst.inv hr
  have hrad (j : ℕ) (hj : j ≤ n + 1) :
      ‖iteratedFDeriv ℝ j (radialPartial f) p‖ ≤ R :=
    (n06_norm_iteratedFDeriv_radialPartial_le hU hf j hp).trans (hheight (j + 1) (by omega))
  have hang (j : ℕ) (hj : j ≤ n + 1) :
      ‖iteratedFDeriv ℝ j (angularPartial f) p‖ ≤ R :=
    (n06_norm_iteratedFDeriv_angularPartial_le hU hf j hp).trans (hheight (j + 1) (by omega))
  have hheightAngle (j : ℕ) (hj : j ≤ n + 1) :
      ‖iteratedFDeriv ℝ j (heightAngular f) p‖ ≤ (2 : ℝ) ^ (n + 1) * B * R := by
    have he : heightAngular f = fun x : PolarPoint => x.1⁻¹ * angularPartial f x := by
      funext x
      simp only [heightAngular, div_eq_mul_inv, mul_comm]
    rw [he]
    exact (n06_norm_iteratedFDeriv_mul_le hU hi hfa j hp hB hR
      (fun k hk => hrecip k (hk.trans hj)) (fun k hk => hang k (hk.trans hj))).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hB) hR)
  have hcost : R ≤ (1 + (2 : ℝ) ^ (n + 1) * B) * R := by
    have hnonneg := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1)) hB
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hnonneg : (1 : ℝ) ≤ 1 + (2 : ℝ) ^ (n + 1) * B) hR
  have hcost' : (2 : ℝ) ^ (n + 1) * B * R ≤
      (1 + (2 : ℝ) ^ (n + 1) * B) * R :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hR
  intro k hk
  have hrr : ‖iteratedFDeriv ℝ k (radialPartial (radialPartial f)) p‖ ≤ R :=
    (n06_norm_iteratedFDeriv_radialPartial_le hU hfr k hp).trans (hrad (k + 1) (by omega))
  have hrt : ‖iteratedFDeriv ℝ k (radialPartial (heightAngular f)) p‖ ≤
      (2 : ℝ) ^ (n + 1) * B * R :=
    (n06_norm_iteratedFDeriv_radialPartial_le hU hft k hp).trans
      (hheightAngle (k + 1) (by omega))
  have htt : ‖iteratedFDeriv ℝ k (angularPartial (heightAngular f)) p‖ ≤
      (2 : ℝ) ^ (n + 1) * B * R :=
    (n06_norm_iteratedFDeriv_angularPartial_le hU hft k hp).trans
      (hheightAngle (k + 1) (by omega))
  apply n06_norm_iteratedFDeriv_pi_le
    ((n06NuSpatialLinearPacket_contDiffOn hU hf hr q ν).contDiffAt (hU.mem_nhds hp))
    k (hR.trans hcost)
  intro i
  fin_cases i <;>
    simp only [n06NuSpatialLinearPacket, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first
  | exact (n06_norm_iteratedFDeriv_const_le 0 k hR (by simpa only [abs_zero] using hR) p).trans hcost
  | exact (hrad k (by omega)).trans hcost
  | exact hrr.trans hcost
  | exact (hheightAngle k (by omega)).trans hcost'
  | exact hrt.trans hcost'
  | exact htt.trans hcost'
  | exact (n06_norm_iteratedFDeriv_const_le q k hR hq p).trans hcost
  | exact (n06_norm_iteratedFDeriv_const_le ν k hR hν p).trans hcost

end ContinuousFlexibility.Analysis
