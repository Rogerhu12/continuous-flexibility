module

public import ContinuousFlexibility.Analysis.RootScaledJacobianBounds
public import ContinuousFlexibility.Analysis.RootChartExtensionGeometry
public import ContinuousFlexibility.Geometry.EuclideanRigidity

/-!
# The genuine root Jacobian lower bound includes the root

The known interior formula gives one lower bound on the open band.
Ordinary smoothness of the same extended chart at each closed-band
point extends that bound to both edges, without changing its constant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem rootScaledJacobian_lower_closed_band
    {d c : PolarPoint → ℝ} {δ τ Λ κ uχ ρ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hcontrol : N04FlowAngularControl (rootRescaledField d c δ) Λ)
    (hh : ContDiff ℝ ∞ h) (hhperiod : ∀ θ, h (θ + Real.pi) = h θ + Real.pi)
    (hhbounds : ∀ θ, deriv h θ ∈ Icc (1 / 4 : ℝ) 4)
    (hδ : 0 < δ) (hτpos : 0 < τ) (hτ : |τ| ≤ 1) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hcvalue : ∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) ρ → κ ≤ c (δ * q.1, q.2))
    (hχvalue : ∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) ρ →
      0 < extendedRootOddCoefficient (rootScaledInverseCoordinate Θ h τ) q ∧
      extendedRootOddCoefficient (rootScaledInverseCoordinate Θ h τ) q ≤ uχ) :
    let J₀ := ((δ * τ) * κ) * (Real.exp (-Λ) / 4) ^ 2 /
      Real.sqrt (((3 / 2 : ℝ) * uχ) ^ (2 / 3 : ℝ))
    0 < J₀ ∧ ∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) ρ →
      J₀ ≤ planeJacobian (extendedRootEvenOddChart (rootScaledInverseCoordinate Θ h τ)) q := by
  let G := rootScaledInverseCoordinate Θ h τ
  have hzero := hχvalue (0, 0) ⟨le_rfl, hρ.le⟩
  have hu : 0 < uχ := hzero.1.trans_le hzero.2
  have hpositive : 0 < ((δ * τ) * κ) * (Real.exp (-Λ) / 4) ^ 2 /
      Real.sqrt (((3 / 2 : ℝ) * uχ) ^ (2 / 3 : ℝ)) :=
    div_pos (mul_pos (mul_pos (mul_pos hδ hτpos) hκ)
      (pow_pos (div_pos (Real.exp_pos _) (by norm_num)) 2))
      (Real.sqrt_pos.mpr (Real.rpow_pos_of_pos (mul_pos (by norm_num) hu) _))
  refine ⟨hpositive, ?_⟩
  intro q hq
  have hG := rootScaledInverseCoordinate_regular hd hc hdperiod hcperiod hΘ hh hhperiod τ
  have hχperiod : ∀ r, 0 ≤ r →
      Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hG.2 r
  have hφperiod : ∀ r, 0 ≤ r → ∀ θ,
      rootEven G (r, θ + Real.pi) = rootEven G (r, θ) + Real.pi :=
    fun r _ θ => rootEven_period_add hG.2 r θ
  have hchart := contDiffAt_extendedRootEvenOddChart_of_ne_zero hG.1 Real.pi_ne_zero
    hχperiod hφperiod (hχvalue q hq).1.ne'
  let U : Set PolarPoint := Ioo (0 : ℝ) ρ ×ˢ (univ : Set ℝ)
  have hclosure : q ∈ closure U := by
    dsimp only [U]
    rw [closure_prod_eq, closure_Ioo hρ.ne, closure_univ]
    exact ⟨hq, mem_univ _⟩
  have : NeBot (𝓝[U] q) := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hlim : Tendsto (planeJacobian (extendedRootEvenOddChart G)) (𝓝[U] q)
      (𝓝 (planeJacobian (extendedRootEvenOddChart G) q)) :=
    (contDiffAt_planeJacobian hchart).continuousAt.continuousWithinAt
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyclosed : y.1 ∈ Icc (0 : ℝ) ρ := ⟨hy.1.1.le, hy.1.2.le⟩
  exact (rootScaledJacobian_uniform_lower hd hc hdperiod hcperiod hΘ hcontrol hh hhperiod
    hhbounds hδ hτpos hτ hκ ⟨hy.1.1, hy.1.2.le.trans hρone⟩ y.2
      (hcvalue y hyclosed) (hχvalue y hyclosed).1 (hχvalue y hyclosed).2).2

end ContinuousFlexibility.Analysis
