import ContinuousFlexibility.Analysis.N06CurrentTestTraces
import ContinuousFlexibility.Analysis.N06RootTransmissionJets
import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback

/-!
# The actual root Green density from forward first jets

The closed test traces determine the actual physical test derivatives
through the forward derivative and its adjugate. Combining these identities
with the true first jets of the reconstructed finite field identifies its
physical Green flux with the existing coordinate principal density.

One arbitrary root radius, canonical endpoint, and orientation are used
throughout. No value of the totalized inverse chart at a boundary is used,
and no smoothness of the physical coefficient fields is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The true forward derivative reconstructs a covector from its two
inverse coordinate derivatives. This is an adjugate identity, valid for
the actual derivatives without extra regularity of either function. -/
theorem n06_fderiv_from_inverseChartDerivatives
    (F : PolarPoint → PolarPoint) (f : PolarPoint → ℝ) (v : PolarPoint)
    {x : PolarPoint} (hJ : planeJacobian F x ≠ 0) :
    fderiv ℝ f x v =
      (fderiv ℝ F x v).1 * n06InverseChartDerivative F (1, 0) f x +
      (fderiv ℝ F x v).2 * n06InverseChartDerivative F (0, 1) f x := by
  have h₁ : (fderiv ℝ F x v).1 =
      v.1 * (fderiv ℝ F x (1, 0)).1 + v.2 * (fderiv ℝ F x (0, 1)).1 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst'] using
      polarCLM_apply_decompose ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F x)) v
  have h₂ : (fderiv ℝ F x v).2 =
      v.1 * (fderiv ℝ F x (1, 0)).2 + v.2 * (fderiv ℝ F x (0, 1)).2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'] using
      polarCLM_apply_decompose ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (fderiv ℝ F x)) v
  rw [h₁, h₂]
  unfold n06InverseChartDerivative
  rw [polarCLM_apply_decompose (fderiv ℝ f x) v,
    polarCLM_apply_decompose (fderiv ℝ f x) (n06InverseChartVector F (1, 0) x),
    polarCLM_apply_decompose (fderiv ℝ f x) (n06InverseChartVector F (0, 1) x)]
  have hJ' : (fderiv ℝ F x (1, 0)).1 * (fderiv ℝ F x (0, 1)).2 -
      (fderiv ℝ F x (1, 0)).2 * (fderiv ℝ F x (0, 1)).1 ≠ 0 := hJ
  have hJ'' : (fderiv ℝ F x (0, 1)).2 * (fderiv ℝ F x (1, 0)).1 -
      (fderiv ℝ F x (0, 1)).1 * (fderiv ℝ F x (1, 0)).2 ≠ 0 := by
    simpa only [mul_comm] using hJ'
  have hJ''' : (fderiv ℝ F x (1, 0)).1 * (fderiv ℝ F x (0, 1)).2 -
      (fderiv ℝ F x (0, 1)).1 * (fderiv ℝ F x (1, 0)).2 ≠ 0 := by
    rw [show (fderiv ℝ F x (1, 0)).1 * (fderiv ℝ F x (0, 1)).2 -
      (fderiv ℝ F x (0, 1)).1 * (fderiv ℝ F x (1, 0)).2 = planeJacobian F x by
        unfold planeJacobian
        ring]
    exact hJ
  simp only [n06InverseChartVector, planeJacobian, mul_one, mul_zero,
    sub_zero, zero_sub]
  field_simp [hJ', hJ'', hJ'''] <;> ring

/-- Recover the physical test derivative from its true quotient by the
nonvanishing physical height. The identity is local at the given point. -/
theorem n06_fderiv_height_quotient
    {φ h : PolarPoint → ℝ} {x : PolarPoint}
    (hφ : DifferentiableAt ℝ φ x) (hh : DifferentiableAt ℝ h x) (hne : h x ≠ 0)
    (v : PolarPoint) :
    fderiv ℝ φ x v = fderiv ℝ h x v * (φ x / h x) +
      h x * fderiv ℝ (fun q => φ q / h q) x v := by
  have he : (fun q => h q * (φ q / h q)) =ᶠ[𝓝 x] φ := by
    filter_upwards [hh.continuousAt.eventually_ne hne] with q hq
    field_simp [hq]
  have hquot : DifferentiableAt ℝ (fun q => φ q / h q) x := by
    simpa only [div_eq_mul_inv] using hφ.fun_mul (hh.fun_inv hne)
  exact (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A v)
    (he.fderiv_eq (𝕜 := ℝ))).symm.trans
      (polar_directional_mul hh hquot v)

namespace N06RootFirstJets

variable {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
  {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}

/-- The actual Jacobian at the root is the product of the signed radial
scale and the genuine derivative of the angular boundary map. -/
theorem jacobian (J : N06RootFirstJets F h r y σ β H ρ κ Hr) (θ : ℝ) :
    planeJacobian F (r, θ) = (σ * ρ θ) * deriv β θ := by
  simp only [planeJacobian, J.chart_radial θ, J.chart_angular θ, mul_zero, sub_zero]

/-- The existing coordinate density has this actual normal row at the
root. The mixed angular drift is retained, with no conormal condition
silently imposed on the chart. -/
theorem principal_density_row
    (J : N06RootFirstJets F h r y σ β H ρ κ Hr)
    (A : SymmetricCoefficients) (θ : ℝ) :
    (coordinatePrincipalDensity A F h).a (r, θ) =
        H θ ^ 2 / |planeJacobian F (r, θ)| * A.a (r, θ) * (σ * ρ θ) ^ 2 ∧
      (coordinatePrincipalDensity A F h).b (r, θ) =
        H θ ^ 2 / |planeJacobian F (r, θ)| * (σ * ρ θ) *
          (A.a (r, θ) * κ θ + A.b (r, θ) * deriv β θ) := by
  constructor <;>
    simp only [coordinatePrincipalDensity, coefficientQuadratic, J.height_value θ,
      J.chart_radial θ, J.chart_angular θ, mul_zero, zero_mul, add_zero, zero_add] <;> ring

end N06RootFirstJets

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ} {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}

/-- The represented closed test traces give the actual physical value
and both actual first derivatives. Only the true forward chart is
differentiated at the arbitrary endpoint. -/
theorem n06_current_root_test_firstJets
    (J : N06RootFirstJets (K.chart z m) (K.height z m) r y σ β H ρ κ Hr)
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    φ (r, θ) = H θ * Q.value (y, β θ) ∧
      radialPartial φ (r, θ) = Hr θ * Q.value (y, β θ) +
        H θ * ((σ * ρ θ) * Q.radial (y, β θ) + κ θ * Q.angular (y, β θ)) ∧
      angularPartial φ (r, θ) = deriv H θ * Q.value (y, β θ) +
        H θ * deriv β θ * Q.angular (y, β θ) := by
  have hb := h04.2.2.2.2.2.2.2.2.1 z hz hs m (r, θ) hr
  have hJ : planeJacobian (K.chart z m) (r, θ) ≠ 0 := hb.2.2.1
  have hh : K.height z m (r, θ) ≠ 0 := hb.2.2.2.ne'
  have hH : H θ ≠ 0 := by simpa only [J.height_value θ] using hh
  have hvalue : Q.value (y, β θ) = φ (r, θ) / H θ := by
    simpa only [J.chart_value θ, J.height_value θ] using
      Q.physical_value (r, θ) ⟨hr, hθ⟩
  have hrad : Q.radial (y, β θ) = n06InverseChartDerivative (K.chart z m) (1, 0)
      (fun q => φ q / K.height z m q) (r, θ) := by
    simpa only [J.chart_value θ] using Q.physical_radial (r, θ) ⟨hr, hθ⟩
  have hang : Q.angular (y, β θ) = n06InverseChartDerivative (K.chart z m) (0, 1)
      (fun q => φ q / K.height z m q) (r, θ) := by
    simpa only [J.chart_value θ] using Q.physical_angular (r, θ) ⟨hr, hθ⟩
  have hfr := n06_fderiv_from_inverseChartDerivatives (K.chart z m)
    (fun q => φ q / K.height z m q) (1, 0) hJ
  have hft := n06_fderiv_from_inverseChartDerivatives (K.chart z m)
    (fun q => φ q / K.height z m q) (0, 1) hJ
  rw [J.chart_radial θ, ← hrad, ← hang] at hfr
  rw [J.chart_angular θ, ← hrad, ← hang] at hft
  simp only [zero_mul, zero_add] at hft
  have hφr := n06_fderiv_height_quotient (hφ.differentiable (by simp) (r, θ))
    (J.height_differentiable θ) hh (1, 0)
  have hφt := n06_fderiv_height_quotient (hφ.differentiable (by simp) (r, θ))
    (J.height_differentiable θ) hh (0, 1)
  change radialPartial φ (r, θ) = radialPartial (K.height z m) (r, θ) *
    (φ (r, θ) / K.height z m (r, θ)) + K.height z m (r, θ) *
      fderiv ℝ (fun q => φ q / K.height z m q) (r, θ) (1, 0) at hφr
  change angularPartial φ (r, θ) = angularPartial (K.height z m) (r, θ) *
    (φ (r, θ) / K.height z m (r, θ)) + K.height z m (r, θ) *
      fderiv ℝ (fun q => φ q / K.height z m q) (r, θ) (0, 1) at hφt
  rw [J.height_radial θ, J.height_value θ, ← hvalue, hfr] at hφr
  rw [J.height_angular θ, J.height_value θ, ← hvalue, hft] at hφt
  refine ⟨?_, hφr, ?_⟩
  · rw [hvalue]
    field_simp [hH]
  · simpa only [mul_assoc] using hφt

/-- The literal physical Green flux of the reconstructed field is
expressed by the same true test traces and both canonical Wronskians.
No regularity of the physical coefficient functions is needed here. -/
theorem n06_current_root_green_firstJets
    (J : N06RootFirstJets (K.chart z m) (K.height z m) r y σ β H ρ κ Hr)
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi)
    (A : SymmetricCoefficients) {W : PolarPoint → ℝ}
    (hW : DifferentiableAt ℝ W (y, β θ)) :
    greenNormalFlux A.a A.b φ (fun p => K.height z m p * W (K.chart z m p)) (r, θ) =
      H θ ^ 2 *
        (A.a (r, θ) * (σ * ρ θ) *
          (Q.value (y, β θ) * radialPartial W (y, β θ) - W (y, β θ) * Q.radial (y, β θ)) +
        (A.a (r, θ) * κ θ + A.b (r, θ) * deriv β θ) *
          (Q.value (y, β θ) * angularPartial W (y, β θ) - W (y, β θ) * Q.angular (y, β θ))) := by
  have ht := n06_current_root_test_firstJets J Q h04 hz hs hφ hr hθ
  unfold greenNormalFlux symmetricNormalFlux
  rw [J.reconstruction_radial θ hW, J.reconstruction_angular θ hW,
    ht.1, ht.2.1, ht.2.2]
  dsimp only
  rw [J.height_value θ, J.chart_value θ]
  ring

/-- The true physical boundary flux and the existing coordinate
principal density agree with their actual Jacobian factor. The signed
radial orientation is retained instead of being silently fixed. -/
theorem n06_current_root_green_density
    (J : N06RootFirstJets (K.chart z m) (K.height z m) r y σ β H ρ κ Hr)
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi)
    (A : SymmetricCoefficients) {W : PolarPoint → ℝ}
    (hW : DifferentiableAt ℝ W (y, β θ)) :
    (σ * ρ θ) *
      greenNormalFlux A.a A.b φ (fun p => K.height z m p * W (K.chart z m p)) (r, θ) =
      |planeJacobian (K.chart z m) (r, θ)| *
        ((coordinatePrincipalDensity A (K.chart z m) (K.height z m)).a (r, θ) *
          (Q.value (y, β θ) * radialPartial W (y, β θ) - W (y, β θ) * Q.radial (y, β θ)) +
        (coordinatePrincipalDensity A (K.chart z m) (K.height z m)).b (r, θ) *
          (Q.value (y, β θ) * angularPartial W (y, β θ) - W (y, β θ) * Q.angular (y, β θ))) := by
  have hJ := (h04.2.2.2.2.2.2.2.2.1 z hz hs m (r, θ) hr).2.2.1
  rw [n06_current_root_green_firstJets J Q h04 hz hs hφ hr hθ A hW,
    (J.principal_density_row A θ).1, (J.principal_density_row A θ).2]
  field_simp [abs_ne_zero.mpr hJ] <;> ring

end ContinuousFlexibility.Statements
