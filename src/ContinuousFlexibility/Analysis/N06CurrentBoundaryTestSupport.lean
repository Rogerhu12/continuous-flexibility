import ContinuousFlexibility.Analysis.N06RootBoundaryCancellation
import ContinuousFlexibility.Analysis.N06BoundaryAngularImage

/-!
# The original radial support removes the outer Green terms

Outside the original closed radial support of a physical test, its
quotient by the actual height is the zero germ. Consequently the genuine
current value and both first traces vanish on the forward image of every
physical boundary point. The actual angular image theorem then gives
vanishing on the whole canonical endpoint circle.

The conclusions apply to either endpoint and to arbitrary first-jet
fields in the Green density. No trace convergence, boundary inverse, or
extra zero-boundary condition is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {m : ℕ} {φ : PolarPoint → ℝ}

/-- All three genuine traces vanish at an actual forward boundary image
outside the same closed support as the original physical test. -/
theorem N06CurrentHeightTestTraces.physical_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0)
    {x : PolarPoint}
    (hx : x ∈ Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi)
    (hxJ : x.1 ∉ J) :
    Q.value (K.chart z m x) = 0 ∧ Q.radial (K.chart z m x) = 0 ∧
      Q.angular (K.chart z m x) = 0 := by
  have he : (fun q => φ q / K.height z m q) =ᶠ[𝓝 x] (fun _ : PolarPoint => (0 : ℝ)) := by
    filter_upwards [(continuous_fst.tendsto x).eventually
      (hJ.isOpen_compl.mem_nhds hxJ)] with q hq
    rw [show φ q = 0 from hzero q.1 hq q.2, zero_div]
  have hd : fderiv ℝ (fun q => φ q / K.height z m q) x = 0 := by
    simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜 := ℝ)
  refine ⟨?_, ?_, ?_⟩
  · rw [Q.physical_value x hx, show φ x = 0 from hzero x.1 hxJ x.2, zero_div]
  · rw [Q.physical_radial x hx]
    simp only [n06InverseChartDerivative, hd, ContinuousLinearMap.zero_apply]
  · rw [Q.physical_angular x hx]
    simp only [n06InverseChartDerivative, hd, ContinuousLinearMap.zero_apply]

/-- The actual transported Green density is zero off the original test
support, for any physical coefficients and any canonical field. -/
theorem N06CurrentHeightTestTraces.physicalDensity_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0)
    {x : PolarPoint}
    (hx : x ∈ Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi)
    (hxJ : x.1 ∉ J) (A : SymmetricCoefficients) (W : PolarPoint → ℝ) :
    n06RootBoundaryDensity A (K.chart z m) (K.height z m)
      Q.value Q.radial Q.angular W x (K.chart z m x) = 0 := by
  obtain ⟨hv, hr, ht⟩ := Q.physical_zero_off_support hJ hzero hx hxJ
  simp only [n06RootBoundaryDensity, hv, hr, ht, zero_mul, mul_zero, sub_self, add_zero]

/-- The genuine forward angular map covers the endpoint circle, so
support vanishing holds at every canonical angle, not only at selected
forward images. This statement treats both radial endpoints uniformly. -/
theorem N06CurrentHeightTestTraces.boundary_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jroot : N06RootFirstJets (K.chart z m) (K.height z m) r y σ β H ρ κ Hr)
    (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ t, t ∉ J → ∀ θ, φ (t, θ) = 0) (hrJ : r ∉ J)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    Q.value (y, θ) = 0 ∧ Q.radial (y, θ) = 0 ∧ Q.angular (y, θ) = 0 := by
  obtain ⟨η, hη, he⟩ :=
    (n06_current_boundary_angular_surjOn Jroot h04 hz hs hr).2.2 hθ
  have hq := Q.physical_zero_off_support hJ hzero (x := (r, η)) ⟨hr, hη⟩ hrJ
  simpa only [Jroot.chart_value η, he] using hq

/-- Every endpoint Green row vanishes off support. The two coefficient
functions may include the actual principal row and either orientation;
there are no regularity assumptions because the integrand is zero. -/
theorem N06CurrentHeightTestTraces.boundaryIntegral_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jroot : N06RootFirstJets (K.chart z m) (K.height z m) r y σ β H ρ κ Hr)
    (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ t, t ∉ J → ∀ θ, φ (t, θ) = 0) (hrJ : r ∉ J)
    (a b : ℝ → ℝ) (W : PolarPoint → ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      a θ * (Q.value (y, θ) * radialPartial W (y, θ) - W (y, θ) * Q.radial (y, θ)) +
      b θ * (Q.value (y, θ) * angularPartial W (y, θ) - W (y, θ) * Q.angular (y, θ))) = 0 := by
  calc
    _ = ∫ _θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      obtain ⟨hv, hrad, hang⟩ := Q.boundary_zero_off_support h04 hz hs Jroot hr hJ hzero hrJ
        (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ)
      simp only [hv, hrad, hang, zero_mul, mul_zero, sub_self, add_zero]
    _ = 0 := by simp

/-- In particular the actual positive and negative radial Wronskians
used by the finite-mode Green identities vanish outside the test support. -/
theorem N06CurrentHeightTestTraces.wronskianIntegral_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jroot : N06RootFirstJets (K.chart z m) (K.height z m) r y σ β H ρ κ Hr)
    (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ t, t ∉ J → ∀ θ, φ (t, θ) = 0) (hrJ : r ∉ J)
    (W : PolarPoint → ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Q.value (y, θ) * radialPartial W (y, θ) - W (y, θ) * Q.radial (y, θ)) = 0 := by
  simpa only [one_mul, zero_mul, add_zero] using
    Q.boundaryIntegral_zero_off_support h04 hz hs Jroot hr hJ hzero hrJ
      (fun _ => 1) (fun _ => 0) W

end ContinuousFlexibility.Statements
