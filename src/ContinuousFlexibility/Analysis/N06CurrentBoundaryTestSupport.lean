module

public import ContinuousFlexibility.Analysis.N06CurrentTestTraces
public import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback
public import ContinuousFlexibility.Analysis.N05N06ClosedChartBridge

/-!
# The original radial support removes the outer Green terms

Outside the original closed radial support of a physical test, its
quotient by the actual height is the zero germ. Consequently the genuine
current value and both first traces vanish on the forward image of every
point in the actual closed physical domain. The genuine closed inverse
then gives vanishing on a canonical endpoint circle whose physical inverse
image misses the support. The original negative-root image clauses supply
this condition at both true root circles.

The conclusions apply to either endpoint and to arbitrary first-jet
fields in the Green density. Artificial moving cuts are not tested against
their reference radial coordinates; their terms are cancelled separately
by the actual canonical transmission law.
-/

@[expose] public section

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
    (hx : x ∈ physicalPieceClosed S K z m ∩ (univ ×ˢ Icc (0 : ℝ) Real.pi))
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
    (hx : x ∈ physicalPieceClosed S K z m ∩ (univ ×ˢ Icc (0 : ℝ) Real.pi))
    (hxJ : x.1 ∉ J) (A : SymmetricCoefficients) (W : PolarPoint → ℝ) :
    (coordinatePrincipalDensity A (K.chart z m) (K.height z m)).a x *
        (Q.value (K.chart z m x) * radialPartial W (K.chart z m x) -
          W (K.chart z m x) * Q.radial (K.chart z m x)) +
      (coordinatePrincipalDensity A (K.chart z m) (K.height z m)).b x *
        (Q.value (K.chart z m x) * angularPartial W (K.chart z m x) -
          W (K.chart z m x) * Q.angular (K.chart z m x)) = 0 := by
  obtain ⟨hv, hr, ht⟩ := Q.physical_zero_off_support hJ hzero hx hxJ
  simp only [hv, hr, ht, zero_mul, mul_zero, sub_self, add_zero]

/-- The genuine closed inverse identifies the trace at a canonical
point with the physical zero germ at its actual inverse image. -/
theorem N06CurrentHeightTestTraces.canonical_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {p : PolarPoint}
    (hp : p ∈ Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi)
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ t, t ∉ J → ∀ θ, φ (t, θ) = 0)
    (hout : (K.inverseChart z m p).1 ∉ J) :
    Q.value p = 0 ∧ Q.radial p = 0 ∧ Q.angular p = 0 := by
  have hx := (n05_canonicalChart_closedAngular_maps h04 hz hs m).2 hp
  have hq := Q.physical_zero_off_support hJ hzero hx hout
  rw [(h04.1.boundary z hz hs m).2.2.2.1 p ⟨hp.1, mem_univ _⟩] at hq
  exact hq

/-- All endpoint traces vanish when the actual closed inverse circle
misses the physical support. This does not identify a moving cut with any
reference radial endpoint. -/
theorem N06CurrentHeightTestTraces.boundary_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {y : ℝ} (hy : y ∈ Icc (K.left m) (K.right m))
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ t, t ∉ J → ∀ θ, φ (t, θ) = 0)
    (hout : ∀ θ ∈ Icc (0 : ℝ) Real.pi, (K.inverseChart z m (y, θ)).1 ∉ J)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    Q.value (y, θ) = 0 ∧ Q.radial (y, θ) = 0 ∧ Q.angular (y, θ) = 0 :=
  Q.canonical_zero_off_support h04 hz hs ⟨hy, hθ⟩ hJ hzero (hout θ hθ)

/-- The original current-cut geometry fixes the physical radii of both
true root circles. Their moving middle curve does not occur here. -/
theorem n06_cutRoot_inverse_radius
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (n : ℕ) :
    (∀ θ, (K.inverseChart z (K.cutPair n).1 (0, θ)).1 = C.left n) ∧
      (∀ θ, (K.inverseChart z (K.cutPair n).2 (0, θ)).1 = C.right n) := by
  have hcut := h04.2.1.1.2 z hz hs n
  constructor
  · intro θ
    have hx : K.inverseChart z (K.cutPair n).1 (0, θ) ∈
        ({C.left n} ×ˢ (univ : Set ℝ)) := by
      rw [← hcut.2.2.2.2.1]
      exact ⟨(0, θ), ⟨rfl, mem_univ _⟩, rfl⟩
    exact hx.1
  · intro θ
    have hx : K.inverseChart z (K.cutPair n).2 (0, θ) ∈
        ({C.right n} ×ˢ (univ : Set ℝ)) := by
      rw [← hcut.2.2.2.2.2]
      exact ⟨(0, θ), ⟨rfl, mem_univ _⟩, rfl⟩
    exact hx.1

/-- For either negative half, the actual root circle is off support
whenever its original component endpoint is off support. This is derived
from the N04 image clause, not an additional endpoint condition. -/
theorem N06CurrentHeightTestTraces.negativeRoot_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (n : ℕ) {r : ℝ}
    (hside : (m = (K.cutPair n).1 ∧ r = C.left n) ∨
      (m = (K.cutPair n).2 ∧ r = C.right n))
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ t, t ∉ J → ∀ θ, φ (t, θ) = 0) (hout : r ∉ J)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    Q.value (0, θ) = 0 ∧ Q.radial (0, θ) = 0 ∧ Q.angular (0, θ) = 0 := by
  obtain ⟨_, _, _, _, _, hR, hl, hr, hRl, hRr⟩ := h04.2.1.1.1 n
  have hy : (0 : ℝ) ∈ Icc (K.left m) (K.right m) := by
    rcases hside with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rw [hl, hRl]
      exact ⟨le_rfl, hR.le⟩
    · rw [hr, hRr]
      exact ⟨le_rfl, hR.le⟩
  have hrad : ∀ η, (K.inverseChart z m (0, η)).1 = r := by
    rcases hside with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (n06_cutRoot_inverse_radius h04 hz hs n).1
    · exact (n06_cutRoot_inverse_radius h04 hz hs n).2
  apply Q.boundary_zero_off_support h04 hz hs hy hJ hzero ?_ hθ
  intro η _
  rw [hrad η]
  exact hout

/-- Every endpoint Green row vanishes off support. The two coefficient
functions may include the actual principal row and either orientation;
there are no regularity assumptions because the integrand is zero. -/
theorem N06CurrentHeightTestTraces.boundaryIntegral_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {y : ℝ} (hy : y ∈ Icc (K.left m) (K.right m))
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ t, t ∉ J → ∀ θ, φ (t, θ) = 0)
    (hout : ∀ θ ∈ Icc (0 : ℝ) Real.pi, (K.inverseChart z m (y, θ)).1 ∉ J)
    (a b : ℝ → ℝ) (W : PolarPoint → ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      a θ * (Q.value (y, θ) * radialPartial W (y, θ) - W (y, θ) * Q.radial (y, θ)) +
      b θ * (Q.value (y, θ) * angularPartial W (y, θ) - W (y, θ) * Q.angular (y, θ))) = 0 := by
  calc
    _ = ∫ _θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      obtain ⟨hv, hrad, hang⟩ := Q.boundary_zero_off_support h04 hz hs hy hJ hzero hout
        (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ)
      simp only [hv, hrad, hang, zero_mul, mul_zero, sub_self, add_zero]
    _ = 0 := by simp

/-- In particular the actual positive and negative radial Wronskians
used by the finite-mode Green identities vanish outside the test support. -/
theorem N06CurrentHeightTestTraces.wronskianIntegral_zero_off_support
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {y : ℝ} (hy : y ∈ Icc (K.left m) (K.right m))
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ t, t ∉ J → ∀ θ, φ (t, θ) = 0)
    (hout : ∀ θ ∈ Icc (0 : ℝ) Real.pi, (K.inverseChart z m (y, θ)).1 ∉ J)
    (W : PolarPoint → ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Q.value (y, θ) * radialPartial W (y, θ) - W (y, θ) * Q.radial (y, θ)) = 0 := by
  simpa only [one_mul, zero_mul, add_zero] using
    Q.boundaryIntegral_zero_off_support h04 hz hs hy hJ hzero hout
      (fun _ => 1) (fun _ => 0) W

end ContinuousFlexibility.Statements
