import ContinuousFlexibility.Analysis.CanonicalSourceMeasure
import ContinuousFlexibility.Analysis.BoundaryMixedJets
import ContinuousFlexibility.Blueprint.CanonicalParts
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Actual smooth local inverses at physical endpoints

The closed-piece hypothesis supplies pointwise smoothness and an invertible
actual derivative. The inverse function theorem therefore gives a local
inverse smooth at the image point, including at a physical endpoint.
The prescribed canonical inverse agrees with this inverse on the image
of the physical interior in the local chart source. No value or
continuity of the prescribed inverse at a canonical endpoint is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A nonzero coordinate Jacobian and pointwise smoothness give an actual
smooth local inverse. Pointwise smoothness of infinite order is sufficient;
there is no common open smoothness neighborhood in the hypotheses. -/
theorem exists_smooth_localInverse_of_planeJacobian_ne_zero
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (hJ : planeJacobian F p ≠ 0) :
    ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
      (e : PolarPoint → PolarPoint) = F ∧ p ∈ e.source ∧
      ContDiffAt ℝ ∞ e.symm (F p) := by
  have hd : (fderiv ℝ F p).det ≠ 0 := by
    rwa [← planeJacobian_eq_fderiv_det]
  let L : PolarPoint ≃L[ℝ] PolarPoint :=
    (fderiv ℝ F p).toContinuousLinearEquivOfDetNeZero hd
  have hFD : HasFDerivAt F (L : PolarPoint →L[ℝ] PolarPoint) p := by
    simpa only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
      (hF.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let e := hF.toOpenPartialHomeomorph F hFD hn
  refine ⟨e, hF.toOpenPartialHomeomorph_coe hFD hn,
    hF.mem_toOpenPartialHomeomorph_source hFD hn, ?_⟩
  exact hF.to_localInverse hFD hn

/-- The local endpoint inverse agrees with the specified inverse on the
actual image collar. This uses only the open-piece inverse identity. -/
theorem canonicalChart_exists_smooth_endpointInverse
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
      (e : PolarPoint → PolarPoint) = K.chart z m ∧ p ∈ e.source ∧
      ContDiffAt ℝ ∞ e.symm (K.chart z m p) ∧
      EqOn e.symm (K.inverseChart z m)
        (K.chart z m '' (physicalPieceOpen S K m ∩ e.source)) := by
  have hclosed := hK.2.2.2.2.2.2.2.2.1 z hz hsector m p hp
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  obtain ⟨e, he, hpe, hsmooth⟩ :=
    exists_smooth_localInverse_of_planeJacobian_ne_zero hclosed.1 hclosed.2.2.1
  refine ⟨e, he, hpe, hsmooth, ?_⟩
  rintro y ⟨x, ⟨hx, hxe⟩, rfl⟩
  calc
    e.symm (K.chart z m x) = x := by
      rw [← he]
      exact e.left_inv hxe
    _ = K.inverseChart z m (K.chart z m x) := (hcharts.2.2.1 x hx).symm

/-- A genuine local inverse transports the finite order of boundary
vanishing to its canonical radial curve. The inverse value and its
smoothness come from the local homeomorphism and the actual IFT. -/
theorem iteratedDeriv_localInverse_radialCurve_eq_zero
    {U : Set PolarPoint} (hU : IsOpen U) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (c : ℝ)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) {n k : ℕ}
    (hzero : ∀ j ≤ n, ∀ θ : ℝ, radialBoundaryJet f c j θ = 0)
    (e : OpenPartialHomeomorph PolarPoint PolarPoint) (θ : ℝ)
    (he : (c, θ) ∈ e.source)
    (hinv : ContDiffAt ℝ ∞ e.symm (e (c, θ))) (hk : k ≤ n) :
    iteratedDeriv k (fun r => f (e.symm (r, (e (c, θ)).2)))
      (e (c, θ)).1 = 0 := by
  have hline : ContDiffAt ℝ ∞
      (fun r : ℝ => (r, (e (c, θ)).2)) (e (c, θ)).1 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hcurve : ContDiffAt ℝ ∞
      (fun r : ℝ => e.symm (r, (e (c, θ)).2)) (e (c, θ)).1 :=
    hinv.comp (e (c, θ)).1 hline
  exact iteratedDeriv_comp_eq_zero_of_radialBoundaryJets_zero hU hf c hc hzero
    hcurve (e.left_inv he) hk

end ContinuousFlexibility.Analysis
