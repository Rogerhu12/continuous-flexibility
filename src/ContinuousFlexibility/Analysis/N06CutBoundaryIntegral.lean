import ContinuousFlexibility.Analysis.N06CutBoundaryCancellation

/-!
# The actual negative-cut boundary integrals cancel

The genuine closed inverse identifies the same canonical cut point on
both halves. The pointwise cancellation proved from the original N05
graph therefore applies directly at every canonical angle, and its two
actual closed Green integrals sum to zero. The measure here is the original unnormalized
half-period interval; subsequent full angular averaging multiplies this
zero identity by the prescribed normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The true boundary Wronskian is continuous for a C1 finite field and
the actual Lipschitz test traces. No second classical derivative occurs. -/
theorem n06_current_boundary_wronskian_continuous
    {S : PhysicalSpacesData} {K : CanonicalData S} {z : AnnularState S × ℝ}
    {m : ℕ} {φ W : PolarPoint → ℝ}
    (Q : N06CurrentHeightTestTraces S K z m φ) (hW : ContDiff ℝ 1 W) (y : ℝ) :
    Continuous (fun θ => Q.value (y, θ) * radialPartial W (y, θ) -
      W (y, θ) * Q.radial (y, θ)) := by
  have hline : Continuous (fun θ : ℝ => (y, θ)) := continuous_const.prodMk continuous_id
  have hd : Continuous (radialPartial W) :=
    (hW.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact ((Q.value_lipschitz.continuous.comp hline).mul (hd.comp hline)).sub
    ((hW.continuous.comp hline).mul (Q.radial_lipschitz.continuous.comp hline))

/-- Both upper-endpoint integrals cancel for the actual finite modes
of the same original graph. The canonical angle is already common to the
two true closed inverse images, including along a moving physical cut. -/
theorem n06N05_finite_current_cut_boundary_integrals_cancel
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    {z : AnnularState S × ℝ} {φ : PolarPoint → ℝ}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (n : ℕ) (s : Finset ℕ) (vl vr : ℕ → ℝ → ℝ)
    (Ql : N06CurrentHeightTestTraces S K z (K.cutPair n).1 φ)
    (Qr : N06CurrentHeightTestTraces S K z (K.cutPair n).2 φ)
    (hφ : ContDiff ℝ ∞ φ)
    (hvl : ∀ k ∈ s, ContDiff ℝ 1 (vl k))
    (hvr : ∀ k ∈ s, ContDiff ℝ 1 (vr k))
    (hmodeL : ∀ k ∈ s, n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).1) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).1) (K.right (K.cutPair n).1))] vl k)
    (hmodeR : ∀ k ∈ s, n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).2) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).2) (K.right (K.cutPair n).2))] vr k) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Ql.value (K.cutRadius n, θ) *
          radialPartial (r11bFiniteSynthesis s vl referenceAngularBasis) (K.cutRadius n, θ) -
        r11bFiniteSynthesis s vl referenceAngularBasis (K.cutRadius n, θ) *
          Ql.radial (K.cutRadius n, θ)) +
    (∫ θ in (0 : ℝ)..Real.pi,
      Qr.value (K.cutRadius n, θ) *
          radialPartial (r11bFiniteSynthesis s vr referenceAngularBasis) (K.cutRadius n, θ) -
        r11bFiniteSynthesis s vr referenceAngularBasis (K.cutRadius n, θ) *
          Qr.radial (K.cutRadius n, θ)) = 0 := by
  let gl : ℝ → ℝ := fun θ => Ql.value (K.cutRadius n, θ) *
    radialPartial (r11bFiniteSynthesis s vl referenceAngularBasis) (K.cutRadius n, θ) -
      r11bFiniteSynthesis s vl referenceAngularBasis (K.cutRadius n, θ) *
        Ql.radial (K.cutRadius n, θ)
  let gr : ℝ → ℝ := fun θ => Qr.value (K.cutRadius n, θ) *
    radialPartial (r11bFiniteSynthesis s vr referenceAngularBasis) (K.cutRadius n, θ) -
      r11bFiniteSynthesis s vr referenceAngularBasis (K.cutRadius n, θ) *
        Qr.radial (K.cutRadius n, θ)
  have hzero (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) : gl θ + gr θ = 0 :=
    n06N05_finite_current_cut_wronskians_cancel hS h hcoordinates hz hs
      u n s vl vr Ql Qr hφ hvl hvr hmodeL hmodeR hθ
  have he : ∀ k ∈ s, ContDiff ℝ 1 (referenceAngularBasis k) :=
    fun k _ => (contDiff_referenceAngularBasis k).of_le (by simp)
  have hlc : Continuous gl := n06_current_boundary_wronskian_continuous Ql
    (n06_contDiff_one_finiteSynthesis s vl referenceAngularBasis hvl he) (K.cutRadius n)
  have hrc : Continuous gr := n06_current_boundary_wronskian_continuous Qr
    (n06_contDiff_one_finiteSynthesis s vr referenceAngularBasis hvr he) (K.cutRadius n)
  change (∫ θ in (0 : ℝ)..Real.pi, gl θ) + (∫ θ in (0 : ℝ)..Real.pi, gr θ) = 0
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi, gl θ + gr θ :=
      (intervalIntegral.integral_add (hlc.intervalIntegrable _ _)
        (hrc.intervalIntegrable _ _)).symm
    _ = ∫ _θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact hzero θ (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ)
    _ = 0 := by simp

end ContinuousFlexibility.Analysis
