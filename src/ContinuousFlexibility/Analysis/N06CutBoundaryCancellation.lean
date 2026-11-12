import ContinuousFlexibility.Analysis.N06CutTransmissionJets

/-!
# True closed test traces and cancellation at an affine cut

The traces constructed from the open current height test obey the same
affine cut relation as the canonical field. This follows from the genuine closed
inverse and the original N04 smooth-test transmission law. The two affine terms cancel in the canonical
Wronskian, including for every finite reconstruction of the original N05
graph. No regularity of the physical coefficient fields is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual closed test traces satisfy the original N04 cut law at
the common canonical angle. The physical cut may move with the state. -/
theorem n06_current_cut_test_traces
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {φ : PolarPoint → ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (n : ℕ)
    (Ql : N06CurrentHeightTestTraces S K z (K.cutPair n).1 φ)
    (Qr : N06CurrentHeightTestTraces S K z (K.cutPair n).2 φ)
    (hφ : ContDiff ℝ ∞ φ)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    Ql.value (K.cutRadius n, θ) = Qr.value (K.cutRadius n, θ) ∧
      Ql.radial (K.cutRadius n, θ) + Qr.radial (K.cutRadius n, θ) =
        -(2 * K.cutRadius n)⁻¹ * Ql.value (K.cutRadius n, θ) ∧
      Ql.angular (K.cutRadius n, θ) = Qr.angular (K.cutRadius n, θ) :=
  n06_current_closed_test_cut_traces h04 hz hs n hφ Ql Qr hθ

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The common affine correction cancels exactly in the sum of the two
canonical outward Wronskians. It need not vanish separately. -/
theorem n06_affine_cut_wronskians_cancel
    {ql qr ql' qr' ul ur ul' ur' τ : ℝ}
    (hq : ql = qr) (hu : ul = ur)
    (hdq : ql' + qr' = -τ * ql) (hdu : ul' + ur' = -τ * ul) :
    (ql * ul' - ul * ql') + (qr * ur' - ur * qr') = 0 := by
  rw [← hq, ← hu]
  linear_combination ql * hdu - ul * hdq

/-- The genuine closed-test traces cancel the two finite modal rows
of the original N05 graph directly at the common canonical cut radius.
Both affine laws follow from the original graph and N04; no current or
reference cut first-jet geometry is assumed. -/
theorem n06N05_finite_current_cut_wronskians_cancel
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
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).2) (K.right (K.cutPair n).2))] vr k)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    (Ql.value (K.cutRadius n, θ) * radialPartial (r11bFiniteSynthesis s vl referenceAngularBasis)
        (K.cutRadius n, θ) - r11bFiniteSynthesis s vl referenceAngularBasis (K.cutRadius n, θ) *
          Ql.radial (K.cutRadius n, θ)) +
      (Qr.value (K.cutRadius n, θ) * radialPartial (r11bFiniteSynthesis s vr referenceAngularBasis)
        (K.cutRadius n, θ) - r11bFiniteSynthesis s vr referenceAngularBasis (K.cutRadius n, θ) *
          Qr.radial (K.cutRadius n, θ)) = 0 := by
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have htest := n06_current_cut_test_traces h04 hz hs n Ql Qr hφ hθ
  have he : ∀ k ∈ s, ContDiff ℝ 1 (referenceAngularBasis k) :=
    fun k _ => (contDiff_referenceAngularBasis k).of_le (by simp)
  have htrace (k : ℕ) (hk : k ∈ s) :=
    n06N05_canonicalMode_cut_traces hS h hcoordinates u n k (vl k) (vr k)
      (hvl k hk) (hvr k hk) (hmodeL k hk) (hmodeR k hk)
  have hsum := n06_finiteSynthesis_cut_traces s vl vr referenceAngularBasis
    hvl hvr he htrace θ
  exact n06_affine_cut_wronskians_cancel htest.1 hsum.1 htest.2.1 hsum.2

end ContinuousFlexibility.Analysis
