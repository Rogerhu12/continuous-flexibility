import ContinuousFlexibility.Analysis.N06CutTransmissionJets

/-!
# True closed test traces and cancellation at an affine cut

The traces constructed from the open current height test obey the same
affine cut relation as the canonical field. This is derived from their
actual physical first jets and the forward chart, not from boundary values
of the totalized inverse. The two affine terms cancel in the canonical
Wronskian, including for every finite reconstruction of the original N05
graph. No regularity of the physical coefficient fields is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The true represented test traces obey the affine relation forced by
the actual forward chart and height jets on the two closed pieces. -/
theorem n06_current_cut_test_traces
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    {φ : PolarPoint → ℝ} {ml mr : ℕ} {r y σ τ : ℝ}
    {β H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets (K.chart z ml) (K.height z ml) r y σ β H ρ κ Hr)
    (Jr : N06RootFirstJets (K.chart z mr) (K.height z mr) r y (-σ) β H ρ κ
      (fun θ => Hr θ - H θ * (σ * ρ θ) * τ))
    (Ql : N06CurrentHeightTestTraces S K z ml φ)
    (Qr : N06CurrentHeightTestTraces S K z mr φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ)
    (hrl : r ∈ Icc (K.physicalLeft ml) (K.physicalRight ml))
    (hrr : r ∈ Icc (K.physicalLeft mr) (K.physicalRight mr))
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    Ql.value (y, β θ) = Qr.value (y, β θ) ∧
      Ql.radial (y, β θ) + Qr.radial (y, β θ) = -τ * Ql.value (y, β θ) ∧
      Ql.angular (y, β θ) = Qr.angular (y, β θ) := by
  have hclosed := h04.2.2.2.2.2.2.2.2.1 z hz hs ml (r, θ) hrl
  have hH : H θ ≠ 0 := by
    simpa only [Jl.height_value θ] using hclosed.2.2.2.ne'
  have hnonzero : (σ * ρ θ) * deriv β θ ≠ 0 := by
    simpa only [Jl.jacobian θ] using hclosed.2.2.1
  have hscale : σ * ρ θ ≠ 0 := (mul_ne_zero_iff.mp hnonzero).1
  have hβ : deriv β θ ≠ 0 := (mul_ne_zero_iff.mp hnonzero).2
  have htl := n06_current_root_test_firstJets Jl Ql h04 hz hs hφ hrl hθ
  have htr := n06_current_root_test_firstJets Jr Qr h04 hz hs hφ hrr hθ
  have hv : Ql.value (y, β θ) = Qr.value (y, β θ) :=
    mul_left_cancel₀ hH (htl.1.symm.trans htr.1)
  have ht : Ql.angular (y, β θ) = Qr.angular (y, β θ) := by
    have he := htl.2.2.symm.trans htr.2.2
    rw [hv] at he
    exact mul_left_cancel₀ (mul_ne_zero hH hβ) (add_left_cancel he)
  refine ⟨hv, ?_, ht⟩
  have he := htl.2.1.symm.trans htr.2.1
  rw [hv, ht] at he
  apply mul_left_cancel₀ (mul_ne_zero hH hscale)
  rw [hv]
  change (H θ * (σ * ρ θ)) * (Ql.radial (y, β θ) + Qr.radial (y, β θ)) =
    (H θ * (σ * ρ θ)) * (-τ * Qr.value (y, β θ))
  linear_combination he

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

/-- The real closed-test traces cancel the two finite modal boundary
terms of the same original N05 graph. The equality is evaluated at the
actual common angular boundary map, with neither boundary inverse nor a
new canonical matching condition among the inputs. -/
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
    (u : B.Space) (ml mr : ℕ) (s : Finset ℕ) (vl vr : ℕ → ℝ → ℝ)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hroot : K.physicalRight ml ∈ radialCore D)
    {y σ τ : ℝ} {β₀ H₀ ρ₀ κ₀ Hr₀ β H ρ κ Hr : ℝ → ℝ}
    (Jl₀ : N06RootFirstJets (K.chart (C.referenceState, 0) ml)
      (K.height (C.referenceState, 0) ml) (K.physicalRight ml) y σ β₀ H₀ ρ₀ κ₀ Hr₀)
    (Jr₀ : N06RootFirstJets (K.chart (C.referenceState, 0) mr)
      (K.height (C.referenceState, 0) mr) (K.physicalRight ml) y (-σ) β₀ H₀ ρ₀ κ₀
        (fun θ => Hr₀ θ - H₀ θ * (σ * ρ₀ θ) * τ))
    (Jl : N06RootFirstJets (K.chart z ml) (K.height z ml)
      (K.physicalRight ml) y σ β H ρ κ Hr)
    (Jr : N06RootFirstJets (K.chart z mr) (K.height z mr)
      (K.physicalRight ml) y (-σ) β H ρ κ
        (fun θ => Hr θ - H θ * (σ * ρ θ) * τ))
    (Ql : N06CurrentHeightTestTraces S K z ml φ)
    (Qr : N06CurrentHeightTestTraces S K z mr φ)
    (hφ : ContDiff ℝ ∞ φ)
    (hvl : ∀ n ∈ s, ContDiff ℝ 1 (vl n))
    (hvr : ∀ n ∈ s, ContDiff ℝ 1 (vr n))
    (hmodeL : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[volume.restrict (Ioo (K.left ml) (K.right ml))] vl n)
    (hmodeR : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr n)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    (Ql.value (y, β θ) * radialPartial (r11bFiniteSynthesis s vl referenceAngularBasis)
        (y, β θ) - r11bFiniteSynthesis s vl referenceAngularBasis (y, β θ) *
          Ql.radial (y, β θ)) +
      (Qr.value (y, β θ) * radialPartial (r11bFiniteSynthesis s vr referenceAngularBasis)
        (y, β θ) - r11bFiniteSynthesis s vr referenceAngularBasis (y, β θ) *
          Qr.radial (y, β θ)) = 0 := by
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have hrl : K.physicalRight ml ∈ Icc (K.physicalLeft ml) (K.physicalRight ml) :=
    ⟨(h04.2.2.2.1 ml).1.le, le_rfl⟩
  have hrr : K.physicalRight ml ∈ Icc (K.physicalLeft mr) (K.physicalRight mr) := by
    rw [hjoin]
    exact ⟨le_rfl, (h04.2.2.2.1 mr).1.le⟩
  have htest := n06_current_cut_test_traces Jl Jr Ql Qr h04 hz hs hφ hrl hrr hθ
  have he : ∀ n ∈ s, ContDiff ℝ 1 (referenceAngularBasis n) :=
    fun n _ => (contDiff_referenceAngularBasis n).of_le (by simp)
  have htrace (n : ℕ) (hn : n ∈ s) :=
    n06N05_canonicalMode_cut_traces hS h hcoordinates u ml mr n (vl n) (vr n)
      hjoin hroot Jl₀ Jr₀ (hvl n hn) (hvr n hn) (hmodeL n hn) (hmodeR n hn)
  have hsum := n06_finiteSynthesis_cut_traces s vl vr referenceAngularBasis
    hvl hvr he htrace (β θ)
  exact n06_affine_cut_wronskians_cancel htest.1 hsum.1 htest.2.1 hsum.2

end ContinuousFlexibility.Analysis
