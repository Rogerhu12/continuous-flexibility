import ContinuousFlexibility.Analysis.N06CutBoundaryCancellation
import ContinuousFlexibility.Analysis.N06BoundaryAngularImage

/-!
# The actual negative-cut boundary integrals cancel

The genuine forward angular map covers the entire half-period. Therefore
the pointwise cut cancellation proved from the original N05 graph holds
at every canonical angular point, and its two actual closed Green
integrals sum to zero. The measure here is the original unnormalized
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

/-- Both canonical upper-endpoint terms cancel for the actual finite
modes of the same original graph. Matching is a conclusion of that graph;
the remaining geometric inputs describe the chosen forward atlas jets. -/
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
    (u : B.Space) (ml mr : ℕ) (s : Finset ℕ) (vl vr : ℕ → ℝ → ℝ)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hcore : Icc (K.physicalLeft ml) (K.physicalRight mr) ⊆ radialCore D)
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
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr n) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Ql.value (y, θ) * radialPartial (r11bFiniteSynthesis s vl referenceAngularBasis) (y, θ) -
        r11bFiniteSynthesis s vl referenceAngularBasis (y, θ) * Ql.radial (y, θ)) +
    (∫ θ in (0 : ℝ)..Real.pi,
      Qr.value (y, θ) * radialPartial (r11bFiniteSynthesis s vr referenceAngularBasis) (y, θ) -
        r11bFiniteSynthesis s vr referenceAngularBasis (y, θ) * Qr.radial (y, θ)) = 0 := by
  let gl : ℝ → ℝ := fun θ => Ql.value (y, θ) *
    radialPartial (r11bFiniteSynthesis s vl referenceAngularBasis) (y, θ) -
      r11bFiniteSynthesis s vl referenceAngularBasis (y, θ) * Ql.radial (y, θ)
  let gr : ℝ → ℝ := fun θ => Qr.value (y, θ) *
    radialPartial (r11bFiniteSynthesis s vr referenceAngularBasis) (y, θ) -
      r11bFiniteSynthesis s vr referenceAngularBasis (y, θ) * Qr.radial (y, θ)
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have hr : K.physicalRight ml ∈ Icc (K.physicalLeft ml) (K.physicalRight ml) :=
    ⟨(h04.2.2.2.1 ml).1.le, le_rfl⟩
  have hsurj := (n06_current_boundary_angular_surjOn Jl h04 hz hs hr).2.2
  have hzero (η : ℝ) (hη : η ∈ Icc (0 : ℝ) Real.pi) : gl η + gr η = 0 := by
    obtain ⟨θ, hθ, heq⟩ := hsurj hη
    rw [← heq]
    exact n06N05_finite_current_cut_wronskians_cancel hS h hcoordinates hz hs
      u ml mr s vl vr hjoin hcore Jl₀ Jr₀ Jl Jr Ql Qr hφ hvl hvr hmodeL hmodeR hθ
  have he : ∀ n ∈ s, ContDiff ℝ 1 (referenceAngularBasis n) :=
    fun n _ => (contDiff_referenceAngularBasis n).of_le (by simp)
  have hlc : Continuous gl := n06_current_boundary_wronskian_continuous Ql
    (n06_contDiff_one_finiteSynthesis s vl referenceAngularBasis hvl he) y
  have hrc : Continuous gr := n06_current_boundary_wronskian_continuous Qr
    (n06_contDiff_one_finiteSynthesis s vr referenceAngularBasis hvr he) y
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
