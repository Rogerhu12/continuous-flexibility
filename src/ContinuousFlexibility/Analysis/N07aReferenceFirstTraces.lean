module

public import ContinuousFlexibility.Analysis.N07aArbitraryAngularProduct
public import ContinuousFlexibility.Analysis.N07aClosedAngularIntegrals
public import ContinuousFlexibility.Analysis.N07aClosedScalarTraces

/-!
# First reference traces from the actual graph and closed side jets

Arbitrary angular product tests identify both value and radial first traces.
The closed-side data are the genuine extensions of the interior jets; no trace
or solution regularity is added to the frozen node statement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped Topology ContDiff

private theorem n07a_trace_mean_sub_pair {f g β : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) (2 * Real.pi)))
    (hg : ContinuousOn g (Icc (0 : ℝ) (2 * Real.pi)))
    (hβ : Continuous β) :
    radialAngularMean (fun θ => (f θ - g θ) * β θ) =
      radialAngularMean (fun θ => f θ * β θ) -
        radialAngularMean (fun θ => g θ * β θ) := by
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hfi : IntervalIntegrable (fun θ => f θ * β θ) volume 0 (2 * Real.pi) :=
    (hf.mul hβ.continuousOn).intervalIntegrable_of_Icc hT
  have hgi : IntervalIntegrable (fun θ => g θ * β θ) volume 0 (2 * Real.pi) :=
    (hg.mul hβ.continuousOn).intervalIntegrable_of_Icc hT
  unfold radialAngularMean
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub hfi hgi]
  ring

/-- Actual closed side jets representing one reference graph have matching
value and radial first traces. Smoothness of the angular jump functions is
obtained from the genuine closed tangential jet tower, not assumed of the
rough graph representative. -/
theorem n07a_referenceGraph_closedSide_firstTraces
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hborder : RadialTrueBorder D) {γ M₀ M₁ : ℝ}
    {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F)
    {l c r : ℝ} (hlc : l < c) (hcr : c < r)
    (hsub : Icc l r ⊆ radialCore D)
    {WL WR DL DR : PolarPoint → ℝ}
    (hWL : ContinuousOn WL (Icc l c ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hWR : ContinuousOn WR (Icc c r ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hDL : ContinuousOn DL (Icc l c ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hDR : ContinuousOn DR (Icc c r ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hderL : ∀ x ∈ Ioo l c, ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun y => WL (y, θ)) (DL (x, θ)) x)
    (hderR : ∀ x ∈ Ioo c r, ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun y => WR (y, θ)) (DR (x, θ)) x)
    (hUL : WL =ᵐ[volume.restrict (Ioo l c ×ˢ Ioc (0 : ℝ) (2 * Real.pi))] U.1)
    (hUR : WR =ᵐ[volume.restrict (Ioo c r ×ˢ Ioc (0 : ℝ) (2 * Real.pi))] U.1)
    (hJ₀ : ContDiff ℝ ∞ (fun θ => WL (c, θ) - WR (c, θ)))
    (hJ₀p : Function.Periodic (fun θ => WL (c, θ) - WR (c, θ)) (2 * Real.pi))
    (hJ₁ : ContDiff ℝ ∞ (fun θ => DL (c, θ) - DR (c, θ)))
    (hJ₁p : Function.Periodic (fun θ => DL (c, θ) - DR (c, θ)) (2 * Real.pi)) :
    (∀ θ, WL (c, θ) = WR (c, θ)) ∧
      (∀ θ, DL (c, θ) = DR (c, θ)) := by
  have hleft : Ioo l c ⊆ Ioo l r := fun _ hx => ⟨hx.1, hx.2.trans hcr⟩
  have hright : Ioo c r ⊆ Ioo l r := fun _ hx => ⟨hlc.trans hx.1, hx.2⟩
  have hpair (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
      (hβp : Function.Periodic β (2 * Real.pi)) :
      radialAngularMean (fun θ => WL (c, θ) * β θ) =
        radialAngularMean (fun θ => WR (c, θ) * β θ) ∧
      radialAngularMean (fun θ => DL (c, θ) * β θ) =
        radialAngularMean (fun θ => DR (c, θ) * β θ) := by
    obtain ⟨v, hv, huv⟩ := n07a_referenceGraph_arbitraryAngular_C1
      hD hborder hgraph (hlc.trans hcr) hsub hβ hβp
    have hL : (fun x => radialAngularMean (fun θ => WL (x, θ) * β θ))
        =ᵐ[volume.restrict (Ioo l c)] v :=
      (n07a_angularIntegral_ae_of_ae hUL β).trans
        (ae_restrict_of_ae_restrict_of_subset hleft huv)
    have hR : (fun x => radialAngularMean (fun θ => WR (x, θ) * β θ))
        =ᵐ[volume.restrict (Ioo c r)] v :=
      (n07a_angularIntegral_ae_of_ae hUR β).trans
        (ae_restrict_of_ae_restrict_of_subset hright huv)
    exact n07a_closedScalar_firstTraces_match hlc hcr
      (n07a_closedAngularIntegral_continuousOn hWL hβ.continuous)
      (n07a_closedAngularIntegral_continuousOn hWR hβ.continuous)
      (n07a_closedAngularIntegral_continuousOn hDL hβ.continuous)
      (n07a_closedAngularIntegral_continuousOn hDR hβ.continuous)
      (fun x hx => n07a_closedAngularIntegral_hasDerivAt hWL hDL hderL hβ.continuous hx)
      (fun x hx => n07a_closedAngularIntegral_hasDerivAt hWR hDR hderR hβ.continuous hx)
      hv hL hR
  have hWLc : ContinuousOn (fun θ => WL (c, θ)) (Icc (0 : ℝ) (2 * Real.pi)) :=
    hWL.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hθ => ⟨⟨hlc.le, le_rfl⟩, hθ⟩)
  have hWRc : ContinuousOn (fun θ => WR (c, θ)) (Icc (0 : ℝ) (2 * Real.pi)) :=
    hWR.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hθ => ⟨⟨le_rfl, hcr.le⟩, hθ⟩)
  have hDLc : ContinuousOn (fun θ => DL (c, θ)) (Icc (0 : ℝ) (2 * Real.pi)) :=
    hDL.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hθ => ⟨⟨hlc.le, le_rfl⟩, hθ⟩)
  have hDRc : ContinuousOn (fun θ => DR (c, θ)) (Icc (0 : ℝ) (2 * Real.pi)) :=
    hDR.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hθ => ⟨⟨le_rfl, hcr.le⟩, hθ⟩)
  have hzero₀ : ∀ θ, WL (c, θ) - WR (c, θ) = 0 := by
    apply n07a_periodic_eq_zero_of_smooth_angular_pairings hJ₀ hJ₀p
    intro β hβ hβp
    rw [n07a_trace_mean_sub_pair hWLc hWRc hβ.continuous,
      (hpair β hβ hβp).1, sub_self]
  have hzero₁ : ∀ θ, DL (c, θ) - DR (c, θ) = 0 := by
    apply n07a_periodic_eq_zero_of_smooth_angular_pairings hJ₁ hJ₁p
    intro β hβ hβp
    rw [n07a_trace_mean_sub_pair hDLc hDRc hβ.continuous,
      (hpair β hβ hβp).2, sub_self]
  exact ⟨fun θ => sub_eq_zero.mp (hzero₀ θ), fun θ => sub_eq_zero.mp (hzero₁ θ)⟩

end ContinuousFlexibility.Analysis
