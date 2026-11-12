import ContinuousFlexibility.Analysis.N07aClosedJets
import ContinuousFlexibility.Analysis.N07aReferenceFirstTraces

/-!
# First-trace identification for within-smooth closed reference sides

The radial jet is the genuine derivative within the closed strip. Smooth
angular traces and their periods follow from this derivative; they are not
separate regularity or matching assumptions on the unknown.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open N07aClosedJets
open scoped ContDiff Topology

/-- The genuine radial first derivative relative to a closed strip. -/
def n07aClosedRadialJet (l r : ℝ) (W : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  fderivWithin ℝ W (closedStrip l r) p (1, 0)

theorem n07aClosedRadialJet_contDiffOn {l r : ℝ} (hlr : l < r)
    {W : PolarPoint → ℝ} (hW : ContDiffOn ℝ ∞ W (closedStrip l r)) :
    ContDiffOn ℝ ∞ (n07aClosedRadialJet l r W) (closedStrip l r) :=
  (hW.fderivWithin ((uniqueDiffOn_Icc hlr).prod uniqueDiffOn_univ)
    (by simp)).clm_apply contDiffOn_const

theorem n07a_closedStrip_angularTrace_contDiff {l r t : ℝ}
    {W : PolarPoint → ℝ} (hW : ContDiffOn ℝ ∞ W (closedStrip l r))
    (ht : t ∈ Icc l r) : ContDiff ℝ ∞ (fun θ => W (t, θ)) :=
  hW.comp_contDiff (contDiff_const.prodMk contDiff_id)
    (fun θ => ⟨ht, mem_univ θ⟩)

theorem n07a_closedStrip_radial_hasDerivWithinAt {l r t : ℝ}
    {W : PolarPoint → ℝ} (hW : ContDiffOn ℝ ∞ W (closedStrip l r))
    (ht : t ∈ Icc l r) (θ : ℝ) :
    HasDerivWithinAt (fun s => W (s, θ))
      (n07aClosedRadialJet l r W (t, θ)) (Icc l r) t := by
  have hd := (hW.differentiableOn (by simp) (t, θ) ⟨ht, mem_univ θ⟩).hasFDerivWithinAt
  have hs : HasDerivWithinAt (fun s : ℝ => (s, θ)) (1, 0) (Icc l r) t :=
    ((hasDerivAt_id' t).prodMk (hasDerivAt_const t θ)).hasDerivWithinAt
  exact hd.comp_hasDerivWithinAt t hs (fun s hs => ⟨hs, mem_univ θ⟩)

theorem n07a_closedStrip_radial_hasDerivAt {l r t : ℝ}
    {W : PolarPoint → ℝ} (hW : ContDiffOn ℝ ∞ W (closedStrip l r))
    (ht : t ∈ Ioo l r) (θ : ℝ) :
    HasDerivAt (fun s => W (s, θ))
      (n07aClosedRadialJet l r W (t, θ)) t :=
  (n07a_closedStrip_radial_hasDerivWithinAt hW (Ioo_subset_Icc_self ht) θ).
    hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem n07aClosedRadialJet_periodic {l r P : ℝ} (hlr : l < r)
    {W : PolarPoint → ℝ} (hW : ContDiffOn ℝ ∞ W (closedStrip l r))
    (hWp : ∀ p ∈ closedStrip l r, W (p + (0, P)) = W p) :
    ∀ p ∈ closedStrip l r,
      n07aClosedRadialJet l r W (p + (0, P)) = n07aClosedRadialJet l r W p := by
  rintro ⟨t, θ⟩ hp
  have h₁ := (n07a_closedStrip_radial_hasDerivWithinAt hW hp.1 (θ + P)).derivWithin
    (uniqueDiffOn_Icc hlr t hp.1)
  have h₂ := (n07a_closedStrip_radial_hasDerivWithinAt hW hp.1 θ).derivWithin
    (uniqueDiffOn_Icc hlr t hp.1)
  have he : EqOn (fun s => W (s, θ + P)) (fun s => W (s, θ)) (Icc l r) := by
    intro s hs
    simpa only [Prod.mk_add_mk, add_zero] using hWp (s, θ) ⟨hs, mem_univ θ⟩
  simpa only [Prod.mk_add_mk, add_zero] using
    h₁.symm.trans ((derivWithin_congr he (he hp.1)).trans h₂)

/-- Apply the actual graph equation to two genuine within-smooth sides.
All angular smoothness, periodicity and first-derivative relations required
by the scalar trace argument are derived from the two closed side fields. -/
theorem n07a_referenceGraph_firstTraces_of_closedSmooth
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hborder : RadialTrueBorder D) {γ M₀ M₁ : ℝ}
    {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F)
    {l c r : ℝ} (hlc : l < c) (hcr : c < r)
    (hsub : Icc l r ⊆ radialCore D)
    {WL WR : PolarPoint → ℝ}
    (hWL : ContDiffOn ℝ ∞ WL (closedStrip l c))
    (hWR : ContDiffOn ℝ ∞ WR (closedStrip c r))
    (hWLp : ∀ p ∈ closedStrip l c, WL (p + (0, Real.pi)) = WL p)
    (hWRp : ∀ p ∈ closedStrip c r, WR (p + (0, Real.pi)) = WR p)
    (hUL : WL =ᵐ[volume.restrict (Ioo l c ×ˢ Ioc (0 : ℝ) (2 * Real.pi))] U.1)
    (hUR : WR =ᵐ[volume.restrict (Ioo c r ×ˢ Ioc (0 : ℝ) (2 * Real.pi))] U.1) :
    (∀ θ, WL (c, θ) = WR (c, θ)) ∧
    (∀ θ, n07aClosedRadialJet l c WL (c, θ) =
      n07aClosedRadialJet c r WR (c, θ)) := by
  let DL := n07aClosedRadialJet l c WL
  let DR := n07aClosedRadialJet c r WR
  have hDL : ContDiffOn ℝ ∞ DL (closedStrip l c) :=
    n07aClosedRadialJet_contDiffOn hlc hWL
  have hDR : ContDiffOn ℝ ∞ DR (closedStrip c r) :=
    n07aClosedRadialJet_contDiffOn hcr hWR
  have hleft : c ∈ Icc l c := ⟨hlc.le, le_rfl⟩
  have hright : c ∈ Icc c r := ⟨le_rfl, hcr.le⟩
  have hpWL : Function.Periodic (fun θ => WL (c, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hWLp (c, θ) ⟨hleft, mem_univ θ⟩
  have hpWR : Function.Periodic (fun θ => WR (c, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hWRp (c, θ) ⟨hright, mem_univ θ⟩
  have hpDL : Function.Periodic (fun θ => DL (c, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using
      n07aClosedRadialJet_periodic hlc hWL hWLp (c, θ) ⟨hleft, mem_univ θ⟩
  have hpDR : Function.Periodic (fun θ => DR (c, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using
      n07aClosedRadialJet_periodic hcr hWR hWRp (c, θ) ⟨hright, mem_univ θ⟩
  have hp₀ := hpWL.sub hpWR
  have hp₁ := hpDL.sub hpDR
  apply n07a_referenceGraph_closedSide_firstTraces hD hborder hgraph hlc hcr hsub
    (hWL.continuousOn.mono (Set.prod_mono Subset.rfl (subset_univ _)))
    (hWR.continuousOn.mono (Set.prod_mono Subset.rfl (subset_univ _)))
    (hDL.continuousOn.mono (Set.prod_mono Subset.rfl (subset_univ _)))
    (hDR.continuousOn.mono (Set.prod_mono Subset.rfl (subset_univ _)))
    (fun x hx θ _ => n07a_closedStrip_radial_hasDerivAt hWL hx θ)
    (fun x hx θ _ => n07a_closedStrip_radial_hasDerivAt hWR hx θ) hUL hUR
  · exact (n07a_closedStrip_angularTrace_contDiff hWL hleft).sub
      (n07a_closedStrip_angularTrace_contDiff hWR hright)
  · simpa only [← two_mul] using hp₀.add_period hp₀
  · exact (n07a_closedStrip_angularTrace_contDiff hDL hleft).sub
      (n07a_closedStrip_angularTrace_contDiff hDR hright)
  · simpa only [← two_mul] using hp₁.add_period hp₁

end ContinuousFlexibility.Analysis
