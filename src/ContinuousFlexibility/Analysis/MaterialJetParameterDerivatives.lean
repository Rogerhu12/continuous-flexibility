module

public import ContinuousFlexibility.Analysis.MixedJetParameterDerivatives

/-!
# Parameter differentiation through the actual weighted divergence

Material pullback converts physical partial derivatives into fixed smooth
material multipliers and ordinary partial derivatives. The parameter
derivative therefore commutes with every weighted physical jet of the
symmetric divergence. Only smooth slices near the parameter are used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

def PhysicalJetHasDerivAt (T : MaterialData) (γ : ℝ)
    (F : ℝ → PolarPoint → ℝ) (G : PolarPoint → ℝ) (t : ℝ) : Prop :=
  MixedJetHasDerivAt (fun s => materialPullback T γ (F s))
    (materialPullback T γ G) t

theorem PhysicalJetHasDerivAt.weighted
    {T : MaterialData} {γ : ℝ} {F : ℝ → PolarPoint → ℝ}
    {G : PolarPoint → ℝ} {t : ℝ}
    (h : PhysicalJetHasDerivAt T γ F G t) (a b c : ℕ) (p : PolarPoint) :
    HasDerivAt (fun s => weightedPhysicalJet T γ a b c (F s) p)
      (weightedPhysicalJet T γ a b c G p) t :=
  (h a b p).const_mul _

theorem PhysicalJetHasDerivAt.congr_on_annularOpen
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {F F' : ℝ → PolarPoint → ℝ} {G G' : PolarPoint → ℝ} {t : ℝ}
    (hT : IsMaterialData D T) (h : PhysicalJetHasDerivAt T γ F G t)
    (hF : ∀ᶠ s in 𝓝 t, EqOn (F s) (F' s) (annularOpen D))
    (hG : EqOn G G' (annularOpen D)) : PhysicalJetHasDerivAt T γ F' G' t := by
  apply MixedJetHasDerivAt.congr h
  · filter_upwards [hF] with s hs
    funext p
    unfold materialPullback
    rw [hs ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩]
  · funext p
    unfold materialPullback
    rw [hG ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩]

theorem PhysicalJetHasDerivAt.add
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {F H : ℝ → PolarPoint → ℝ} {G K : PolarPoint → ℝ} {t : ℝ}
    (hT : IsMaterialData D T)
    (hF : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞ (F s) (annularOpen D))
    (hH : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞ (H s) (annularOpen D))
    (hG : ContDiffOn ℝ ∞ G (annularOpen D))
    (hK : ContDiffOn ℝ ∞ K (annularOpen D))
    (h : PhysicalJetHasDerivAt T γ F G t)
    (h' : PhysicalJetHasDerivAt T γ H K t) :
    PhysicalJetHasDerivAt T γ (fun s p => F s p + H s p) (fun p => G p + K p) t := by
  have hd := MixedJetHasDerivAt.add
    (hF.mono fun s hs => contDiff_materialPullback hT hs)
    (hH.mono fun s hs => contDiff_materialPullback hT hs)
    (contDiff_materialPullback hT hG) (contDiff_materialPullback hT hK) h h'
  apply hd.congr
  · exact Eventually.of_forall fun s => funext fun p => by
      simp only [materialPullback, mul_add]
  · funext p
    simp only [materialPullback, mul_add]

/-- A derivative for the unweighted material coefficient, multiplied by
one fixed actual height field, gives the weighted derivative. -/
theorem physicalJetHasDerivAt_coefficient_mul
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {A : ℝ → PolarPoint → ℝ} {B u : PolarPoint → ℝ} {t : ℝ}
    (hT : IsMaterialData D T)
    (hA : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞ (A s) (annularOpen D))
    (hB : ContDiffOn ℝ ∞ B (annularOpen D))
    (hu : ContDiffOn ℝ ∞ u (annularOpen D))
    (h : MixedJetHasDerivAt (fun s p => A s (T.radius p.1, p.2))
      (fun p => B (T.radius p.1, p.2)) t) :
    PhysicalJetHasDerivAt T γ (fun s p => A s p * u p) (fun p => B p * u p) t := by
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hinside (p : PolarPoint) : (T.radius p.1, p.2) ∈ annularOpen D :=
    ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩
  have hcoord : ContDiff ℝ ∞ (fun p : PolarPoint => (T.radius p.1, p.2)) :=
    (hr.comp contDiff_fst).prodMk contDiff_snd
  have hAm : ∀ᶠ s in 𝓝 t, ContDiff ℝ ∞ (fun p : PolarPoint => A s (T.radius p.1, p.2)) :=
    hA.mono fun s hs => hs.comp_contDiff hcoord hinside
  have hBm : ContDiff ℝ ∞ (fun p : PolarPoint => B (T.radius p.1, p.2)) :=
    hB.comp_contDiff hcoord hinside
  have huM : ContDiff ℝ ∞ (materialPullback T γ u) :=
    contDiff_materialPullback (γ := γ) hT hu
  have hd := MixedJetHasDerivAt.mul_const (u := materialPullback T γ u) hAm hBm huM h
  apply hd.congr
  · exact Eventually.of_forall fun s => funext fun p => by
      dsimp only [materialPullback]
      ring
  · funext p
    dsimp only [materialPullback]
    ring

theorem PhysicalJetHasDerivAt.angularPartial
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {F : ℝ → PolarPoint → ℝ} {G : PolarPoint → ℝ} {t : ℝ}
    (hT : IsMaterialData D T)
    (hF : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞ (F s) (annularOpen D))
    (hG : ContDiffOn ℝ ∞ G (annularOpen D))
    (h : PhysicalJetHasDerivAt T γ F G t) :
    PhysicalJetHasDerivAt T γ (fun s => ContinuousFlexibility.angularPartial (F s)) (ContinuousFlexibility.angularPartial G) t := by
  have hd := MixedJetHasDerivAt.angularPartial
    (hF.mono fun s hs => contDiff_materialPullback hT hs)
    (contDiff_materialPullback hT hG) h
  apply hd.congr
  · filter_upwards [hF] with s hs
    exact (funext (n02n03_materialPullback_angularPartial hT hs)).symm
  · exact (funext (n02n03_materialPullback_angularPartial hT hG)).symm

theorem PhysicalJetHasDerivAt.radialPartial
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {F : ℝ → PolarPoint → ℝ} {G : PolarPoint → ℝ} {t : ℝ}
    (hT : IsMaterialData D T)
    (hF : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞ (F s) (annularOpen D))
    (hG : ContDiffOn ℝ ∞ G (annularOpen D))
    (h : PhysicalJetHasDerivAt T γ F G t) :
    PhysicalJetHasDerivAt T γ (fun s => ContinuousFlexibility.radialPartial (F s)) (ContinuousFlexibility.radialPartial G) t := by
  let L (p : PolarPoint) : ℝ :=
    γ * deriv (fun r => Real.log (T.H (T.radius r))) p.1
  let A (p : PolarPoint) : ℝ := (T.ell (T.radius p.1))⁻¹
  have hlog : ContDiff ℝ ∞ (fun r => Real.log (T.H (T.radius r))) :=
    materialRadius_comp_contDiff hT
      ((hT.1 T.H (by simp)).log (fun r hr => (hT.2.1 r hr).2.1.ne'))
  have hL : ContDiff ℝ ∞ L :=
    contDiff_const.mul ((contDiff_infty_iff_deriv.mp hlog).2.comp contDiff_fst)
  have hA : ContDiff ℝ ∞ A := (materialInvEll_radius_contDiff hT).comp contDiff_fst
  have hFm : ∀ᶠ s in 𝓝 t, ContDiff ℝ ∞ (materialPullback T γ (F s)) :=
    hF.mono fun s hs => contDiff_materialPullback hT hs
  have hGm : ContDiff ℝ ∞ (materialPullback T γ G) := contDiff_materialPullback hT hG
  have hr (f : PolarPoint → ℝ) (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (ContinuousFlexibility.radialPartial f) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact contDiffAt_radialPartial hf.contDiffAt (m := ∞) (by simp)
  have hR := MixedJetHasDerivAt.radialPartial hFm hGm h
  have hLF := MixedJetHasDerivAt.const_mul hFm hGm hL h
  have hV := MixedJetHasDerivAt.add
    (hFm.mono fun s hs => hr _ hs) (hFm.mono fun s hs => hL.mul hs)
    (hr _ hGm) (hL.mul hGm) hR hLF
  have hd := MixedJetHasDerivAt.const_mul
    (hFm.mono fun s hs => (hr _ hs).add (hL.mul hs))
    ((hr _ hGm).add (hL.mul hGm)) hA hV
  apply hd.congr
  · filter_upwards [hF] with s hs
    exact (funext (n02n03_materialPullback_radialPartial hT hs)).symm
  · exact (funext (n02n03_materialPullback_radialPartial hT hG)).symm

/-- The coefficient derivative propagates through both actual fluxes
and through every weighted physical jet of their divergence. -/
theorem physicalJetHasDerivAt_symmetric_divergence
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {A B : ℝ → PolarPoint → ℝ} {A' B' u : PolarPoint → ℝ} {t : ℝ}
    (hT : IsMaterialData D T)
    (hA : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞ (A s) (annularOpen D))
    (hB : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞ (B s) (annularOpen D))
    (hA' : ContDiffOn ℝ ∞ A' (annularOpen D))
    (hB' : ContDiffOn ℝ ∞ B' (annularOpen D))
    (hu : ContDiffOn ℝ ∞ u (annularOpen D))
    (hAd : MixedJetHasDerivAt (fun s p => A s (T.radius p.1, p.2))
      (fun p => A' (T.radius p.1, p.2)) t)
    (hBd : MixedJetHasDerivAt (fun s p => B s (T.radius p.1, p.2))
      (fun p => B' (T.radius p.1, p.2)) t) :
    PhysicalJetHasDerivAt T γ
      (fun s p => ContinuousFlexibility.radialPartial (fun q => A s q * ContinuousFlexibility.angularPartial u q) p +
        ContinuousFlexibility.angularPartial (fun q => A s q * ContinuousFlexibility.radialPartial u q + B s q * ContinuousFlexibility.angularPartial u q) p)
      (fun p => ContinuousFlexibility.radialPartial (fun q => A' q * ContinuousFlexibility.angularPartial u q) p +
        ContinuousFlexibility.angularPartial (fun q => A' q * ContinuousFlexibility.radialPartial u q + B' q * ContinuousFlexibility.angularPartial u q) p) t := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hur := contDiffOn_radialPartial_of_isOpen hU hu
  have hut := contDiffOn_angularPartial_of_isOpen hU hu
  have hF := physicalJetHasDerivAt_coefficient_mul (γ := γ) hT hA hA' hut hAd
  have hG := PhysicalJetHasDerivAt.add hT
    (hA.mono fun s hs => hs.mul hur) (hB.mono fun s hs => hs.mul hut)
    (hA'.mul hur) (hB'.mul hut)
    (physicalJetHasDerivAt_coefficient_mul (γ := γ) hT hA hA' hur hAd)
    (physicalJetHasDerivAt_coefficient_mul (γ := γ) hT hB hB' hut hBd)
  have hFs : ∀ᶠ s in 𝓝 t,
      ContDiffOn ℝ ∞ (fun p => A s p * ContinuousFlexibility.angularPartial u p) (annularOpen D) :=
    hA.mono fun s hs => hs.mul hut
  have hGs : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞
      (fun p => A s p * ContinuousFlexibility.radialPartial u p + B s p * ContinuousFlexibility.angularPartial u p) (annularOpen D) := by
    filter_upwards [hA, hB] with s hs hs'
    exact (hs.mul hur).add (hs'.mul hut)
  exact PhysicalJetHasDerivAt.add hT
    (hFs.mono fun s hs => contDiffOn_radialPartial_of_isOpen hU hs)
    (hGs.mono fun s hs => contDiffOn_angularPartial_of_isOpen hU hs)
    (contDiffOn_radialPartial_of_isOpen hU (hA'.mul hut))
    (contDiffOn_angularPartial_of_isOpen hU ((hA'.mul hur).add (hB'.mul hut)))
    (PhysicalJetHasDerivAt.radialPartial hT hFs (hA'.mul hut) hF)
    (PhysicalJetHasDerivAt.angularPartial hT hGs ((hA'.mul hur).add (hB'.mul hut)) hG)

end ContinuousFlexibility.Statements
