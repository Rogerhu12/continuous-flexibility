import ContinuousFlexibility.Analysis.N04bRootLiteralMaps
import ContinuousFlexibility.Analysis.N04bContinuousInverseGerm

/-!
# Smoothness and full inverse germs of the literal pasted maps

Positive-side agreement makes the pasted chart and height equal to their
smooth root models on a full physical neighborhood. Actual physical
injectivity identifies the positive inverse with the collar inverse.
The inverse function theorem is then applied to the literal pasted chart,
so its partial homeomorphism has precisely that global forward function.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04bPastedRootChart_regular
    (r₀ : ℝ) (side : Bool)
    {Froot Fphysical : PolarPoint → PolarPoint} {S : Set PolarPoint} {p : PolarPoint}
    (hS : IsOpen S) (hp : n04bRootAffine r₀ side p ∈ S)
    (hMatch : EqOn (fun q => Fphysical ((n04bRootAffine r₀ side).symm q)) Froot
      (S ∩ {q : PolarPoint | 0 < q.1}))
    (hF : ContDiffAt ℝ ∞ Froot (n04bRootAffine r₀ side p))
    (hJ : planeJacobian Froot (n04bRootAffine r₀ side p) ≠ 0) :
    ContDiffAt ℝ ∞ (n04bPastedRootChart r₀ side Froot Fphysical) p ∧
      planeJacobian (n04bPastedRootChart r₀ side Froot Fphysical) p ≠ 0 := by
  let e := n04bRootAffine r₀ side
  have he := (n04bRootAffine_contDiff r₀ side).contDiffAt (x := p)
  have hgerm : n04bPastedRootChart r₀ side Froot Fphysical =ᶠ[𝓝 p] Froot ∘ e :=
    n04b_rootSidePaste_germ e hS hp hMatch
  have hmodel : ContDiffAt ℝ ∞ (Froot ∘ e) p := hF.comp p he
  refine ⟨hmodel.congr_of_eventuallyEq hgerm, ?_⟩
  have hEq : planeJacobian (n04bPastedRootChart r₀ side Froot Fphysical) p =
      planeJacobian (Froot ∘ e) p := by
    unfold planeJacobian
    rw [hgerm.fderiv_eq]
  rw [hEq, planeJacobian_comp (he.differentiableAt (by simp))
    (hF.differentiableAt (by simp))]
  exact mul_ne_zero hJ (n04bRootAffine_jacobian_ne_zero r₀ side p)

theorem n04bPastedRootHeight_regular
    (r₀ : ℝ) (side : Bool)
    {hroot hphysical : PolarPoint → ℝ} {S : Set PolarPoint} {p : PolarPoint}
    (hS : IsOpen S) (hp : n04bRootAffine r₀ side p ∈ S)
    (hMatch : EqOn (fun q => hphysical ((n04bRootAffine r₀ side).symm q)) hroot
      (S ∩ {q : PolarPoint | 0 < q.1}))
    (hh : ContDiffAt ℝ ∞ hroot (n04bRootAffine r₀ side p))
    (hpos : 0 < hroot (n04bRootAffine r₀ side p)) :
    ContDiffAt ℝ ∞ (n04bPastedRootHeight r₀ side hroot hphysical) p ∧
      0 < n04bPastedRootHeight r₀ side hroot hphysical p := by
  let e := n04bRootAffine r₀ side
  have hgerm : n04bPastedRootHeight r₀ side hroot hphysical =ᶠ[𝓝 p] hroot ∘ e :=
    n04b_rootSidePaste_germ e hS hp hMatch
  have hmodel : ContDiffAt ℝ ∞ (hroot ∘ e) p :=
    hh.comp p (n04bRootAffine_contDiff r₀ side).contDiffAt
  have hEq : n04bPastedRootHeight r₀ side hroot hphysical p = hroot (e p) :=
    n04b_rootSidePaste_eqOn e hMatch hp
  exact ⟨hmodel.congr_of_eventuallyEq hgerm, hEq.symm ▸ hpos⟩

/-- Physical injectivity identifies the actual positive inverse with the
affine image of the genuine collar inverse. -/
theorem n04bPastedRootInverse_eqOn_collar
    (r₀ : ℝ) (side : Bool)
    {Froot Fphysical G H : PolarPoint → PolarPoint} {g : PolarPoint → ℝ}
    {S T Ω : Set PolarPoint}
    (hMaps : MapsTo G T S) (hRight : RightInvOn G Froot T)
    (hFactor : ∀ p ∈ S, (Froot p).1 = p.1 * g p)
    (hFactorPos : ∀ p ∈ S, 0 < g p)
    (hPhysical : MapsTo (n04bRootAffine r₀ side).symm
      (S ∩ {p : PolarPoint | 0 < p.1}) Ω)
    (hMatch : EqOn (fun q => Fphysical ((n04bRootAffine r₀ side).symm q)) Froot
      (S ∩ {q : PolarPoint | 0 < q.1}))
    (hPhysInj : InjOn Fphysical Ω)
    (hHMaps : MapsTo H (T ∩ {q : PolarPoint | 0 < q.1}) Ω)
    (hHRight : RightInvOn H Fphysical (T ∩ {q : PolarPoint | 0 < q.1})) :
    EqOn (n04bPastedRootInverse r₀ side G H)
      (fun q => (n04bRootAffine r₀ side).symm (G q)) T := by
  intro q hq
  by_cases hq0 : 0 < q.1
  · change (if 0 < q.1 then H q else (n04bRootAffine r₀ side).symm (G q)) = _
    rw [if_pos hq0]
    have hGpos := n04b_collarInverse_first_pos hMaps hRight hFactor hFactorPos hq hq0
    have hGSource : G q ∈ S ∩ {p : PolarPoint | 0 < p.1} :=
      ⟨hMaps hq, hGpos⟩
    apply hPhysInj (hHMaps ⟨hq, hq0⟩) (hPhysical hGSource)
    exact (hHRight ⟨hq, hq0⟩).trans ((hMatch hGSource).trans (hRight hq)).symm
  · exact if_neg hq0

/-- The literal forward and inverse functions have the genuine smooth
inverse germ at every point of their matching collar. -/
theorem n04bPastedRootChart_inverse_germ
    (r₀ : ℝ) (side : Bool)
    {Froot Fphysical G H : PolarPoint → PolarPoint} {g : PolarPoint → ℝ}
    {S T Ω : Set PolarPoint} {p : PolarPoint}
    (hS : IsOpen S) (hT : IsOpen T)
    (hMaps : MapsTo G T S) (hLeft : LeftInvOn G Froot S)
    (hRight : RightInvOn G Froot T) (hG : ContDiffOn ℝ ∞ G T)
    (hFactor : ∀ q ∈ S, (Froot q).1 = q.1 * g q)
    (hFactorPos : ∀ q ∈ S, 0 < g q)
    (hPhysical : MapsTo (n04bRootAffine r₀ side).symm
      (S ∩ {q : PolarPoint | 0 < q.1}) Ω)
    (hMatch : EqOn (fun q => Fphysical ((n04bRootAffine r₀ side).symm q)) Froot
      (S ∩ {q : PolarPoint | 0 < q.1}))
    (hPhysInj : InjOn Fphysical Ω)
    (hHMaps : MapsTo H (T ∩ {q : PolarPoint | 0 < q.1}) Ω)
    (hHRight : RightInvOn H Fphysical (T ∩ {q : PolarPoint | 0 < q.1}))
    (hp : n04bRootAffine r₀ side p ∈ S)
    (hImage : Froot (n04bRootAffine r₀ side p) ∈ T)
    (hF : ContDiffAt ℝ ∞ Froot (n04bRootAffine r₀ side p))
    (hJ : planeJacobian Froot (n04bRootAffine r₀ side p) ≠ 0) :
    ContDiffAt ℝ ∞ (n04bPastedRootInverse r₀ side G H)
        (n04bPastedRootChart r₀ side Froot Fphysical p) ∧
      CanonicalBoundaryInverseGerm (n04bPastedRootChart r₀ side Froot Fphysical)
        (n04bPastedRootInverse r₀ side G H) p := by
  let e := n04bRootAffine r₀ side
  let F := n04bPastedRootChart r₀ side Froot Fphysical
  let J := n04bPastedRootInverse r₀ side G H
  have hEqJ : EqOn J (fun q => e.symm (G q)) T :=
    n04bPastedRootInverse_eqOn_collar r₀ side hMaps hRight hFactor hFactorPos
      hPhysical hMatch hPhysInj hHMaps hHRight
  have hEqF : EqOn F (fun q => Froot (e q)) (e ⁻¹' S) :=
    n04b_rootSidePaste_eqOn e hMatch
  have hFp : F p = Froot (e p) := hEqF hp
  have hFpT : F p ∈ T := by rw [hFp]; exact hImage
  have hJGerm : J =ᶠ[𝓝 (F p)] (fun q => e.symm (G q)) := by
    filter_upwards [hT.mem_nhds hFpT] with q hq
    exact hEqJ hq
  have hJModel : ContDiffAt ℝ ∞ (fun q => e.symm (G q)) (F p) :=
    (n04bRootAffine_symm_contDiff r₀ side).contDiffAt.comp (F p)
      (hG.contDiffAt (hT.mem_nhds hFpT))
  have hJSmooth : ContDiffAt ℝ ∞ J (F p) :=
    hJModel.congr_of_eventuallyEq hJGerm
  have hValue : J (F p) = p := by
    rw [hEqJ hFpT, hFp, hLeft hp]
    exact e.symm_apply_apply p
  have hRightPaste : ∀ᶠ q in 𝓝 (F p), F (J q) = q := by
    filter_upwards [hT.mem_nhds hFpT] with q hq
    rw [hEqJ hq]
    have hSource : e (e.symm (G q)) ∈ S := by
      rw [e.apply_symm_apply]
      exact hMaps hq
    calc
      F (e.symm (G q)) = Froot (e (e.symm (G q))) := hEqF hSource
      _ = Froot (G q) := congrArg Froot (e.apply_symm_apply (G q))
      _ = q := hRight hq
  have hRegular := n04bPastedRootChart_regular r₀ side hS hp hMatch hF hJ
  exact ⟨hJSmooth, n04b_boundaryInverseGerm_of_continuous_rightInverse
    hRegular.1 hRegular.2 hJSmooth.continuousAt hValue hRightPaste⟩

end ContinuousFlexibility.Analysis
