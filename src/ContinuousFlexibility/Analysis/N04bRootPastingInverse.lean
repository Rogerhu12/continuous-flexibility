import ContinuousFlexibility.Analysis.N04bRootPastingModel
import ContinuousFlexibility.Analysis.N04bRootLiteralGerms

/-!
# Choosing the actual collar inverse for a literal root paste

The local model constructs an injective collar and its genuine smooth
inverse. Its positive target collar is shrunk inside the canonical
interval. The resulting literal inverse keeps the specified physical
inverse at every positive radius.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

namespace N04bRootPastingModel

theorem exists_literal_root_germs
    {r₀ B : ℝ} {side : Bool} {Ω : Set PolarPoint}
    {Fphysical Hphysical : PolarPoint → PolarPoint} {hphysical : PolarPoint → ℝ}
    (M : N04bRootPastingModel r₀ side Ω Fphysical hphysical)
    (hB : 0 < B) (hInj : InjOn Fphysical Ω)
    (hHMaps : MapsTo Hphysical (Ioo (0 : ℝ) B ×ˢ univ) Ω)
    (hHRight : RightInvOn Hphysical Fphysical (Ioo (0 : ℝ) B ×ˢ univ)) :
    ∃ G : PolarPoint → PolarPoint,
      let F := n04bPastedRootChart r₀ side M.rootChart Fphysical
      let h := n04bPastedRootHeight r₀ side M.rootHeight hphysical
      let J := n04bPastedRootInverse r₀ side G Hphysical
      (∀ θ : ℝ, ContDiffAt ℝ ∞ F (r₀, θ) ∧ ContDiffAt ℝ ∞ h (r₀, θ) ∧
        planeJacobian F (r₀, θ) ≠ 0 ∧ 0 < h (r₀, θ) ∧
        CanonicalBoundaryInverseGerm F J (r₀, θ)) ∧
      (∀ q : PolarPoint, q.1 = 0 → ContDiffAt ℝ ∞ J q) := by
  obtain ⟨η, hη, hMaps₀, hLeft, hRight₀, hSmooth₀, _⟩ :=
    n04b_exists_cylindrical_collar_inverse M.radius_pos Real.pi_ne_zero
      (fun p hp => (M.chart_smooth p hp).contDiffWithinAt)
      M.angle_pos M.jacobian_pos (fun r _ θ => M.period r θ) M.axis
  let V : Set PolarPoint :=
    Ioo (-M.radius / 2) (M.radius / 2) ×ˢ (univ : Set ℝ)
  let G := Function.invFunOn M.rootChart V
  let η' := min η B
  let W : Set PolarPoint := Ioo (-η') η' ×ˢ (univ : Set ℝ)
  let e := n04bRootAffine r₀ side
  let F := n04bPastedRootChart r₀ side M.rootChart Fphysical
  let h := n04bPastedRootHeight r₀ side M.rootHeight hphysical
  let J := n04bPastedRootInverse r₀ side G Hphysical
  have hη' : 0 < η' := lt_min_iff.mpr ⟨hη, hB⟩
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_univ
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_univ
  have hVSub : V ⊆ Ioo (-M.radius) M.radius ×ˢ (univ : Set ℝ) := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1, M.radius_pos],
      by linarith [hp.1.2, M.radius_pos]⟩, mem_univ _⟩
  have hWSub : W ⊆ Ioo (-η) η ×ˢ (univ : Set ℝ) := by
    intro q hq
    have heη : η' ≤ η := min_le_left _ _
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩
  have hMaps : MapsTo G W V := fun _ hq => hMaps₀ (hWSub hq)
  have hRight : RightInvOn G M.rootChart W := fun _ hq => hRight₀ (hWSub hq)
  have hSmooth : ContDiffOn ℝ ∞ G W := hSmooth₀.mono hWSub
  have hPhysical : MapsTo e.symm (V ∩ {p : PolarPoint | 0 < p.1}) Ω :=
    fun _ hp => M.physical ⟨hVSub hp.1, hp.2⟩
  have hMatch : EqOn (fun p => Fphysical (e.symm p)) M.rootChart
      (V ∩ {p : PolarPoint | 0 < p.1}) :=
    fun _ hp => M.chart_match ⟨hVSub hp.1, hp.2⟩
  have hHeight : EqOn (fun p => hphysical (e.symm p)) M.rootHeight
      (V ∩ {p : PolarPoint | 0 < p.1}) :=
    fun _ hp => M.height_match ⟨hVSub hp.1, hp.2⟩
  have hPositiveTarget : W ∩ {q : PolarPoint | 0 < q.1} ⊆
      Ioo (0 : ℝ) B ×ˢ (univ : Set ℝ) := by
    intro q hq
    exact ⟨⟨hq.2, hq.1.1.2.trans_le (min_le_right _ _)⟩, mem_univ _⟩
  have hHMaps' : MapsTo Hphysical (W ∩ {q : PolarPoint | 0 < q.1}) Ω :=
    fun _ hq => hHMaps (hPositiveTarget hq)
  have hHRight' : RightInvOn Hphysical Fphysical (W ∩ {q : PolarPoint | 0 < q.1}) :=
    fun _ hq => hHRight (hPositiveTarget hq)
  have hEqJ : EqOn J (fun q => e.symm (G q)) W :=
    n04bPastedRootInverse_eqOn_collar r₀ side hMaps hRight
      (fun p _ => M.factor p) (fun p hp => M.factor_pos p (hVSub hp))
      hPhysical hMatch hInj hHMaps' hHRight'
  refine ⟨G, ?_, ?_⟩
  · intro θ
    have hp : e (r₀, θ) ∈ V := by
      rw [n04bRootAffine_at_root]
      exact ⟨⟨by linarith [M.radius_pos], by linarith [M.radius_pos]⟩, mem_univ _⟩
    have hImage : M.rootChart (e (r₀, θ)) ∈ W := by
      rw [n04bRootAffine_at_root]
      refine ⟨?_, mem_univ _⟩
      rw [M.axis θ]
      exact ⟨neg_lt_zero.mpr hη', hη'⟩
    have hf := n04bPastedRootChart_regular r₀ side hV hp hMatch
      (M.chart_smooth _ (hVSub hp)) (M.jacobian_pos _ (hVSub hp)).ne'
    have hh := n04bPastedRootHeight_regular r₀ side hV hp hHeight
      (M.height_smooth _ (hVSub hp)) (M.height_pos _ (hVSub hp))
    have hi := n04bPastedRootChart_inverse_germ r₀ side hV hW hMaps hLeft
      hRight hSmooth (fun p _ => M.factor p)
      (fun p hp => M.factor_pos p (hVSub hp)) hPhysical hMatch hInj
      hHMaps' hHRight' hp hImage (M.chart_smooth _ (hVSub hp))
      (M.jacobian_pos _ (hVSub hp)).ne'
    exact ⟨hf.1, hh.1, hf.2, hh.2, hi.2⟩
  · intro q hq
    have hqW : q ∈ W := by
      refine ⟨?_, mem_univ _⟩
      rw [hq]
      exact ⟨neg_lt_zero.mpr hη', hη'⟩
    have hEq : J =ᶠ[𝓝 q] (fun y => e.symm (G y)) := by
      filter_upwards [hW.mem_nhds hqW] with y hy
      exact hEqJ hy
    have hModel : ContDiffAt ℝ ∞ (fun y => e.symm (G y)) q :=
      (n04bRootAffine_symm_contDiff r₀ side).contDiffAt.comp q
        (hSmooth.contDiffAt (hW.mem_nhds hqW))
    exact hModel.congr_of_eventuallyEq hEq

end N04bRootPastingModel
end ContinuousFlexibility.Analysis
