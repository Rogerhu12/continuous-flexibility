import ContinuousFlexibility.Analysis.N01cCosineFlowIdentities
import ContinuousFlexibility.Analysis.OneHighCircleFlowInterior
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Interior spatial regularity of the supplied ordinary flow

The explicit inverse of the cosine coordinate is smooth at every
physical interior point. Pulling back the genuine compact-flow
regularity therefore gives the actual radial and angular regularity of
the original ordinary trajectories.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

def rootCosineInverse (l h r : ℝ) : ℝ :=
  Real.arccos (1 - 2 * ((r - l) / (h - l)))

private theorem n01c_rootCosineInverse_argument_mem
    {l h r : ℝ} (hlh : l < h) (hr : r ∈ Ioo l h) :
    1 - 2 * ((r - l) / (h - l)) ∈ Ioo (-1 : ℝ) 1 := by
  have hwidth : 0 < h - l := sub_pos.mpr hlh
  have hlow : 0 < (r - l) / (h - l) := div_pos (sub_pos.mpr hr.1) hwidth
  have hhigh : (r - l) / (h - l) < 1 :=
    (div_lt_one hwidth).mpr (by linarith [hr.2])
  constructor <;> nlinarith

theorem rootCosineInverse_mem_Ioo
    {l h r : ℝ} (hlh : l < h) (hr : r ∈ Ioo l h) :
    rootCosineInverse l h r ∈ Ioo (0 : ℝ) Real.pi := by
  have hb := n01c_rootCosineInverse_argument_mem hlh hr
  exact ⟨Real.arccos_pos.mpr hb.2, Real.arccos_lt_pi.mpr hb.1⟩

theorem rootCosinePath_inverse
    {l h r : ℝ} (hlh : l < h) (hr : r ∈ Ioo l h) :
    rootCosinePath l h (rootCosineInverse l h r) = r := by
  have hb := n01c_rootCosineInverse_argument_mem hlh hr
  dsimp only [rootCosinePath, rootCosineInverse]
  rw [Real.cos_arccos hb.1.le hb.2.le]
  field_simp [(sub_pos.mpr hlh).ne'] <;> ring

theorem contDiffAt_rootCosineInverse
    {l h r : ℝ} (hlh : l < h) (hr : r ∈ Ioo l h) :
    ContDiffAt ℝ ∞ (rootCosineInverse l h) r := by
  have hb := n01c_rootCosineInverse_argument_mem hlh hr
  have harg : ContDiff ℝ ∞
      (fun x : ℝ => 1 - 2 * ((x - l) / (h - l))) :=
    contDiff_const.sub
      (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const (h - l)))
  exact (Real.contDiffAt_arccos (ne_of_gt hb.1) (ne_of_lt hb.2)).comp r harg.contDiffAt

theorem rootCosinePath_surjOn
    {l h : ℝ} (hlh : l < h) :
    SurjOn (rootCosinePath l h) (Icc (0 : ℝ) Real.pi) (Icc l h) := by
  intro r hr
  by_cases hrl : r = l
  · subst r
    exact ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, rootCosinePath_zero l h⟩
  by_cases hrh : r = h
  · subst r
    exact ⟨Real.pi, ⟨Real.pi_pos.le, le_rfl⟩, rootCosinePath_pi l h⟩
  have hi : r ∈ Ioo l h :=
    ⟨lt_of_le_of_ne hr.1 (Ne.symm hrl), lt_of_le_of_ne hr.2 hrh⟩
  have ht := rootCosineInverse_mem_Ioo hlh hi
  exact ⟨rootCosineInverse l h r, ⟨ht.1.le, ht.2.le⟩, rootCosinePath_inverse hlh hi⟩

theorem contDiffOn_of_rootCosinePullback
    {l h : ℝ} {F : PolarPoint → ℝ} (hlh : l < h)
    (hF : ∀ t ∈ Ioo (0 : ℝ) Real.pi, ∀ θ : ℝ,
      ContDiffAt ℝ ∞ (fun p : PolarPoint => F (rootCosinePath l h p.1, p.2)) (t, θ)) :
    ContDiffOn ℝ ∞ F (Ioo l h ×ˢ (univ : Set ℝ)) := by
  intro p hp
  have hinv : ContDiffAt ℝ ∞
      (fun q : PolarPoint => (rootCosineInverse l h q.1, q.2)) p :=
    ((contDiffAt_rootCosineInverse hlh hp.1).comp p contDiffAt_fst).prodMk contDiffAt_snd
  have hc := (hF (rootCosineInverse l h p.1)
    (rootCosineInverse_mem_Ioo hlh hp.1) p.2).comp p hinv
  have he : F =ᶠ[𝓝 p] (fun q : PolarPoint =>
      F (rootCosinePath l h (rootCosineInverse l h q.1), q.2)) := by
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∈ Ioo l h :=
      continuous_fst.continuousAt.preimage_mem_nhds (Ioo_mem_nhds hp.1.1 hp.1.2)
    filter_upwards [hnear] with q hq
    rw [rootCosinePath_inverse hlh hq]
  exact (hc.congr_of_eventuallyEq he).contDiffWithinAt

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

theorem contDiffOn_minusFlow_of_cosineSpeed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ)
    (hG : ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p))) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint => C.minusFlow z m p.1 p.2)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  apply contDiffOn_of_rootCosinePullback (hA.2.2.1.1 m).2.1
  intro t ht θ
  exact circleFlow_contDiffAt hG Real.pi_pos (componentCosineSpeed_periodic hS z m)
    (continuousOn_componentCosineFlow hA hB hz m)
    (componentCosineFlow_initial hB hz m)
    (fun r hr α => hasDerivAt_componentCosineFlow hS hT hA hB hz m α hr) ht

end ContinuousFlexibility.Statements
