import ContinuousFlexibility.Analysis.CompactParameterIntegral
import ContinuousFlexibility.Analysis.ScalarParameterInverse
import ContinuousFlexibility.Analysis.ReturnCorrectionDisplacementRegularity

/-!
# The removable divided difference in a parameter family

The actual angular derivative of a jointly smooth scalar family is
jointly smooth. Integration along the segment between two variable
arguments therefore proves parameter smoothness of the divided
difference, including the locus where those arguments agree.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem scalarParameterAngularDerivative_contDiffOn
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hI : IsOpen I)
    (hF : ContDiffOn ℝ ∞ (fun p : PolarPoint => F p.1 p.2) (I ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint => deriv (F p.1) p.2) (I ×ˢ univ) := by
  have hU : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hA : ContDiffOn ℝ ∞
      (angularPartial (fun p : PolarPoint => F p.1 p.2)) (I ×ˢ univ) := by
    intro p hp
    exact (contDiffAt_angularPartial (hF.contDiffAt (hU.mem_nhds hp))
      (m := ∞) (by simp)).contDiffWithinAt
  apply hA.congr
  intro p hp
  exact (hasDerivAt_angular_slice
    ((hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))).deriv

theorem scalarParameter_dslope_comp_contDiffOn
    {I : Set ℝ} {G : ℝ → ℝ → ℝ} {X E : PolarPoint → ℝ}
    (hI : IsOpen I)
    (hG : ContDiffOn ℝ ∞ (fun p : PolarPoint => G p.1 p.2) (I ×ˢ univ))
    (hX : ContDiffOn ℝ ∞ X (I ×ˢ univ))
    (hE : ContDiffOn ℝ ∞ E (I ×ˢ univ)) :
    ContDiffOn ℝ ∞
      (fun p : PolarPoint => dslope (G p.1) (X p) (X p + E p)) (I ×ˢ univ) := by
  let H : PolarPoint × ℝ → ℝ := fun q => deriv (G q.1.1) (X q.1 + q.2 * E q.1)
  have hU : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hDG := scalarParameterAngularDerivative_contDiffOn hI hG
  have hH : ∀ p ∈ I ×ˢ (univ : Set ℝ), ∀ a : ℝ, |a| < 3 →
      ContDiffAt ℝ (⊤ : ℕ∞) H (p, a) := by
    intro p hp a _
    have hx : ContDiffAt ℝ ∞ (fun q : PolarPoint × ℝ => X q.1) (p, a) :=
      (hX.contDiffAt (hU.mem_nhds hp)).comp (p, a) contDiffAt_fst
    have he : ContDiffAt ℝ ∞ (fun q : PolarPoint × ℝ => E q.1) (p, a) :=
      (hE.contDiffAt (hU.mem_nhds hp)).comp (p, a) contDiffAt_fst
    have harg : ContDiffAt ℝ ∞
        (fun q : PolarPoint × ℝ => (q.1.1, X q.1 + q.2 * E q.1)) (p, a) :=
      contDiffAt_fst.fst.prodMk (hx.add (contDiffAt_snd.mul he))
    exact (hDG.contDiffAt (hU.mem_nhds
      (show (p.1, X p + a * E p) ∈ I ×ˢ univ from ⟨hp.1, mem_univ _⟩))).comp
        (p, a) harg
  have hi : ContDiffOn ℝ ∞ (fun p => ∫ a in (0 : ℝ)..1, H (p, a)) (I ×ˢ univ) :=
    contDiffOn_compactParameterIntegral hU hH
  apply hi.congr
  intro p hp
  have hg : ContDiff ℝ ∞ (G p.1) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    exact (hG.contDiffAt (hU.mem_nhds
      (show (p.1, θ) ∈ I ×ˢ univ from ⟨hp.1, mem_univ _⟩))).comp θ
      (contDiffAt_const.prodMk contDiffAt_id)
  exact returnCorrection_dslope_integral (hg.of_le (by simp)) (X p) (E p)

end ContinuousFlexibility.Statements
