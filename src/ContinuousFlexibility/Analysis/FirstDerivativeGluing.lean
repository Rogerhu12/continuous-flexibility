import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Topology.Piecewise

/-!
# Actual first derivatives across a matching interface

Matching values and actual first derivatives give a true derivative of
the piecewise function. The proof joins the two within-derivatives using
the public union theorem. Matching continuous derivative fields then give
genuine C¹ regularity on an open domain, without conditions on how often
a curve crosses the interface.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At a point where the two actual first jets agree, any piecewise
selection has that same actual derivative. -/
theorem hasFDerivAt_piecewise_of_matching_jets
    {s : Set E} [DecidablePred (· ∈ s)] {f g : E → F}
    {x : E} {L : E →L[ℝ] F}
    (hf : HasFDerivAt f L x) (hg : HasFDerivAt g L x) (he : f x = g x) :
    HasFDerivAt (s.piecewise f g) L x := by
  have hvalue : s.piecewise f g x = f x := by
    by_cases hx : x ∈ s
    · exact piecewise_eq_of_mem s f g hx
    · exact (piecewise_eq_of_notMem s f g hx).trans he.symm
  have hleft : HasFDerivWithinAt (s.piecewise f g) L s x :=
    hf.hasFDerivWithinAt.congr (piecewise_eqOn s f g) hvalue
  have hright : HasFDerivWithinAt (s.piecewise f g) L sᶜ x :=
    hg.hasFDerivWithinAt.congr (piecewise_eqOn_compl s f g) (hvalue.trans he)
  have hboth := hleft.union hright
  rw [union_compl_self] at hboth
  exact hboth.hasFDerivAt_of_univ

/-- Smoothness is only required at points in the appropriate closures.
The interface condition concerns the actual full first derivative. -/
theorem contDiffOn_one_piecewise_of_matching_jets
    {U s : Set E} [DecidablePred (· ∈ s)] (hU : IsOpen U) {f g : E → F}
    (hf : ∀ x ∈ U ∩ closure s, ContDiffAt ℝ 1 f x)
    (hg : ∀ x ∈ U ∩ closure sᶜ, ContDiffAt ℝ 1 g x)
    (hmatch : ∀ x ∈ U ∩ frontier s,
      f x = g x ∧ fderiv ℝ f x = fderiv ℝ g x) :
    ContDiffOn ℝ 1 (s.piecewise f g) U := by
  classical
  have hD (x : E) (hx : x ∈ U) :
      HasFDerivAt (s.piecewise f g)
        (s.piecewise (fderiv ℝ f) (fderiv ℝ g) x) x := by
    by_cases hleft : x ∈ closure s
    · by_cases hright : x ∈ closure sᶜ
      · have hfront : x ∈ frontier s := by
          rw [frontier_eq_closure_inter_closure]
          exact ⟨hleft, hright⟩
        have he := hmatch x ⟨hx, hfront⟩
        have hdf := (hf x ⟨hx, hleft⟩).differentiableAt_one
        have hdg := (hg x ⟨hx, hright⟩).differentiableAt_one
        have hd := hasFDerivAt_piecewise_of_matching_jets (s := s)
          hdf.hasFDerivAt (hdg.hasFDerivAt.congr_fderiv he.2.symm) he.1
        by_cases hxs : x ∈ s
        · simpa only [piecewise_eq_of_mem s _ _ hxs] using hd
        · simpa only [piecewise_eq_of_notMem s _ _ hxs, he.2] using hd
      · have hinterior : x ∈ interior s := by
          simpa only [closure_compl, mem_compl_iff, not_not] using hright
        have hxs : x ∈ s := interior_subset hinterior
        have he : s.piecewise f g =ᶠ[𝓝 x] f := by
          filter_upwards [isOpen_interior.mem_nhds hinterior] with y hy
          exact piecewise_eq_of_mem s f g (interior_subset hy)
        rw [piecewise_eq_of_mem s _ _ hxs]
        exact (hf x ⟨hx, hleft⟩).differentiableAt_one.hasFDerivAt.congr_of_eventuallyEq he
    · have hxs : x ∉ s := fun hs => hleft (subset_closure hs)
      have he : s.piecewise f g =ᶠ[𝓝 x] g := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hleft] with y hy
        exact piecewise_eq_of_notMem s f g (fun hs => hy (subset_closure hs))
      rw [piecewise_eq_of_notMem s _ _ hxs]
      exact (hg x ⟨hx, subset_closure hxs⟩).differentiableAt_one.hasFDerivAt.congr_of_eventuallyEq he
  have hcont : ContinuousOn (s.piecewise (fderiv ℝ f) (fderiv ℝ g)) U :=
    ContinuousOn.piecewise (fun x hx => (hmatch x hx).2)
      (fun x hx => ((hf x hx).continuousAt_fderiv (by simp)).continuousWithinAt)
      (fun x hx => ((hg x hx).continuousAt_fderiv (by simp)).continuousWithinAt)
  have hC : ContDiffOn ℝ ((0 : ℕ∞ω) + 1) (s.piecewise f g) U := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (𝕜 := ℝ) (n := 0) hU.uniqueDiffOn).2
    exact ⟨by simp, s.piecewise (fderiv ℝ f) (fderiv ℝ g),
      contDiffOn_zero.mpr hcont, fun x hx => (hD x hx).hasFDerivWithinAt⟩
  simpa only [zero_add] using hC

end ContinuousFlexibility.Analysis
