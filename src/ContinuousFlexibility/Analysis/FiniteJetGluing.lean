module

public import ContinuousFlexibility.Analysis.FirstDerivativeGluing

/-!
# Finite regularity from matching ordinary jets

The functions need ordinary smoothness only at the relevant closure
points. Matching actual jets through order n suffices for a C^n piecewise
function on the open ambient domain. No common infinite-order collar or
restriction on how curves cross the interface is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

universe u v w

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem value_eq_of_zero_full_jet {f g : E → F} {x : E}
    (h : iteratedFDeriv ℝ 0 f x = iteratedFDeriv ℝ 0 g x) : f x = g x := by
  have he := congrArg (fun A : E [×0]→L[ℝ] F => A (fun i => Fin.elim0 i)) h
  simpa only [iteratedFDeriv_zero_apply] using he

private theorem full_jet_fderiv_eq_of_successor {f g : E → F} {x : E} (n : ℕ)
    (h : iteratedFDeriv ℝ (n + 1) f x = iteratedFDeriv ℝ (n + 1) g x) :
    iteratedFDeriv ℝ n (fderiv ℝ f) x = iteratedFDeriv ℝ n (fderiv ℝ g) x := by
  ext v w
  have he := congrArg (fun A : E [×(n + 1)]→L[ℝ] F => A (Fin.snoc v w)) h
  simpa only [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last] using he

/-- The actual first derivative is the piecewise selection of the two
actual derivatives, including points on the interface. -/
theorem hasFDerivAt_piecewise_on_domain_of_matching_jets
    {U s : Set E} [DecidablePred (· ∈ s)] {f g : E → F}
    (hf : ∀ x ∈ U ∩ closure s, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ U ∩ closure sᶜ, DifferentiableAt ℝ g x)
    (hmatch : ∀ x ∈ U ∩ frontier s,
      f x = g x ∧ fderiv ℝ f x = fderiv ℝ g x)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (s.piecewise f g)
      (s.piecewise (fderiv ℝ f) (fderiv ℝ g) x) x := by
  by_cases hleft : x ∈ closure s
  · by_cases hright : x ∈ closure sᶜ
    · have hfront : x ∈ frontier s := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨hleft, hright⟩
      have he := hmatch x ⟨hx, hfront⟩
      have hd := hasFDerivAt_piecewise_of_matching_jets (s := s)
        (hf x ⟨hx, hleft⟩).hasFDerivAt
        ((hg x ⟨hx, hright⟩).hasFDerivAt.congr_fderiv he.2.symm) he.1
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
      exact (hf x ⟨hx, hleft⟩).hasFDerivAt.congr_of_eventuallyEq he
  · have hxs : x ∉ s := fun hs => hleft (subset_closure hs)
    have he : s.piecewise f g =ᶠ[𝓝 x] g := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hleft] with y hy
      exact piecewise_eq_of_notMem s f g (fun hs => hy (subset_closure hs))
    rw [piecewise_eq_of_notMem s _ _ hxs]
    exact (hg x ⟨hx, subset_closure hxs⟩).hasFDerivAt.congr_of_eventuallyEq he

/-- Pointwise regularity at every relevant closure point and agreement
of all actual jets through n yield genuine C^n regularity after gluing. -/
theorem contDiffOn_nat_piecewise_of_matching_full_jets
    (n : ℕ) {U s : Set E} [DecidablePred (· ∈ s)] (hU : IsOpen U) :
    ∀ {V : Type (max u w)} [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E → V},
      (∀ x ∈ U ∩ closure s, ContDiffAt ℝ n f x) →
      (∀ x ∈ U ∩ closure sᶜ, ContDiffAt ℝ n g x) →
      (∀ x ∈ U ∩ frontier s, ∀ k : ℕ, k ≤ n →
        iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x) →
      ContDiffOn ℝ n (s.piecewise f g) U := by
  induction n with
  | zero =>
    intro V _ _ f g hf hg hmatch
    apply contDiffOn_zero.mpr
    exact ContinuousOn.piecewise
      (fun x hx => value_eq_of_zero_full_jet (hmatch x hx 0 le_rfl))
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
  | succ n ih =>
    intro V _ _ f g hf hg hmatch
    have hfirst : ∀ x ∈ U ∩ frontier s,
        f x = g x ∧ fderiv ℝ f x = fderiv ℝ g x := by
      intro x hx
      refine ⟨value_eq_of_zero_full_jet (hmatch x hx 0 (Nat.zero_le _)), ?_⟩
      exact value_eq_of_zero_full_jet
        (full_jet_fderiv_eq_of_successor 0 (hmatch x hx 1 (Nat.succ_le_succ (Nat.zero_le n))))
    have hdf : ∀ x ∈ U ∩ closure s, ContDiffAt ℝ n (fderiv ℝ f) x := by
      intro x hx
      exact (hf x hx).fderiv_right (by simp only [Nat.cast_succ, le_refl])
    have hdg : ∀ x ∈ U ∩ closure sᶜ, ContDiffAt ℝ n (fderiv ℝ g) x := by
      intro x hx
      exact (hg x hx).fderiv_right (by simp only [Nat.cast_succ, le_refl])
    have hderivative : ContDiffOn ℝ n (s.piecewise (fderiv ℝ f) (fderiv ℝ g)) U :=
      ih hdf hdg (fun x hx k hk =>
        full_jet_fderiv_eq_of_successor k (hmatch x hx (k + 1) (Nat.succ_le_succ hk)))
    have hle : (1 : ℕ∞ω) ≤ ((n + 1 : ℕ) : ℕ∞ω) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hC : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (s.piecewise f g) U := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        (hU.uniqueDiffOn (𝕜 := ℝ))).mpr
      refine ⟨by simp, s.piecewise (fderiv ℝ f) (fderiv ℝ g), hderivative, ?_⟩
      intro x hx
      exact (hasFDerivAt_piecewise_on_domain_of_matching_jets
        (fun y hy => ((hf y hy).of_le hle).differentiableAt_one)
        (fun y hy => ((hg y hy).of_le hle).differentiableAt_one) hfirst hx).hasFDerivWithinAt
    simpa only [Nat.cast_succ] using hC

end ContinuousFlexibility.Analysis
