import ContinuousFlexibility.Analysis.NonlinearInverseJetTriangle

/-!
# Exact finite boundary inverse jet formulas

The local inverse equation gives an algebraic formula for each positive
ordinary inverse jet. All nonlinear terms use strictly smaller inverse
orders. The maps need only be smooth at the actual boundary base points;
no common smooth extension in the parameter is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology BigOperators ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Removing the actual forward linearization leaves precisely the
nonlinear partition terms, as an equality of evaluated ordinary jets. -/
theorem n04Realization_linearization_remainder_apply
    {f : E → F} {g : F → E} {x : F}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (hn : 0 < n) (v : Fin n → F) :
    iteratedFDeriv ℝ n
        ((f - (fderiv ℝ f (g x) : E → F)) ∘ g) x v =
      ∑ c : OrderedFinpartition n,
        if 2 ≤ c.length then
          iteratedFDeriv ℝ c.length f (g x)
            (fun i => iteratedFDeriv ℝ (c.partSize i) g x (v ∘ c.emb i))
        else 0 := by
  classical
  let D : E →L[ℝ] F := fderiv ℝ f (g x)
  let R : E → F := f - (D : E → F)
  have hR : ContDiffAt ℝ ∞ R (g x) := hf.sub D.contDiff.contDiffAt
  have hdR : HasFDerivAt R (D - D) (g x) :=
    (hf.differentiableAt (by simp)).hasFDerivAt.sub D.hasFDerivAt
  have hRone : iteratedFDeriv ℝ 1 R (g x) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_one, hdR.fderiv, sub_self, norm_zero]
  have hRhigher (j : ℕ) (hj : 2 ≤ j) :
      iteratedFDeriv ℝ j R (g x) = iteratedFDeriv ℝ j f (g x) := by
    change iteratedFDeriv ℝ j (f - (D : E → F)) (g x) = _
    rw [iteratedFDeriv_sub_apply
      (hf.of_le (by simp : (j : ℕ∞ω) ≤ ∞))
      D.contDiff.contDiffAt, flowJet_iteratedFDeriv_clm_eq_zero D hj, sub_zero]
  have hcomp : iteratedFDeriv ℝ n (R ∘ g) x =
      ∑ c : OrderedFinpartition n,
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length R (g x))
          (fun i => iteratedFDeriv ℝ (c.partSize i) g x) :=
    iteratedFDeriv_comp hR hg (by simp : (n : ℕ∞ω) ≤ ∞)
  have heval := congrArg (fun A : F [×n]→L[ℝ] F => A v) hcomp
  simp only [ContinuousMultilinearMap.sum_apply,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply] at heval
  refine heval.trans (Finset.sum_congr rfl (fun c _ => ?_))
  by_cases hc : 2 ≤ c.length
  · rw [if_pos hc, hRhigher c.length hc]
  · have hlen : c.length = 1 := by
      have hpos := c.length_pos hn
      omega
    have hzero : iteratedFDeriv ℝ c.length R (g x) = 0 := by
      rw [hlen]
      exact hRone
    rw [if_neg hc, hzero, ContinuousMultilinearMap.zero_apply]

/-- The actual higher inverse jet is an algebraic expression in the
first inverse differential, forward jets and lower inverse jets. -/
theorem n04Realization_inverse_higherJet_apply
    {f : E → F} {g : F → E} {x : F}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x)
    (hfg : f ∘ g =ᶠ[𝓝 x] (id : F → F))
    (L : F →L[ℝ] E)
    (hL : L.comp (fderiv ℝ f (g x)) = ContinuousLinearMap.id ℝ E)
    {n : ℕ} (hn : 2 ≤ n) (v : Fin n → F) :
    iteratedFDeriv ℝ n g x v =
      -L (∑ c : OrderedFinpartition n,
        if 2 ≤ c.length then
          iteratedFDeriv ℝ c.length f (g x)
            (fun i => iteratedFDeriv ℝ (c.partSize i) g x (v ∘ c.emb i))
        else 0) := by
  classical
  let D : E →L[ℝ] F := fderiv ℝ f (g x)
  let R : E → F := f - (D : E → F)
  let Y : F [×n]→L[ℝ] E := iteratedFDeriv ℝ n g x
  let Z : F [×n]→L[ℝ] F := iteratedFDeriv ℝ n (R ∘ g) x
  have hR : ContDiffAt ℝ ∞ R (g x) := hf.sub D.contDiff.contDiffAt
  have hRg : ContDiffAt ℝ ∞ (R ∘ g) x := hR.comp x hg
  have hDg : ContDiffAt ℝ ∞ ((D : E → F) ∘ g) x :=
    D.contDiff.contDiffAt.comp x hg
  have he : f ∘ g = (R ∘ g) + ((D : E → F) ∘ g) := by
    funext y
    exact (sub_add_cancel (f (g y)) (D (g y))).symm
  have hseries : iteratedFDeriv ℝ n (f ∘ g) x =
      Z + D.compContinuousMultilinearMap Y := by
    rw [he, iteratedFDeriv_add_apply
      (hRg.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      (hDg.of_le (by simp : (n : ℕ∞ω) ≤ ∞)),
      D.iteratedFDeriv_comp_left hg (by simp : (n : ℕ∞ω) ≤ ∞)]
  have hzero : iteratedFDeriv ℝ n (f ∘ g) x = 0 := by
    rw [(hfg.iteratedFDeriv ℝ n).self_of_nhds]
    have hid : (ContinuousLinearMap.id ℝ F : F → F) = id := by
      funext w
      simp only [ContinuousLinearMap.id_apply, id_eq]
    rw [← hid]
    exact flowJet_iteratedFDeriv_clm_eq_zero (ContinuousLinearMap.id ℝ F) hn x
  have hbalance : Z + D.compContinuousMultilinearMap Y = 0 := hseries.symm.trans hzero
  have hv := congrArg (fun A : F [×n]→L[ℝ] F => A v) hbalance
  have hv' : Z v + D (Y v) = 0 := by
    simpa only [ContinuousMultilinearMap.add_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousMultilinearMap.zero_apply] using hv
  have hDvalue : D (Y v) = -Z v := by
    have h := congrArg (fun w : F => -Z v + w) hv'
    simpa only [← add_assoc, neg_add_cancel, zero_add, add_zero] using h
  have hleft := congrArg (fun A : E →L[ℝ] E => A (Y v)) hL
  have hleft' : L (D (Y v)) = Y v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, D] using hleft
  have hvalue : Y v = -L (Z v) := by
    calc
      Y v = L (D (Y v)) := hleft'.symm
      _ = L (-Z v) := congrArg L hDvalue
      _ = -L (Z v) := L.map_neg _
  exact hvalue.trans (congrArg (fun y => -L y)
    (n04Realization_linearization_remainder_apply hf hg (by omega) v))

end ContinuousFlexibility.Analysis
