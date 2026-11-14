module

public import ContinuousFlexibility.Analysis.FlowJetLinearization

/-!
# Actual nonlinear inverse jets and their triangular estimate

A genuine local right-inverse identity identifies the first derivative
from the left inverse of the actual forward derivative. At every higher
order, subtracting the forward linearization leaves only nonlinear
partition terms, all involving lower inverse jets. These statements
hold at a point and therefore apply to inverses on open coordinate strips.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual derivative of a local inverse equals the specified
left inverse of the actual forward derivative. -/
theorem nonlinearInverse_fderiv_eq
    {f : E → F} {g : F → E} {x : F}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x)
    (hfg : f ∘ g =ᶠ[𝓝 x] (id : F → F))
    (L : F →L[ℝ] E)
    (hL : L.comp (fderiv ℝ f (g x)) = ContinuousLinearMap.id ℝ E) :
    fderiv ℝ g x = L := by
  have hcomp : (fderiv ℝ f (g x)).comp (fderiv ℝ g x) =
      ContinuousLinearMap.id ℝ F := by
    rw [← fderiv_comp x (hf.differentiableAt (by simp))
      (hg.differentiableAt (by simp)), hfg.fderiv_eq, fderiv_id]
  apply ContinuousLinearMap.ext
  intro v
  have hleft := congrArg (fun A : E →L[ℝ] E => A (fderiv ℝ g x v)) hL
  have hright := congrArg (fun A : F →L[ℝ] F => A v) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hleft hright
  exact hleft.symm.trans (congrArg L hright)

/-- The initial quantitative input for the inverse induction is only
the norm of the true inverse first derivative. -/
theorem nonlinearInverse_firstJet_norm
    {f : E → F} {g : F → E} {x : F}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x)
    (hfg : f ∘ g =ᶠ[𝓝 x] (id : F → F))
    (L : F →L[ℝ] E)
    (hL : L.comp (fderiv ℝ f (g x)) = ContinuousLinearMap.id ℝ E) :
    ‖iteratedFDeriv ℝ 1 g x‖ = ‖L‖ := by
  rw [norm_iteratedFDeriv_one, nonlinearInverse_fderiv_eq hf hg hfg L hL]

/-- The actual higher inverse jet is controlled by the original field
jets and strictly lower inverse jets. The factor norm L has derivative
weight zero; no inverse-jet bound is assumed. -/
theorem nonlinearInverse_highJet_norm_le
    {f : E → F} {g : F → E} {x : F}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x)
    (hfg : f ∘ g =ᶠ[𝓝 x] (id : F → F))
    (L : F →L[ℝ] E)
    (hL : L.comp (fderiv ℝ f (g x)) = ContinuousLinearMap.id ℝ E)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖iteratedFDeriv ℝ n g x‖ ≤ ‖L‖ *
      ∑ c : OrderedFinpartition n,
        if 2 ≤ c.length then
          ‖iteratedFDeriv ℝ c.length f (g x)‖ *
            ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) g x‖
        else 0 := by
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
      funext v
      simp only [ContinuousLinearMap.id_apply, id_eq]
    rw [← hid]
    exact flowJet_iteratedFDeriv_clm_eq_zero (ContinuousLinearMap.id ℝ F) hn x
  have hbalance : Z + D.compContinuousMultilinearMap Y = 0 := hseries.symm.trans hzero
  have hvalue (v : Fin n → F) : Y v = -L (Z v) := by
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
    calc
      Y v = L (D (Y v)) := hleft'.symm
      _ = L (-Z v) := congrArg L hDvalue
      _ = -L (Z v) := L.map_neg _
  have hYZ : ‖Y‖ ≤ ‖L‖ * ‖Z‖ := by
    apply ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro v
    rw [hvalue v, norm_neg]
    calc
      ‖L (Z v)‖ ≤ ‖L‖ * ‖Z v‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖Z‖ * ∏ i, ‖v i‖) :=
        mul_le_mul_of_nonneg_left (Z.le_opNorm v) (norm_nonneg L)
      _ = (‖L‖ * ‖Z‖) * ∏ i, ‖v i‖ := (mul_assoc _ _ _).symm
  exact hYZ.trans (mul_le_mul_of_nonneg_left
    (flowJet_linearization_remainder_bound_at hf hg (by omega : 0 < n))
    (norm_nonneg L))

end ContinuousFlexibility.Analysis
