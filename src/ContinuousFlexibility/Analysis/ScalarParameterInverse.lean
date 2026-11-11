import ContinuousFlexibility.Analysis.ReturnFlowInverseRegularity

/-!
# Actual inverse curves in a smooth scalar parameter family

Strict positivity and an actual right inverse determine the inverse
family. The triangular inverse function theorem supplies its joint
smoothness, and differentiating the genuine inverse identity gives
the parameter derivative. Neither conclusion assumes inverse
regularity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

theorem scalarParameter_comp_contDiffOn
    {I : Set ℝ} {F G : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun p : PolarPoint => F p.1 p.2) (I ×ˢ univ))
    (hG : ContDiffOn ℝ ∞ (fun p : PolarPoint => G p.1 p.2) (I ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint => F p.1 (G p.1 p.2)) (I ×ˢ univ) := by
  have h := hF.comp (contDiffOn_fst.prodMk hG)
    (fun p hp => show (p.1, G p.1 p.2) ∈ I ×ˢ univ from ⟨hp.1, mem_univ _⟩)
  apply h.congr
  intro p _
  rfl

theorem scalarParameterInverse_contDiffOn
    {I : Set ℝ} {F G : ℝ → ℝ → ℝ} (hI : IsOpen I)
    (hF : ContDiffOn ℝ ∞ (fun p : PolarPoint => F p.1 p.2) (I ×ˢ univ))
    (hpos : ∀ t ∈ I, ∀ θ, 0 < deriv (F t) θ)
    (hright : ∀ t ∈ I, ∀ θ, F t (G t θ) = θ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint => G p.1 p.2) (I ×ˢ univ) := by
  intro p hp
  have hinj : ∀ᶠ t in 𝓝 p.1, Function.Injective (F t) := by
    filter_upwards [hI.mem_nhds hp.1] with t ht
    exact (strictMono_of_deriv_pos (hpos t ht)).injective
  have hs := returnFlow_invFun_contDiffAt
    (hF.contDiffAt ((hI.prod isOpen_univ).mem_nhds
      (show (p.1, G p.1 p.2) ∈ I ×ˢ univ from ⟨hp.1, mem_univ _⟩)))
    (by simp) (hpos p.1 hp.1 (G p.1 p.2)).ne' hinj
  have hpoint : (p.1, F p.1 (G p.1 p.2)) = p :=
    Prod.ext rfl (hright p.1 hp.1 p.2)
  rw [hpoint] at hs
  apply ContDiffAt.contDiffWithinAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [(hI.prod isOpen_univ).mem_nhds hp] with q hq
  have heq := Function.leftInverse_invFun
    (strictMono_of_deriv_pos (hpos q.1 hq.1)).injective (G q.1 q.2)
  rw [hright q.1 hq.1 q.2] at heq
  exact heq.symm

theorem scalarParameterInverse_hasDerivAt
    {I : Set ℝ} {F G : ℝ → ℝ → ℝ} (hI : IsOpen I)
    (hF : ContDiffOn ℝ ∞ (fun p : PolarPoint => F p.1 p.2) (I ×ˢ univ))
    (hpos : ∀ t ∈ I, ∀ θ, 0 < deriv (F t) θ)
    (hright : ∀ t ∈ I, ∀ θ, F t (G t θ) = θ)
    {t : ℝ} (ht : t ∈ I) (θ : ℝ) :
    HasDerivAt (fun s => G s θ)
      (-deriv (fun s => F s (G t θ)) t / deriv (F t) (G t θ)) t := by
  have hG := scalarParameterInverse_contDiffOn hI hF hpos hright
  have hGdiff : DifferentiableAt ℝ (fun p : PolarPoint => G p.1 p.2) (t, θ) :=
    (hG.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)).differentiableAt
      (by simp)
  have hg : HasDerivAt (fun s => G s θ) (deriv (fun s => G s θ) t) t :=
    (hasDerivAt_radial_slice hGdiff).differentiableAt.hasDerivAt
  have hFdiff : DifferentiableAt ℝ (fun p : PolarPoint => F p.1 p.2) (t, G t θ) :=
    (hF.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)).differentiableAt
      (by simp)
  let A : PolarPoint →L[ℝ] ℝ := fderiv ℝ (fun p : PolarPoint => F p.1 p.2) (t, G t θ)
  have hchain : HasDerivAt (fun s => F s (G s θ))
      (A (1, deriv (fun s => G s θ) t)) t := by
    simpa only [Function.comp_def, A] using
      hFdiff.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk hg)
  have heq : (fun _ : ℝ => θ) =ᶠ[𝓝 t] (fun s => F s (G s θ)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (hright s hs θ).symm
  have hzero : A (1, deriv (fun s => G s θ) t) = 0 :=
    (hchain.congr_of_eventuallyEq heq).unique (hasDerivAt_const t θ)
  have hfirst : deriv (fun s => F s (G t θ)) t = A (1, 0) :=
    (hasDerivAt_radial_slice hFdiff).deriv
  have hsecond : deriv (F t) (G t θ) = A (0, 1) :=
    (hasDerivAt_angular_slice hFdiff).deriv
  have hcoord : A (1, deriv (fun s => G s θ) t) =
      deriv (fun s => F s (G t θ)) t +
        deriv (fun s => G s θ) t * deriv (F t) (G t θ) := by
    have h := congrArg
      (fun L : PolarPoint →L[ℝ] ℝ => L (1, deriv (fun s => G s θ) t))
      (returnFlow_linearMap_coordinates A)
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
      mul_one, ← hfirst, ← hsecond, mul_comm] using h
  rw [hcoord] at hzero
  apply hg.congr_deriv
  apply (eq_div_iff (hpos t ht (G t θ)).ne').mpr
  linarith only [hzero]

end ContinuousFlexibility.Statements

