import ContinuousFlexibility.Analysis.CylinderMixedJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Local identities for the actual mixed coordinate derivatives. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

theorem mixedDerivative_congr_of_eventuallyEq
    {f g : PolarPoint → ℝ} {p : PolarPoint} (h : f =ᶠ[𝓝 p] g) (a b : ℕ) :
    mixedDerivative a b f p = mixedDerivative a b g p := by
  have hc : ∀ᶠ r in 𝓝 p.1, ∀ᶠ θ in 𝓝 p.2, f (r, θ) = g (r, θ) := h.curry_nhds
  have hr : (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) =ᶠ[𝓝 p.1]
      (fun r => iteratedDeriv b (fun θ => g (r, θ)) p.2) := by
    filter_upwards [hc] with r hr
    have hθ : (fun θ => f (r, θ)) =ᶠ[𝓝 p.2] fun θ => g (r, θ) := hr
    exact hθ.iteratedDeriv_eq b
  exact hr.iteratedDeriv_eq a

theorem mixedDerivative_congr_on_open
    {U : Set PolarPoint} {f g : PolarPoint → ℝ} (hU : IsOpen U) (hfg : EqOn f g U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative a b f p = mixedDerivative a b g p := by
  apply mixedDerivative_congr_of_eventuallyEq (a := a) (b := b)
  filter_upwards [hU.mem_nhds hp] with q hq
  exact hfg hq

theorem mixedDerivative_sub_of_contDiffOn
    {U : Set PolarPoint} {f g : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative a b (fun q => f q - g q) p =
      mixedDerivative a b f p - mixedDerivative a b g p := by
  have hnear : ∀ᶠ r in 𝓝 p.1, (r, p.2) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
  have heq : (fun r => iteratedDeriv b (fun θ => f (r, θ) - g (r, θ)) p.2)
      =ᶠ[𝓝 p.1] (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2 -
        iteratedDeriv b (fun θ => g (r, θ)) p.2) := by
    filter_upwards [hnear] with r hr
    have hfs : ContDiffAt ℝ (b : ℕ∞ω) (fun θ => f (r, θ)) p.2 := by
      simpa only [Function.comp_def] using
        (((hf.contDiffAt (hU.mem_nhds hr)).comp p.2
          ((contDiffAt_const (c := r)).prodMk contDiffAt_id)).of_le
            (show (b : ℕ∞ω) ≤ ∞ by simp))
    have hgs : ContDiffAt ℝ (b : ℕ∞ω) (fun θ => g (r, θ)) p.2 := by
      simpa only [Function.comp_def] using
        (((hg.contDiffAt (hU.mem_nhds hr)).comp p.2
          ((contDiffAt_const (c := r)).prodMk contDiffAt_id)).of_le
            (show (b : ℕ∞ω) ≤ ∞ by simp))
    exact iteratedDeriv_fun_sub hfs hgs
  have hfr : ContDiffAt ℝ (a : ℕ∞ω)
      (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) p.1 := by
    have h := ((contDiffOn_mixedDerivative hU hf 0 b).contDiffAt (hU.mem_nhds hp)).comp p.1
      (contDiffAt_id.prodMk (contDiffAt_const (c := p.2)))
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero, id_eq] using
      h.of_le (show (a : ℕ∞ω) ≤ ∞ by simp)
  have hgr : ContDiffAt ℝ (a : ℕ∞ω)
      (fun r => iteratedDeriv b (fun θ => g (r, θ)) p.2) p.1 := by
    have h := ((contDiffOn_mixedDerivative hU hg 0 b).contDiffAt (hU.mem_nhds hp)).comp p.1
      (contDiffAt_id.prodMk (contDiffAt_const (c := p.2)))
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero, id_eq] using
      h.of_le (show (a : ℕ∞ω) ≤ ∞ by simp)
  unfold mixedDerivative
  rw [heq.iteratedDeriv_eq a]
  exact iteratedDeriv_fun_sub hfr hgr

theorem mixedDerivative_angular_translation_abs_le
    (T : ℝ → ℝ) (a b : ℕ) (hb : 1 ≤ b) (p : PolarPoint) :
    |mixedDerivative a b (fun q : PolarPoint => q.2 - T q.1) p| ≤ 1 := by
  have hθ (r : ℝ) : iteratedDeriv b (fun θ => θ - T r) p.2 = if b = 1 then 1 else 0 := by
    have hsub := iteratedDeriv_fun_sub
      (contDiffAt_id : ContDiffAt ℝ (b : ℕ∞ω) (fun θ : ℝ => θ) p.2)
      (contDiffAt_const : ContDiffAt ℝ (b : ℕ∞ω) (fun _ : ℝ => T r) p.2)
    simp only [id_eq] at hsub
    rw [hsub]
    simp only [iteratedDeriv_fun_id, iteratedDeriv_const,
      if_neg (by omega : b ≠ 0), sub_zero]
  unfold mixedDerivative
  simp_rw [hθ]
  rw [iteratedDeriv_const]
  split_ifs <;> norm_num

end ContinuousFlexibility.Statements
