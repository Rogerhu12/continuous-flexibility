import ContinuousFlexibility.Analysis.CanonicalTwoEndpointCubicMixed
import ContinuousFlexibility.Analysis.BoundaryTaylorExtension
import ContinuousFlexibility.Analysis.LocalMixedProductBounds

/-!
# Cubic division of an actual field with a smooth representative

A global smooth representative is used only to define the removable
quotient. Its genuine germs on the closed cylinder retain all jets of
the actual field. The factorization and the fixed-loss mixed estimate
therefore refer to that actual field, including both boundary circles.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem contDiff_intervalRadialCubicQuotient
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) {l r : ℝ} (hlr : l < r)
    (hleft : ∀ θ k, k ≤ 2 → iteratedDeriv k (fun x : ℝ => F (x, θ)) l = 0)
    (hright : ∀ θ k, k ≤ 2 → iteratedDeriv k (fun x : ℝ => F (x, θ)) r = 0) :
    ContDiff ℝ ∞ (intervalRadialCubicQuotient F l r) := by
  let G := translateRadialField l F
  have hG : ContDiff ℝ ∞ G :=
    hF.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
  have hGl : ∀ θ k, k ≤ 2 → iteratedDeriv k (fun x : ℝ => G (x, θ)) 0 = 0 := by
    intro θ k hk
    calc
      iteratedDeriv k (fun x : ℝ => G (x, θ)) 0 =
          iteratedDeriv k (fun x : ℝ => F (x, θ)) (l + 0) :=
        congrFun (iteratedDeriv_comp_const_add k (fun x : ℝ => F (x, θ)) l) 0
      _ = 0 := by simpa only [add_zero] using hleft θ k hk
  have hGr : ∀ θ k, k ≤ 2 →
      iteratedDeriv k (fun x : ℝ => G (x, θ)) (r - l) = 0 := by
    intro θ k hk
    have hsum : l + (r - l) = r := by ring
    calc
      iteratedDeriv k (fun x : ℝ => G (x, θ)) (r - l) =
          iteratedDeriv k (fun x : ℝ => F (x, θ)) (l + (r - l)) :=
        congrFun (iteratedDeriv_comp_const_add k (fun x : ℝ => F (x, θ)) l) (r - l)
      _ = 0 := by simpa only [hsum] using hright θ k hk
  exact (contDiff_radialTwoEndpointCubicQuotient hG (sub_pos.mpr hlr) hGl hGr).comp
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)

/-- Both boundary factors are genuinely removable. The bound loses six
radial derivatives, no angular derivatives, and has constant one over 36. -/
theorem intervalRadialCubicQuotient_of_closed_germs
    {F f : PolarPoint → ℝ} {l r : ℝ}
    (hF : ContDiff ℝ ∞ F) (hlr : l < r)
    (he : ∀ p ∈ Icc l r ×ˢ (univ : Set ℝ), F =ᶠ[𝓝 p] f)
    (hleft : ∀ θ k, k ≤ 2 → radialBoundaryJet f l k θ = 0)
    (hright : ∀ θ k, k ≤ 2 → radialBoundaryJet f r k θ = 0) :
    ContDiff ℝ ∞ (intervalRadialCubicQuotient F l r) ∧
      (∀ p ∈ Icc l r ×ˢ (univ : Set ℝ),
        f p = ((p.1 - l) * (r - p.1)) ^ 3 * intervalRadialCubicQuotient F l r p) ∧
      ∀ a b : ℕ, ∀ M : ℝ, ∀ p ∈ Icc l r ×ˢ (univ : Set ℝ),
        (∀ x ∈ Icc l r, |mixedDerivative (a + 6) b f (x, p.2)| ≤ M) →
        |mixedDerivative a b (intervalRadialCubicQuotient F l r) p| ≤ M / 36 := by
  have hFjet (x : ℝ) (hx : x ∈ Icc l r)
      (hzero : ∀ θ k, k ≤ 2 → radialBoundaryJet f x k θ = 0) :
      ∀ θ k, k ≤ 2 → iteratedDeriv k (fun t : ℝ => F (t, θ)) x = 0 := by
    intro θ k hk
    have hg := (he (x, θ) ⟨hx, mem_univ _⟩).comp_tendsto
      ((continuous_id.prodMk continuous_const).tendsto x)
    exact (hg.iteratedDeriv k).eq_of_nhds.trans (hzero θ k hk)
  have hFl := hFjet l ⟨le_rfl, hlr.le⟩ hleft
  have hFr := hFjet r ⟨hlr.le, le_rfl⟩ hright
  refine ⟨contDiff_intervalRadialCubicQuotient hF hlr hFl hFr, ?_, ?_⟩
  · intro p hp
    by_cases hpl : p.1 = l
    · have hp' : p = (l, p.2) := Prod.ext hpl rfl
      have hz : f (l, p.2) = 0 := by
        simpa only [radialBoundaryJet, iteratedDeriv_zero] using hleft p.2 0 (by decide)
      rw [hp']
      simp only [hz, sub_self, zero_mul, zero_pow (by decide : 3 ≠ 0)]
    by_cases hpr : p.1 = r
    · have hp' : p = (r, p.2) := Prod.ext hpr rfl
      have hz : f (r, p.2) = 0 := by
        simpa only [radialBoundaryJet, iteratedDeriv_zero] using hright p.2 0 (by decide)
      rw [hp']
      simp only [hz, sub_self, mul_zero, zero_pow (by decide : 3 ≠ 0), zero_mul]
    have hpin : p.1 ∈ Ioo l r :=
      ⟨lt_of_le_of_ne hp.1.1 (Ne.symm hpl), lt_of_le_of_ne hp.1.2 hpr⟩
    have hden : ((p.1 - l) * (r - p.1)) ^ 3 ≠ 0 :=
      pow_ne_zero 3 (mul_pos (sub_pos.mpr hpin.1) (sub_pos.mpr hpin.2)).ne'
    have hfactor := (eq_div_iff hden).mp
      (intervalRadialCubicQuotient_eq_div F (p := p) hpin)
    calc
      f p = F p := (he p hp).eq_of_nhds.symm
      _ = intervalRadialCubicQuotient F l r p * ((p.1 - l) * (r - p.1)) ^ 3 := hfactor.symm
      _ = _ := mul_comm _ _
  · intro a b M p hp hbound
    apply abs_mixedDerivative_intervalRadialCubicQuotient_le hF hlr hFl hFr a b
      (p := p) ?_ hp.1
    intro x hx
    rw [mixedDerivative_eq_of_germ (he (x, p.2) ⟨hx, mem_univ _⟩) (a + 6) b]
    exact hbound x hx

end ContinuousFlexibility.Analysis
