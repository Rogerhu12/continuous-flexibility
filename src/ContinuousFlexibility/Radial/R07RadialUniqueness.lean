import ContinuousFlexibility.Radial.R07RadialODE

/-!
# Uniqueness for the physical radial initial value problem

The density-root conjugacy used to construct radial solutions also proves
uniqueness on a retained interval. In particular a nonzero natural solution
cannot have both its value and its derivative vanish at a finite matching
radius. No endpoint uniqueness assertion is substituted for this finite
interval statement.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

theorem radialHomogeneous_eqOn_Icc {D : Statements.ReferenceData}
    (hD : Statements.RadialProfileGeometry D) {l h t₀ J : ℝ}
    (hl : D.a < l) (hlh : l ≤ h) (hh : h < D.b) (ht : t₀ ∈ Icc l h)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hueq : ∀ r ∈ Icc l h, radialJacobi J D.w u r = 0)
    (hveq : ∀ r ∈ Icc l h, radialJacobi J D.w v r = 0)
    (h₀ : u t₀ = v t₀) (h₁ : deriv u t₀ = deriv v t₀) :
    EqOn u v (Icc l h) := by
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hp : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hD.2.2.2.2.1
  obtain ⟨s, hs, hsp, hroot⟩ := exists_radialDensityRoot hl hlh hh hw hp
  have hV := contDiffOn_radialDensityPotential (b := D.b) hs hsp J hD.1
  obtain ⟨q, hq, _, hqg⟩ := exists_contDiff_joinGerm_extension hl hlh hh hV.neg
  let ψ (f : ℝ → ℝ) : ℝ → ℝ := fun r => s r * f r
  have hψ (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (ψ f) := hs.mul hf
  have hdψ (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (r : ℝ) :
      deriv (ψ f) r = deriv s r * f r + s r * deriv f r :=
    (((hs.differentiable (by simp) r).hasDerivAt).mul
      (hf.differentiable (by simp) r).hasDerivAt).deriv
  have hEq (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
      (heq : ∀ r ∈ Icc l h, radialJacobi J D.w f r = 0) :
      ∀ r ∈ Icc l h, deriv (deriv (ψ f)) r = -q r * ψ f r := by
    intro r hr
    have hquot : (fun x => ψ f x / s x) = f := by
      funext x
      exact mul_div_cancel_left₀ _ (hsp x).ne'
    have hid := radialJacobi_densityRoot hs (hψ f hf) hw hsp
      (hD.1.trans (hl.trans_le hr.1)) (hroot r hr) (J := J)
    rw [hquot, heq r hr] at hid
    have hz : -deriv (deriv (ψ f)) r + radialDensityPotential J s r * ψ f r = 0 :=
      (mul_eq_zero.mp hid.symm).resolve_left (neg_ne_zero.mpr (hsp r).ne')
    rw [(hqg r hr).eq_of_nhds]
    linarith only [hz]
  have he : EqOn (ψ u) (ψ v) (Icc l h) := smoothSecondOrder_eqOn hq.continuous ht
    (hψ u hu) (hψ v hv) (hEq u hu hueq) (hEq v hv hveq)
    (by dsimp only [ψ]; rw [h₀])
    (by rw [hdψ u hu, hdψ v hv, h₀, h₁])
  intro r hr
  exact (mul_left_cancel₀ (hsp r).ne') (he hr)

/-- Initial data zero force the zero solution throughout any compact
interval on which the radial equation holds. -/
theorem radialHomogeneous_zero_on_Icc {D : Statements.ReferenceData}
    (hD : Statements.RadialProfileGeometry D) {l h t₀ J : ℝ}
    (hl : D.a < l) (hlh : l ≤ h) (hh : h < D.b) (ht : t₀ ∈ Icc l h)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hueq : ∀ r ∈ Icc l h, radialJacobi J D.w u r = 0)
    (h₀ : u t₀ = 0) (h₁ : deriv u t₀ = 0) :
    EqOn u (fun _ => 0) (Icc l h) := by
  apply radialHomogeneous_eqOn_Icc hD hl hlh hh ht hu contDiff_const hueq
  · intro r _
    simp [radialJacobi]
  · exact h₀
  · simpa only [deriv_const] using h₁

end ContinuousFlexibility.Radial
