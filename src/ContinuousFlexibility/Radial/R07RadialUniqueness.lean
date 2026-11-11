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

theorem continuousOn_radialJacobi {w u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (J : ℝ)
    {S : Set ℝ} (hS : ∀ r ∈ S, r ≠ 0) :
    ContinuousOn (radialJacobi J w u) S := by
  have hw' := (contDiff_infty_iff_deriv.mp hw).2
  have hu' := (contDiff_infty_iff_deriv.mp hu).2
  have hf := (contDiff_infty_iff_deriv.mp (hw.mul hu')).2
  exact hf.continuous.continuousOn.sub
    (((continuous_const.mul hw'.continuous).continuousOn.div continuousOn_id hS).mul
      hu.continuous.continuousOn)

/-- Smooth radial equations extend to the two finite endpoints of their
open interval. No condition at a flat physical endpoint is used here. -/
theorem radialJacobi_zero_on_Icc {w u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) {J l h : ℝ}
    (hl : 0 < l) (hlh : l < h)
    (heq : ∀ r ∈ Ioo l h, radialJacobi J w u r = 0) :
    ∀ r ∈ Icc l h, radialJacobi J w u r = 0 := by
  apply Set.EqOn.of_subset_closure heq
    (continuousOn_radialJacobi hw hu J (fun r hr => (hl.trans_le hr.1).ne'))
    continuousOn_const Ioo_subset_Icc_self
  rw [closure_Ioo hlh.ne]

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

/-- Match a given solution on a genuine neighborhood of the initial point,
while extending it over a larger retained compact interval. -/
theorem exists_radialSolution_matching_germ {D : Statements.ReferenceData}
    (hD : Statements.RadialProfileGeometry D) {l h a b t₀ J : ℝ}
    (hl : D.a < l) (hh : h < D.b) (hla : l ≤ a) (hat : a < t₀)
    (htb : t₀ < b) (hbh : b ≤ h) {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hveq : ∀ r ∈ Icc a b, radialJacobi J D.w v r = 0) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ r ∈ Icc l h, radialJacobi J D.w u r = 0) ∧ u =ᶠ[𝓝 t₀] v := by
  have ht : t₀ ∈ Icc l h := ⟨hla.trans hat.le, htb.le.trans hbh⟩
  have hlh : l ≤ h := ht.1.trans ht.2
  obtain ⟨u, hu, h₀, h₁, hueq⟩ := exists_radialSolution_on_Icc hD hl hlh hh ht
    J (v t₀) (deriv v t₀)
  have he : EqOn u v (Icc a b) := radialHomogeneous_eqOn_Icc hD
    (hl.trans_le hla) (hat.le.trans htb.le) (hbh.trans_lt hh) ⟨hat.le, htb.le⟩ hu hv
    (fun r hr => hueq r ⟨hla.trans hr.1, hr.2.trans hbh⟩) hveq h₀ h₁
  refine ⟨u, hu, hueq, ?_⟩
  filter_upwards [Icc_mem_nhds hat htb] with r hr
  exact he hr

/-- A nontrivial natural solution has nonzero Cauchy data at its finite
entrance. This is a finite interval consequence of the radial IVP. -/
theorem radialNaturalTail_cauchyData_ne_zero {D : Statements.ReferenceData}
    (hD : Statements.RadialProfileGeometry D) {right : Bool} {j : ℕ} {e : ℝ}
    (he : e ∈ Statements.radialCore D) {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hN : Statements.RadialNaturalTail D right j e v) :
    (v e, deriv v e) ≠ (0, 0) := by
  intro hz
  have hv₀ : v e = 0 := congrArg Prod.fst hz
  have hv₁ : deriv v e = 0 := congrArg Prod.snd hz
  obtain ⟨r, hr, hvr⟩ := hN.2.2.2
  have hrCore : r ∈ Statements.radialCore D := by
    cases right
    · exact ⟨hr.1, hr.2.trans he.2⟩
    · exact ⟨he.1.trans hr.1, hr.2⟩
  have hne : e ≠ r := by
    cases right
    · exact (ne_of_gt hr.2)
    · exact ne_of_lt hr.1
  have hlh : min e r < max e r := min_lt_max.mpr hne
  have hcoreL : D.a < min e r := lt_min he.1 hrCore.1
  have hcoreH : max e r < D.b := max_lt he.2 hrCore.2
  have heq : ∀ x ∈ Icc (min e r) (max e r), radialJacobi ((j : ℝ) ^ 2) D.w v x = 0 := by
    apply radialJacobi_zero_on_Icc hD.2.2.1.1 hv (hD.1.trans hcoreL) hlh
    intro x hx
    apply hN.2.1.2 x
    cases right
    · rw [min_eq_right hr.2.le, max_eq_left hr.2.le] at hx
      exact ⟨hrCore.1.trans hx.1, hx.2⟩
    · rw [min_eq_left hr.1.le, max_eq_right hr.1.le] at hx
      exact ⟨hx.1, hx.2.trans hrCore.2⟩
  have hzero := radialHomogeneous_zero_on_Icc hD hcoreL hlh.le hcoreH
    (mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩) hv heq hv₀ hv₁
  exact hvr (hzero (mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩))

end ContinuousFlexibility.Radial
