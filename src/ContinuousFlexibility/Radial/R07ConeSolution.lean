import ContinuousFlexibility.Radial.R07RadialUniqueness
import ContinuousFlexibility.Radial.R07ConeGeometry

/-!
# The actual incoming solution on a cone head

On a germ `w(r)=scale*r`, the two conical modes are normalized powers of
the radius. A smooth global extension of the radius supplies a smooth
representative for finite-interval uniqueness; the actual profile is used
throughout the radial initial value problem.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

theorem r07_hasDerivAt_normalized_power {u : ℝ → ℝ} {r c ν : ℝ}
    (hr : 0 < r) (hu : u =ᶠ[𝓝 r] fun x => x ^ ν / c ^ ν) :
    HasDerivAt u (ν / r * u r) r := by
  have h := (hasDerivAt_rpow_const (p := ν) (Or.inl hr.ne')).div_const (c ^ ν)
  have he : ν * r ^ (ν - 1) / c ^ ν = ν / r * u r := by
    rw [hu.eq_of_nhds, rpow_sub hr ν 1, rpow_one]
    ring
  exact he ▸ h.congr_of_eventuallyEq hu

theorem r07_radialJacobi_cone_power {w u : ℝ → ℝ} {r c ν scale J : ℝ}
    (hr : 0 < r) (hν : ν ^ 2 = J)
    (hw : w =ᶠ[𝓝 r] fun x => scale * x)
    (hu : u =ᶠ[𝓝 r] fun x => x ^ ν / c ^ ν) :
    radialJacobi J w u r = 0 := by
  have hd := r07_hasDerivAt_normalized_power hr hu
  have hwd : deriv w r = scale := by
    rw [hw.deriv_eq]
    simpa only [id_eq, mul_one] using ((hasDerivAt_id r).const_mul scale).deriv
  have hflux : (fun x => w x * deriv u x) =ᶠ[𝓝 r] fun x => (scale * ν) * u x := by
    filter_upwards [hw, hu.eventuallyEq_nhds, Ioi_mem_nhds hr] with x hx hxg hx₀
    have hxpos : 0 < x := hx₀
    rw [hx, (r07_hasDerivAt_normalized_power hxpos hxg).deriv]
    field_simp [hxpos.ne'] <;> ring
  unfold radialJacobi
  rw [hflux.deriv_eq, (hd.const_mul (scale * ν)).deriv, hwd, ← hν]
  ring

theorem r07_deriv_eqOn_Icc {l h : ℝ} (hlh : l < h) {u v : ℝ → ℝ}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (he : EqOn u v (Icc l h))
    {x : ℝ} (hx : x ∈ Icc l h) : deriv u x = deriv v x := by
  have hd := derivWithin_congr he (he hx)
  rw [(hu x).derivWithin (uniqueDiffOn_Icc hlh x hx),
    (hv x).derivWithin (uniqueDiffOn_Icc hlh x hx)] at hd
  exact hd

/-- A conical initial condition gives the exact logarithmic slope at the
outer end of the cone, before the following short join is traversed. -/
theorem exists_r07_cone_incoming {D : Statements.ReferenceData}
    (hD : Statements.RadialProfileGeometry D) {right : Bool} {j : ℕ} (hj : 2 ≤ j)
    {c p e scale : ℝ} (hc : c ∈ Statements.radialCore D)
    (hp : p ∈ Statements.radialCore D) (he : e ∈ Statements.radialCore D)
    (horder : if right then c < p ∧ p < e else e < p ∧ p < c)
    (hs : 0 < scale)
    (hcone : ∀ r ∈ uIcc c p, D.w =ᶠ[𝓝 r] fun x => scale * x) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      u c = 1 ∧ deriv u c = (if right then (j : ℝ) else -(j : ℝ)) / c ∧
      0 < u p ∧
      (∀ r ∈ uIcc c e, radialJacobi ((j : ℝ) ^ 2) D.w u r = 0) ∧
      deriv u p = (if right then (j : ℝ) else -(j : ℝ)) / p * u p ∧
      ∀ r ∈ Statements.radialOpenSpan c p, 0 < deriv D.w r := by
  let ν : ℝ := if right then (j : ℝ) else -(j : ℝ)
  let l := min c e
  let h := max c e
  have hl : D.a < l := lt_min hc.1 he.1
  have hh : h < D.b := max_lt hc.2 he.2
  have hlh : l ≤ h := min_le_max
  have hcI : c ∈ Icc l h := ⟨min_le_left _ _, le_max_left _ _⟩
  have hc₀ : 0 < c := hD.1.trans hc.1
  have hp₀ : 0 < p := hD.1.trans hp.1
  have hcp : min c p < max c p := by
    apply min_lt_max.mpr
    cases right
    · exact ne_of_gt horder.2
    · exact ne_of_lt horder.1
  have hcap : uIcc c p ⊆ Icc l h := by
    cases right
    · rw [uIcc_of_ge horder.2.le]
      intro r hr
      exact ⟨(min_le_right c e).trans (horder.1.le.trans hr.1), hr.2.trans (le_max_left c e)⟩
    · rw [uIcc_of_le horder.1.le]
      intro r hr
      exact ⟨(min_le_left c e).trans hr.1, hr.2.trans (horder.2.le.trans (le_max_right c e))⟩
  obtain ⟨R, hR, hRp, hRg⟩ := exists_r07_smooth_radius_germ (hD.1.trans hl) hlh
  let v : ℝ → ℝ := fun r => R r ^ ν / c ^ ν
  have hv : ContDiff ℝ ∞ v := (hR.rpow_const_of_ne (fun r => (hRp r).ne')).div_const _
  have hvg (r : ℝ) (hr : r ∈ Icc l h) : v =ᶠ[𝓝 r] fun x => x ^ ν / c ^ ν :=
    (hRg r hr).fun_comp (fun z => z ^ ν / c ^ ν)
  have hv₀ : v c = 1 := by rw [(hvg c hcI).eq_of_nhds]; exact div_self (rpow_pos_of_pos hc₀ ν).ne'
  have hv₁ : deriv v c = ν / c := by
    rw [(r07_hasDerivAt_normalized_power hc₀ (hvg c hcI)).deriv, hv₀, mul_one]
  obtain ⟨u, hu, hu₀, hu₁, hueq⟩ := exists_radialSolution_on_Icc hD hl hlh hh hcI
    ((j : ℝ) ^ 2) 1 (ν / c)
  have hν : ν ^ 2 = (j : ℝ) ^ 2 := by cases right <;> simp only [ν, Bool.false_eq_true, ite_false, ite_true, neg_sq]
  have hveq : ∀ r ∈ uIcc c p, radialJacobi ((j : ℝ) ^ 2) D.w v r = 0 := by
    intro r hr
    exact r07_radialJacobi_cone_power (hD.1.trans (hl.trans_le (hcap hr).1)) hν
      (hcone r hr) (hvg r (hcap hr))
  have hEq : EqOn u v (uIcc c p) := radialHomogeneous_eqOn_Icc hD
    (lt_min hc.1 hp.1)
    hcp.le (max_lt hc.2 hp.2) ⟨min_le_left _ _, le_max_left _ _⟩ hu hv
    (fun r hr => hueq r (hcap hr)) hveq (hu₀.trans hv₀.symm) (hu₁.trans hv₁.symm)
  have hpCap : p ∈ uIcc c p := right_mem_uIcc
  have hup : 0 < u p := by
    rw [hEq hpCap]
    exact div_pos (rpow_pos_of_pos (hRp p) ν) (rpow_pos_of_pos hc₀ ν)
  have hd : deriv u p = ν / p * u p := by
    rw [r07_deriv_eqOn_Icc hcp (hu.differentiable (by simp)) (hv.differentiable (by simp)) hEq hpCap,
      (r07_hasDerivAt_normalized_power hp₀ (hvg p (hcap hpCap))).deriv, hEq hpCap]
  refine ⟨u, hu, hu₀, hu₁, hup, fun r hr => hueq r hr, hd, ?_⟩
  intro r hr
  have hr' : r ∈ uIcc c p := ⟨hr.1.le, hr.2.le⟩
  rw [(hcone r hr').deriv_eq]
  have hdlinear : deriv (fun x : ℝ => scale * x) r = scale := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id r).const_mul scale).deriv
  rw [hdlinear]
  exact hs

end ContinuousFlexibility.Radial
