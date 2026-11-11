import ContinuousFlexibility.Radial.MorseRadiusODE
import ContinuousFlexibility.Radial.MorseJoinActualGerms
import ContinuousFlexibility.Radial.Liouville
import ContinuousFlexibility.Statements.RadialTargets

/-!
# Smooth radial initial value problems on a retained interval

The natural solution supplied by the deep-tail theorem must be continued
back across a finite transition cell. The incoming cap solution also needs
an actual initial value problem, rather than a formal boundary state.

On a compact interval where the profile is positive, write it as `s²` with
`s` a globally smooth positive function. The substitution `u = ψ / s`
turns the radial equation into a scalar second-order equation with a
smooth potential. Only the germs near the retained interval are extended;
the original radial profile and its equation remain unchanged there.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

/-- A positive smooth density root on the whole line, agreeing with a
given positive profile on a neighborhood of the retained interval. -/
theorem exists_radialDensityRoot {a b l h : ℝ} {w : ℝ → ℝ}
    (hal : a < l) (hlh : l ≤ h) (hhb : h < b)
    (hw : ContDiff ℝ ∞ w) (hp : ∀ r ∈ Ioo a b, 0 < w r) :
    ∃ s : ℝ → ℝ, ContDiff ℝ ∞ s ∧ (∀ r, 0 < s r) ∧
      ∀ r ∈ Icc l h, w =ᶠ[𝓝 r] fun x => s x ^ 2 := by
  have hlog : ContDiffOn ℝ ∞ (fun r => log (w r)) (Ioo a b) :=
    hw.contDiffOn.log (fun r hr => (hp r hr).ne')
  obtain ⟨F, hF, _, hg⟩ := exists_contDiff_joinGerm_extension hal hlh hhb hlog
  let s : ℝ → ℝ := fun r => exp (F r / 2)
  refine ⟨s, (hF.div_const 2).exp, fun r => exp_pos _, ?_⟩
  intro r hr
  have hr' : r ∈ Ioo a b := ⟨hal.trans_le hr.1, hr.2.trans_lt hhb⟩
  filter_upwards [hg r hr, Ioo_mem_nhds hr'.1 hr'.2] with x hx hx'
  change w x = exp (F x / 2) ^ 2
  rw [hx, pow_two, ← exp_add, show log (w x) / 2 + log (w x) / 2 = log (w x) by ring,
    exp_log (hp x hx')]

/-- The scalar potential after division by the density root. -/
def radialDensityPotential (J : ℝ) (s : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv s) r / s r + 2 * J * deriv s r / (r * s r)

theorem contDiffOn_radialDensityPotential {s : ℝ → ℝ} (hs : ContDiff ℝ ∞ s)
    (hsp : ∀ r, 0 < s r) (J : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (radialDensityPotential J s) (Ioo a b) := by
  have hs' : ContDiff ℝ ∞ (deriv s) := (contDiff_infty_iff_deriv.mp hs).2
  have hs'' : ContDiff ℝ ∞ (deriv (deriv s)) := (contDiff_infty_iff_deriv.mp hs').2
  exact (hs''.contDiffOn.div hs.contDiffOn (fun r _ => (hsp r).ne')).add
    ((contDiffOn_const.mul hs'.contDiffOn).div
      (contDiffOn_id.mul hs.contDiffOn)
      (fun r hr => mul_ne_zero (ha.trans hr.1).ne' (hsp r).ne'))

/-- Liouville's identity with the physical radius as its own coordinate. -/
theorem radialJacobi_densityRoot {s ψ w : ℝ → ℝ} {r J : ℝ}
    (hs : ContDiff ℝ ∞ s) (hψ : ContDiff ℝ ∞ ψ) (hw : ContDiff ℝ ∞ w)
    (hsp : ∀ x, 0 < s x) (hr : 0 < r)
    (hroot : w =ᶠ[𝓝 r] fun x => s x ^ 2) :
    radialJacobi J w (fun x => ψ x / s x) r =
      -(s r) * (-deriv (deriv ψ) r + radialDensityPotential J s r * ψ r) := by
  have hu : ContDiff ℝ ∞ (fun x => ψ x / s x) :=
    hψ.div hs (fun x => (hsp x).ne')
  have hs' := (contDiff_infty_iff_deriv.mp hs).2
  have hψ' := (contDiff_infty_iff_deriv.mp hψ).2
  have hu' := (contDiff_infty_iff_deriv.mp hu).2
  have hweight : (fun x : ℝ => w (id x)) =ᶠ[𝓝 r]
      fun x => (1 : ℝ) * s x ^ 2 * deriv (id : ℝ → ℝ) x := by
    simpa only [id_eq, deriv_id', one_mul, mul_one] using hroot
  have h := radialJacobi_liouville (a := J) (c := 1) (x := r)
    (R := id) (s := s) (ψ := ψ) (w := w) (u := fun x => ψ x / s x)
    (Eventually.of_forall (fun _ => differentiableAt_id))
    (Eventually.of_forall (hs.differentiable (by simp)))
    (Eventually.of_forall (hψ.differentiable (by simp)))
    (Eventually.of_forall (hu.differentiable (by simp)))
    (by simpa only [deriv_id'] using
      (differentiableAt_const (1 : ℝ) : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) r))
    (hs'.differentiable (by simp) r) (hψ'.differentiable (by simp) r)
    (hw.differentiable (by simp) r)
    ((hw.differentiable (by simp) r).mul (hu'.differentiable (by simp) r))
    hr.ne' (by simp) (hsp r).ne' hweight (Eventually.of_forall (fun _ => rfl))
  simp only [id_eq, deriv_id', deriv_const, one_mul, div_one, zero_add,
    liouvilleSchrodinger, liouvilleV0, liouvilleRho] at h
  convert h using 1 <;> unfold radialDensityPotential <;> ring

/-- Every initial value and slope at an interior radius extend across any
retained compact interval as a genuine smooth solution of the radial ODE. -/
theorem exists_radialSolution_on_Icc {D : Statements.ReferenceData}
    (hD : Statements.RadialProfileGeometry D) {l h t₀ : ℝ}
    (hl : D.a < l) (hlh : l ≤ h) (hh : h < D.b) (ht : t₀ ∈ Icc l h)
    (J u₀ v₀ : ℝ) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ u t₀ = u₀ ∧ deriv u t₀ = v₀ ∧
      ∀ r ∈ Icc l h, radialJacobi J D.w u r = 0 := by
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hp : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hD.2.2.2.2.1
  obtain ⟨s, hs, hsp, hroot⟩ := exists_radialDensityRoot hl hlh hh hw hp
  have hV := contDiffOn_radialDensityPotential (b := D.b) hs hsp J hD.1
  obtain ⟨q, hq, _, hqg⟩ := exists_contDiff_joinGerm_extension hl hlh hh hV.neg
  obtain ⟨ψ, hψ, hψ₀, hψ₁, hψeq⟩ := exists_smoothSecondOrderSolution hq ht
    (s t₀ * u₀) (deriv s t₀ * u₀ + s t₀ * v₀)
  let u : ℝ → ℝ := fun r => ψ r / s r
  have hu : ContDiff ℝ ∞ u := hψ.div hs (fun r => (hsp r).ne')
  have hval : u t₀ = u₀ := by
    change ψ t₀ / s t₀ = u₀
    rw [hψ₀]
    exact mul_div_cancel_left₀ _ (hsp t₀).ne'
  have hder : deriv u t₀ = v₀ := by
    rw [show deriv u t₀ =
      (deriv ψ t₀ * s t₀ - ψ t₀ * deriv s t₀) / s t₀ ^ 2 from
      ((hψ.differentiable (by simp) t₀).hasDerivAt.div
        (hs.differentiable (by simp) t₀).hasDerivAt (hsp t₀).ne').deriv,
      hψ₀, hψ₁]
    field_simp [(hsp t₀).ne']
    ring
  refine ⟨u, hu, hval, hder, ?_⟩
  intro r hr
  rw [radialJacobi_densityRoot hs hψ hw hsp (hD.1.trans (hl.trans_le hr.1)) (hroot r hr),
    hψeq r hr, (hqg r hr).eq_of_nhds]
  ring

end ContinuousFlexibility.Radial
