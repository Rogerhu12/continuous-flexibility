module

public import ContinuousFlexibility.Radial.R07RadialODE
public import ContinuousFlexibility.Radial.DirichletRiccatiComparison

/-!
# The positive-cap equation in an oriented model coordinate

The profile identity `w (R x) = scale * R' x` cancels the first-order
term in the radial equation. The scale is allowed to be negative, so
the same lemma applies when the left cap is traversed in reverse.
The identity is only required on the closed cap; uniqueness of derivatives
within that interval justifies the calculation at both boundary points.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

/-- Exact linearity of the radial differential expression in its height. -/
theorem radialJacobi_const_mul (J c : ℝ) (w u : ℝ → ℝ) (r : ℝ) :
    radialJacobi J w (fun x => c * u x) r = c * radialJacobi J w u r := by
  have hflux : (fun x => w x * deriv (fun t => c * u t) x) =
      fun x => c * (w x * deriv u x) := by
    funext x
    rw [deriv_const_mul_field]
    ring
  unfold radialJacobi
  rw [hflux, deriv_const_mul_field]
  dsimp only
  ring

/-- Differentiating the profile identity on a nontrivial closed cap is
valid at the cut and at the join as well as in the interior. -/
theorem r07_cap_weight_derivative {R w : ℝ → ℝ} {scale L : ℝ}
    (hL : 0 < L) (hR : ContDiff ℝ ∞ R) (hw : ContDiff ℝ ∞ w)
    (hweight : ∀ x ∈ Icc 0 L, w (R x) = scale * deriv R x)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    deriv w (R x) * deriv R x = scale * deriv (deriv R) x := by
  have hR' : ContDiff ℝ ∞ (deriv R) := (contDiff_infty_iff_deriv.mp hR).2
  have hleft := (hw.differentiable (by simp) (R x)).hasDerivAt.comp x
    (hR.differentiable (by simp) x).hasDerivAt
  have hright := (hR'.differentiable (by simp) x).hasDerivAt.const_mul scale
  have he := derivWithin_congr hweight (hweight x hx)
  change derivWithin (w ∘ R) (Icc 0 L) x =
    derivWithin (fun y => scale * deriv R y) (Icc 0 L) x at he
  rw [hleft.differentiableAt.derivWithin (uniqueDiffOn_Icc hL x hx),
    hright.differentiableAt.derivWithin (uniqueDiffOn_Icc hL x hx),
    hleft.deriv, hright.deriv] at he
  exact he

/-- The actual physical solution pulls back to the scalar positive-cap
system. No inverse coordinate or abstract model solution is postulated. -/
theorem r07_cap_pullback_system {R w u : ℝ → ℝ} {J scale L : ℝ}
    (hL : 0 < L) (hscale : scale ≠ 0)
    (hR : ContDiff ℝ ∞ R) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc 0 L, w (R x) = scale * deriv R x)
    (hode : ∀ x ∈ Icc 0 L, radialJacobi J w u (R x) = 0) :
    (∀ x ∈ Icc 0 L,
      HasDerivAt (fun t => u (R t)) (deriv u (R x) * deriv R x) x) ∧
    (∀ x ∈ Icc 0 L,
      HasDerivAt (fun t => deriv u (R t) * deriv R t)
        ((J * deriv (deriv R) x / R x) * u (R x)) x) := by
  have hR' : ContDiff ℝ ∞ (deriv R) := (contDiff_infty_iff_deriv.mp hR).2
  have hu' : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  refine ⟨fun x _ => (hu.differentiable (by simp) (R x)).hasDerivAt.comp x
    (hR.differentiable (by simp) x).hasDerivAt, ?_⟩
  intro x hx
  have hder := ((hu'.differentiable (by simp) (R x)).hasDerivAt.comp x
    (hR.differentiable (by simp) x).hasDerivAt).mul
    (hR'.differentiable (by simp) x).hasDerivAt
  have hweight' := r07_cap_weight_derivative hL hR hw hweight hx
  have hflux : deriv (fun r => w r * deriv u r) (R x) =
      deriv w (R x) * deriv u (R x) + w (R x) * deriv (deriv u) (R x) :=
    ((hw.differentiable (by simp) (R x)).hasDerivAt.mul
      (hu'.differentiable (by simp) (R x)).hasDerivAt).deriv
  have heq := hode x hx
  unfold radialJacobi at heq
  rw [hflux] at heq
  have heq' : deriv w (R x) * deriv u (R x) + w (R x) * deriv (deriv u) (R x) =
      J * deriv w (R x) / R x * u (R x) := by linarith only [heq]
  apply hder.congr_deriv
  apply mul_left_cancel₀ hscale
  calc
    scale * ((deriv (deriv u) (R x) * deriv R x) * deriv R x +
        deriv u (R x) * deriv (deriv R) x) =
      deriv (deriv u) (R x) * (scale * deriv R x) * deriv R x +
        deriv u (R x) * (scale * deriv (deriv R) x) := by ring
    _ = deriv (deriv u) (R x) * w (R x) * deriv R x +
        deriv u (R x) * (deriv w (R x) * deriv R x) := by
          rw [← hweight x hx, ← hweight']
    _ = (deriv w (R x) * deriv u (R x) +
        w (R x) * deriv (deriv u) (R x)) * deriv R x := by ring
    _ = (J * deriv w (R x) / R x * u (R x)) * deriv R x := by rw [heq']
    _ = (J / R x * u (R x)) * (deriv w (R x) * deriv R x) := by ring
    _ = (J / R x * u (R x)) * (scale * deriv (deriv R) x) := by rw [hweight']
    _ = scale * ((J * deriv (deriv R) x / R x) * u (R x)) := by ring

end ContinuousFlexibility.Radial
