module

public import ContinuousFlexibility.Radial.GeneralLiouvilleTransport

/-!
# Liouville conjugacy on the actual radius range

The model height gives a radial height through the genuine inverse radius
coordinate. The flux and second derivative are computed on that range using
local smoothness at every radius in the image.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The radial height obtained by dividing by the positive density root and
composing with the inverse radius coordinate. -/
def generalLiouvilleRadialHeight (R s ψ : ℝ → ℝ) : ℝ → ℝ :=
  (fun x => ψ x / s x) ∘ generalLiouvilleCoordinate R

variable {R s ψ : ℝ → ℝ} {scale : ℝ}

theorem generalLiouvilleRadialHeight_apply (hd : ∀ x, 0 < deriv R x) (x : ℝ) :
    generalLiouvilleRadialHeight R s ψ (R x) = ψ x / s x := by
  simp only [generalLiouvilleRadialHeight, Function.comp_apply,
    generalLiouvilleCoordinate_apply hd]

theorem generalLiouvilleRadialHeight_contDiffAt
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s) (hψ : ContDiff ℝ ∞ ψ)
    (hd : ∀ x, 0 < deriv R x) (hspos : ∀ x, 0 < s x) (x : ℝ) :
    ContDiffAt ℝ ∞ (generalLiouvilleRadialHeight R s ψ) (R x) := by
  have hq : ContDiffAt ℝ ∞ (fun y => ψ y / s y) (generalLiouvilleCoordinate R (R x)) := by
    rw [generalLiouvilleCoordinate_apply hd]
    exact hψ.contDiffAt.div hs.contDiffAt (hspos x).ne'
  exact hq.comp (R x) (generalLiouvilleCoordinate_contDiffAt hR hd x)

theorem generalLiouvilleRadialHeight_contDiffOn
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s) (hψ : ContDiff ℝ ∞ ψ)
    (hd : ∀ x, 0 < deriv R x) (hspos : ∀ x, 0 < s x) :
    ContDiffOn ℝ ∞ (generalLiouvilleRadialHeight R s ψ) (range R) := by
  rintro _ ⟨x, rfl⟩
  exact (generalLiouvilleRadialHeight_contDiffAt hR hs hψ hd hspos x).contDiffWithinAt

/-- The actual radial Jacobi expression of the constructed height agrees
with the model Schrödinger expression at every radius in the image. -/
theorem generalLiouvilleRadialHeight_radialJacobi
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s) (hψ : ContDiff ℝ ∞ ψ)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) (j x : ℝ) :
    radialJacobi (j ^ 2) (generalLiouvilleProfile R s scale)
        (generalLiouvilleRadialHeight R s ψ) (R x) =
      -(scale * s x / deriv R x) * liouvilleSchrodinger (j ^ 2) R s ψ x := by
  have hd : ∀ y, 0 < deriv R y := fun y => (hp y).2.1
  have hu (y : ℝ) : ContDiffAt ℝ ∞ (generalLiouvilleRadialHeight R s ψ) (R y) :=
    generalLiouvilleRadialHeight_contDiffAt hR hs hψ hd (fun z => (hp z).2.2) y
  have hw := (generalLiouvilleProfile_contDiffAt (scale := scale) hR hs hd x).differentiableAt (by simp)
  have hdu : DifferentiableAt ℝ (deriv (generalLiouvilleRadialHeight R s ψ)) (R x) :=
    ((hu x).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  exact radialJacobi_liouville
    (Eventually.of_forall (hR.differentiable (by simp)))
    (Eventually.of_forall (hs.differentiable (by simp)))
    (Eventually.of_forall (hψ.differentiable (by simp)))
    (Eventually.of_forall (fun t => (hu t).differentiableAt (by simp)))
    ((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) x)
    ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp) x)
    ((contDiff_infty_iff_deriv.mp hψ).2.differentiable (by simp) x)
    hw (hw.mul hdu) (hp x).1.ne' (hd x).ne' (hp x).2.2.ne'
    (Eventually.of_forall (generalLiouvilleProfile_apply hd))
    (Eventually.of_forall (generalLiouvilleRadialHeight_apply hd))

theorem generalLiouvilleRadialHeight_forcing_iff
    (hscale : 0 < scale) (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hψ : ContDiff ℝ ∞ ψ) (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
    (f : ℝ → ℝ) (j x : ℝ) :
    radialJacobi (j ^ 2) (generalLiouvilleProfile R s scale)
        (generalLiouvilleRadialHeight R s ψ) (R x) = f (R x) ↔
      liouvilleSchrodinger (j ^ 2) R s ψ x = liouvilleSource scale R s f x :=
  liouville_forcing_iff hscale.ne' (hp x).2.2.ne' (hp x).2.1.ne'
    (generalLiouvilleRadialHeight_radialJacobi hR hs hψ hp j x)

end ContinuousFlexibility.Radial
