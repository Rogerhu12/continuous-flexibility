import ContinuousFlexibility.Scalar.HeightDerivatives
import ContinuousFlexibility.Geometry.PlanarOrientation

/-!
# Actual inverse jets forced by weighted cut transmission

The value identity on the constant test fixes the two weights. Centered
affine tests have zero value at the shared physical point, so the derivative
identity then determines the radial columns of the true inverse derivatives.
Equality along the boundary curve fixes the angular columns. These facts
are statements about actual derivatives, with no coefficient regularity or
normal-form estimates as hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A centered affine test removes the derivative of its scalar weight. -/
theorem radialPartial_weighted_centered_linear
    {G : PolarPoint → PolarPoint} {k : PolarPoint → ℝ} {q : PolarPoint}
    (hG : DifferentiableAt ℝ G q) (hk : DifferentiableAt ℝ k q)
    (ℓ : PolarPoint →L[ℝ] ℝ) :
    radialPartial (fun y => k y * (ℓ (G y) - ℓ (G q))) q =
      k q * ℓ (fderiv ℝ G q (1, 0)) := by
  have hd : HasFDerivAt (fun y => ℓ (G y) - ℓ (G q))
      (ℓ.comp (fderiv ℝ G q)) q :=
    (ℓ.hasFDerivAt.comp q hG.hasFDerivAt).sub_const _
  rw [radialPartial_mul hk hd.differentiableAt]
  simp only [sub_self, mul_zero, zero_add, radialPartial, hd.fderiv,
    ContinuousLinearMap.comp_apply]

/-- The full weighted transmission law on genuine global smooth tests
forces equality of weights and opposite actual radial inverse columns. -/
theorem inverse_radialJet_of_weighted_cutLaw
    {G₀ G₁ : PolarPoint → PolarPoint} {k₀ k₁ : PolarPoint → ℝ}
    {q : PolarPoint} {c : ℝ}
    (hG₀ : DifferentiableAt ℝ G₀ q) (hG₁ : DifferentiableAt ℝ G₁ q)
    (hk₀ : DifferentiableAt ℝ k₀ q) (hk₁ : DifferentiableAt ℝ k₁ q)
    (hpoint : G₁ q = G₀ q) (hkzero : k₀ q ≠ 0)
    (hcut : ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
      k₁ q * u (G₁ q) = k₀ q * u (G₀ q) ∧
      radialPartial (fun y => k₁ y * u (G₁ y)) q =
        -radialPartial (fun y => k₀ y * u (G₀ y)) q -
          (k₀ q * u (G₀ q)) / c) :
    k₁ q = k₀ q ∧ fderiv ℝ G₁ q (1, 0) = -fderiv ℝ G₀ q (1, 0) := by
  have hk : k₁ q = k₀ q := by
    simpa only [mul_one] using
      (hcut (fun _ : PolarPoint => (1 : ℝ)) contDiff_const).1
  have hlinear (ℓ : PolarPoint →L[ℝ] ℝ) :
      ℓ (fderiv ℝ G₁ q (1, 0)) = -ℓ (fderiv ℝ G₀ q (1, 0)) := by
    let u : PolarPoint → ℝ := fun y => ℓ y - ℓ (G₀ q)
    have hu : ContDiff ℝ ∞ u := ℓ.contDiff.sub contDiff_const
    have hzero : u (G₀ q) = 0 := sub_self _
    have hr₀ : radialPartial (fun y => k₀ y * u (G₀ y)) q =
        k₀ q * ℓ (fderiv ℝ G₀ q (1, 0)) :=
      radialPartial_weighted_centered_linear hG₀ hk₀ ℓ
    have hr₁ : radialPartial (fun y => k₁ y * u (G₁ y)) q =
        k₁ q * ℓ (fderiv ℝ G₁ q (1, 0)) := by
      dsimp only [u]
      rw [← hpoint]
      exact radialPartial_weighted_centered_linear hG₁ hk₁ ℓ
    have he := (hcut u hu).2
    rw [hr₁, hr₀, hzero, mul_zero, zero_div, sub_zero, hk] at he
    apply mul_left_cancel₀ hkzero
    simpa only [mul_neg] using he
  refine ⟨hk, Prod.ext ?_ ?_⟩
  · simpa only [ContinuousLinearMap.coe_fst', Prod.fst_neg] using
      hlinear (ContinuousLinearMap.fst ℝ ℝ ℝ)
  · simpa only [ContinuousLinearMap.coe_snd', Prod.snd_neg] using
      hlinear (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- A genuine common boundary curve gives equality of angular inverse
columns, by uniqueness of its actual one-dimensional derivative. -/
theorem inverse_angularJet_of_boundary_eq
    {G₀ G₁ : PolarPoint → PolarPoint} {ρ θ : ℝ}
    (hG₀ : DifferentiableAt ℝ G₀ (ρ, θ))
    (hG₁ : DifferentiableAt ℝ G₁ (ρ, θ))
    (hboundary : ∀ η : ℝ, G₁ (ρ, η) = G₀ (ρ, η)) :
    fderiv ℝ G₁ (ρ, θ) (0, 1) = fderiv ℝ G₀ (ρ, θ) (0, 1) := by
  have hline : HasDerivAt (fun η : ℝ => (ρ, η)) ((0, 1) : PolarPoint) θ :=
    (hasDerivAt_const θ ρ).prodMk (hasDerivAt_id' θ)
  have hleft := hG₀.hasFDerivAt.comp_hasDerivAt θ hline
  have hright := hG₁.hasFDerivAt.comp_hasDerivAt θ hline
  have he : G₁ ∘ (fun η : ℝ => (ρ, η)) = G₀ ∘ (fun η : ℝ => (ρ, η)) :=
    funext hboundary
  rw [he] at hright
  exact hright.unique hleft

/-- The reflected inverse columns determine the forward inverse maps.
This is finite-dimensional linear algebra applied later to actual jets. -/
theorem planeInverse_reflected_columns
    {F₀ F₁ G₀ G₁ : PolarPoint →L[ℝ] PolarPoint}
    (hleft : G₀.comp F₀ = ContinuousLinearMap.id ℝ PolarPoint)
    (hright : F₁.comp G₁ = ContinuousLinearMap.id ℝ PolarPoint)
    (hradial : G₁ (1, 0) = -G₀ (1, 0))
    (hangular : G₁ (0, 1) = G₀ (0, 1)) (v : PolarPoint) :
    F₁ v = (-(F₀ v).1, (F₀ v).2) := by
  have hcolumns (w : PolarPoint) : G₁ w = G₀ (-w.1, w.2) := by
    rw [planeCLM_apply_decompose G₁ w,
      planeCLM_apply_decompose G₀ (-w.1, w.2), hradial, hangular]
    ext <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring
  have hleftv : G₀ (F₀ v) = v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun M : PolarPoint →L[ℝ] PolarPoint => M v) hleft
  have hpre : G₁ (-(F₀ v).1, (F₀ v).2) = v := by
    rw [hcolumns]
    simpa only [neg_neg, Prod.mk.eta] using hleftv
  calc
    F₁ v = F₁ (G₁ (-(F₀ v).1, (F₀ v).2)) := congrArg F₁ hpre.symm
    _ = (-(F₀ v).1, (F₀ v).2) := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun M : PolarPoint →L[ℝ] PolarPoint =>
          M (-(F₀ v).1, (F₀ v).2)) hright

end ContinuousFlexibility.Analysis
