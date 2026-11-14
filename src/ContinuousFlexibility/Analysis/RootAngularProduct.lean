module

public import ContinuousFlexibility.Analysis.RootTravelDifferential
public import ContinuousFlexibility.Scalar.HeightDerivatives

/-!
# A smooth angular-product denominator for the root height

The product of the two characteristic angular derivatives is expressed
without fractional radial powers:
  Uθ Vθ = φθ² - x³ χθ².
Here φ and χ are the genuine smooth extensions. This expression is
smooth across the root, and its boundary value is the square of the
prescribed angular normalization derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootAngularProduct (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  angularPartial (extendedRootEven G) p ^ 2 -
    p.1 ^ 3 * angularPartial (extendedRootOddCoefficient G) p ^ 2

private theorem hasDerivAt_angleSlice
    {f : ℝ × ℝ → ℝ} {x θ : ℝ} (hf : DifferentiableAt ℝ f (x, θ)) :
    HasDerivAt (fun η : ℝ => f (x, η)) (angularPartial f (x, θ)) θ := by
  have hp : HasDerivAt (fun η : ℝ => (x, η)) (0, 1) θ :=
    (hasDerivAt_const θ x).prodMk (hasDerivAt_id θ)
  have hd := hf.hasFDerivAt.comp_hasDerivAt θ hp
  have he : f ∘ (fun η : ℝ => (x, η)) = (fun η : ℝ => f (x, η)) := by
    funext η
    exact Function.comp_apply
  rw [he] at hd
  exact hd

theorem contDiff_rootAngularProduct
    {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T) :
    ContDiff ℝ ∞ (rootAngularProduct G) := by
  have hφ : ContDiff ℝ ∞ (angularPartial (extendedRootEven G)) :=
    ((contDiff_extendedRootEven hG hT hφperiod).fderiv_right
      (m := ∞) (by simp)).clm_apply contDiff_const
  have hχ : ContDiff ℝ ∞ (angularPartial (extendedRootOddCoefficient G)) :=
    ((contDiff_extendedRootOddCoefficient hG hT hχperiod).fderiv_right
      (m := ∞) (by simp)).clm_apply contDiff_const
  exact (hφ.pow 2).sub ((contDiff_fst.pow 3).mul (hχ.pow 2))

theorem angularPartial_rootCharacteristicCoordinate_pair
    {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    angularPartial (rootCharacteristicCoordinate G 1) p =
        angularPartial (extendedRootEven G) p -
          p.1 ^ (3 / 2 : ℝ) * angularPartial (extendedRootOddCoefficient G) p ∧
      angularPartial (rootCharacteristicCoordinate G (-1)) p =
        angularPartial (extendedRootEven G) p +
          p.1 ^ (3 / 2 : ℝ) * angularPartial (extendedRootOddCoefficient G) p := by
  have hu := hasDerivAt_angleSlice (x := p.1) (θ := p.2)
    ((contDiffAt_rootCharacteristicCoordinate (σ := 1) (θ := p.2) hG hp).differentiableAt (by simp))
  have hv := hasDerivAt_angleSlice (x := p.1) (θ := p.2)
    ((contDiffAt_rootCharacteristicCoordinate (σ := -1) (θ := p.2) hG hp).differentiableAt (by simp))
  have hφ := hasDerivAt_angleSlice (x := p.1) (θ := p.2)
    ((contDiff_extendedRootEven hG hT hφperiod).differentiable (by simp) p)
  have hχ := hasDerivAt_angleSlice (x := p.1) (θ := p.2)
    ((contDiff_extendedRootOddCoefficient hG hT hχperiod).differentiable (by simp) p)
  have hm := hφ.fun_sub (hχ.const_mul (p.1 ^ (3 / 2 : ℝ)))
  have hp' := hφ.fun_add (hχ.const_mul (p.1 ^ (3 / 2 : ℝ)))
  have hem : (fun η : ℝ => extendedRootEven G (p.1, η) -
      p.1 ^ (3 / 2 : ℝ) * extendedRootOddCoefficient G (p.1, η)) =
      (fun η : ℝ => rootCharacteristicCoordinate G 1 (p.1, η)) := by
    funext η
    exact (rootCharacteristicCoordinate_eq_extended_even_odd G (p := (p.1, η)) hp).1.symm
  have hep : (fun η : ℝ => extendedRootEven G (p.1, η) +
      p.1 ^ (3 / 2 : ℝ) * extendedRootOddCoefficient G (p.1, η)) =
      (fun η : ℝ => rootCharacteristicCoordinate G (-1) (p.1, η)) := by
    funext η
    exact (rootCharacteristicCoordinate_eq_extended_even_odd G (p := (p.1, η)) hp).2.symm
  rw [hem] at hm
  rw [hep] at hp'
  exact ⟨hu.unique hm, hv.unique hp'⟩

theorem rootAngularProduct_eq_characteristicProduct
    {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    rootAngularProduct G p =
      angularPartial (rootCharacteristicCoordinate G 1) p *
        angularPartial (rootCharacteristicCoordinate G (-1)) p := by
  obtain ⟨hu, hv⟩ := angularPartial_rootCharacteristicCoordinate_pair
    hG hT hχperiod hφperiod hp
  have hpow : (p.1 ^ (3 / 2 : ℝ)) ^ 2 = p.1 ^ 3 := by
    rw [rpow_three_halves_eq_mul_sqrt hp.le, mul_pow, Real.sq_sqrt hp.le]
    ring
  rw [hu, hv]
  unfold rootAngularProduct
  rw [← hpow]
  ring

theorem angularPartial_extendedRootEven_zero
    {G : ℝ × ℝ × ℝ → ℝ} {hL : ℝ → ℝ} {T θ a : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hφperiod : ∀ r, 0 ≤ r → ∀ η, rootEven G (r, η + T) = rootEven G (r, η) + T)
    (hzero : ∀ η : ℝ, G (0, 0, η) = hL η)
    (hLderiv : HasDerivAt hL a θ) :
    angularPartial (extendedRootEven G) (0, θ) = a := by
  have hd := hasDerivAt_angleSlice (x := (0 : ℝ)) (θ := θ)
    ((contDiff_extendedRootEven hG hT hφperiod).differentiable (by simp) (0, θ))
  have he : (fun η : ℝ => extendedRootEven G (0, η)) = hL := by
    funext η
    rw [extendedRootEven_of_nonneg G (le_refl (0 : ℝ)), rootEven_zero, hzero]
  rw [he] at hd
  exact hd.unique hLderiv

theorem rootAngularProduct_zero
    {G : ℝ × ℝ × ℝ → ℝ} {hL : ℝ → ℝ} {T θ a : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hφperiod : ∀ r, 0 ≤ r → ∀ η, rootEven G (r, η + T) = rootEven G (r, η) + T)
    (hzero : ∀ η : ℝ, G (0, 0, η) = hL η)
    (hLderiv : HasDerivAt hL a θ) :
    rootAngularProduct G (0, θ) = a ^ 2 := by
  simp only [rootAngularProduct,
    angularPartial_extendedRootEven_zero hG hT hφperiod hzero hLderiv,
    zero_pow (by decide : 3 ≠ 0), zero_mul, sub_zero]

end ContinuousFlexibility.Analysis
