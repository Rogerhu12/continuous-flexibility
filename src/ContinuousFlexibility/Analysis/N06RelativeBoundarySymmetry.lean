import ContinuousFlexibility.Analysis.N06RelativeChartHeightPatch
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Symmetry inherited by the actual relative boundary correction

Equal fields on a nondegenerate closed interval have the same ordinary
boundary jets when both are smooth at the endpoint. This converts the
actual closed-strip period and reflection identities into identities of
the actual Taylor coefficients. The explicit relative patch preserves a
common affine angular transformation law, including a periodic angular
lift and even or odd reflection.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

theorem n06_iteratedDeriv_congr_closed_interval
    {l r c : ℝ} (hlr : l < r) (hc : c ∈ Icc l r)
    {f g : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f c) (hg : ContDiffAt ℝ ∞ g c)
    (hfg : EqOn f g (Icc l r)) (n : ℕ) :
    iteratedDeriv n f c = iteratedDeriv n g c := by
  calc
    iteratedDeriv n f c = iteratedDerivWithin n f (Icc l r) c :=
      (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlr)
        (hf.of_le (show (n : ℕ∞ω) ≤ ∞ by simp)) hc).symm
    _ = iteratedDerivWithin n g (Icc l r) c := iteratedDerivWithin_congr hfg hc
    _ = iteratedDeriv n g c :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlr)
        (hg.of_le (show (n : ℕ∞ω) ≤ ∞ by simp)) hc

/-- A genuine closed-strip scalar symmetry is inherited by every actual
radial boundary jet. No extension symmetry outside the strip is required. -/
theorem n06_radialBoundaryJet_transform
    {l r c : ℝ} (hlr : l < r) (hc : c ∈ Icc l r)
    {f : ℝ × ℝ → ℝ} (hf : ∀ θ, ContDiffAt ℝ ∞ f (c, θ))
    (τ : ℝ → ℝ) (κ : ℝ)
    (htransform : ∀ x ∈ Icc l r, ∀ θ, f (x, τ θ) = κ * f (x, θ))
    (n : ℕ) (θ : ℝ) :
    radialBoundaryJet f c n (τ θ) = κ * radialBoundaryJet f c n θ := by
  have hs (η : ℝ) : ContDiffAt ℝ ∞ (fun x => f (x, η)) c :=
    (hf η).comp (f := fun x : ℝ => (x, η)) c
      (contDiffAt_id.prodMk contDiffAt_const)
  have he := n06_iteratedDeriv_congr_closed_interval hlr hc (hs (τ θ))
    (contDiffAt_const.mul (hs θ)) (fun x hx => htransform x hx θ) n
  change iteratedDeriv n (fun x => f (x, τ θ)) c =
    κ * iteratedDeriv n (fun x => f (x, θ)) c
  exact he.trans (by simp only [iteratedDeriv_const_mul_field])

theorem n06_boundaryTaylorPolynomial_transform {n : ℕ} {a : ℕ → ℝ → ℝ}
    (τ : ℝ → ℝ) (κ : ℝ)
    (ha : ∀ j ≤ n, ∀ θ, a j (τ θ) = κ * a j θ)
    (c x θ : ℝ) :
    boundaryTaylorPolynomial n c a (x, τ θ) =
      κ * boundaryTaylorPolynomial n c a (x, θ) := by
  unfold boundaryTaylorPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ha j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) θ]
  ring

theorem n06SmallBoundaryExtension_transform {n : ℕ} {a b : ℕ → ℝ → ℝ}
    (τ : ℝ → ℝ) (κ : ℝ)
    (ha : ∀ j ≤ n, ∀ θ, a j (τ θ) = κ * a j θ)
    (hb : ∀ j ≤ n, ∀ θ, b j (τ θ) = κ * b j θ)
    (l r δ x θ : ℝ) :
    n06SmallBoundaryExtension n l r δ a b (x, τ θ) =
      κ * n06SmallBoundaryExtension n l r δ a b (x, θ) := by
  unfold n06SmallBoundaryExtension
  rw [n06_boundaryTaylorPolynomial_transform τ κ ha,
    n06_boundaryTaylorPolynomial_transform τ κ hb]
  ring

/-- A common affine angular law of the actual current and reference
fields is retained by the constructed relative patch. The inhomogeneous
term cancels before taking any radial boundary derivative. -/
theorem n06RelativeBoundaryPatch_transform {n : ℕ} {l r δ : ℝ}
    (hlr : l < r) {f₀ : ℝ × ℝ → ℝ} {f : Bool → ℝ × ℝ → ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ),
      ContDiffAt ℝ ∞ f₀ (if side then r else l, θ))
    (hf : ∀ (side : Bool) (θ : ℝ),
      ContDiffAt ℝ ∞ (f side) (if side then r else l, θ))
    (τ : ℝ → ℝ) (κ : ℝ) (b : ℝ → ℝ)
    (h₀transform : ∀ x ∈ Icc l r, ∀ θ, f₀ (x, τ θ) = κ * f₀ (x, θ) + b θ)
    (hftransform : ∀ side x, x ∈ Icc l r → ∀ θ,
      f side (x, τ θ) = κ * f side (x, θ) + b θ)
    {x : ℝ} (hx : x ∈ Icc l r) (θ : ℝ) :
    n06RelativeBoundaryPatch n l r δ f₀ f (x, τ θ) =
      κ * n06RelativeBoundaryPatch n l r δ f₀ f (x, θ) + b θ := by
  have hsub (side : Bool) (y : ℝ) (hy : y ∈ Icc l r) (η : ℝ) :
      f side (y, τ η) - f₀ (y, τ η) = κ * (f side (y, η) - f₀ (y, η)) := by
    rw [hftransform side y hy η, h₀transform y hy η]
    ring
  have ha (j : ℕ) (η : ℝ) :
      radialBoundaryJet (fun q => f false q - f₀ q) l j (τ η) =
        κ * radialBoundaryJet (fun q => f false q - f₀ q) l j η :=
    n06_radialBoundaryJet_transform hlr ⟨le_rfl, hlr.le⟩
      (fun η => (hf false η).sub (h₀ false η)) τ κ (hsub false) j η
  have hb (j : ℕ) (η : ℝ) :
      radialBoundaryJet (fun q => f true q - f₀ q) r j (τ η) =
        κ * radialBoundaryJet (fun q => f true q - f₀ q) r j η :=
    n06_radialBoundaryJet_transform hlr ⟨hlr.le, le_rfl⟩
      (fun η => (hf true η).sub (h₀ true η)) τ κ (hsub true) j η
  unfold n06RelativeBoundaryPatch
  rw [h₀transform x hx θ, n06SmallBoundaryExtension_transform τ κ
    (fun j _ η => ha j η) (fun j _ η => hb j η)]
  ring

/-- The two actual chart coordinates retain their common affine law. -/
theorem n06RelativeChartPatch_transform {l r δ : ℝ} (hlr : l < r)
    {F₀ : ℝ × ℝ → ℝ × ℝ} {F : Bool → ℝ × ℝ → ℝ × ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ),
      ContDiffAt ℝ ∞ F₀ (if side then r else l, θ))
    (hF : ∀ (side : Bool) (θ : ℝ),
      ContDiffAt ℝ ∞ (F side) (if side then r else l, θ))
    (τ : ℝ → ℝ) (κ : ℝ × ℝ) (b : ℝ → ℝ × ℝ)
    (h₀transform : ∀ x ∈ Icc l r, ∀ θ,
      F₀ (x, τ θ) = (κ.1 * (F₀ (x, θ)).1 + (b θ).1,
        κ.2 * (F₀ (x, θ)).2 + (b θ).2))
    (hFtransform : ∀ side x, x ∈ Icc l r → ∀ θ,
      F side (x, τ θ) = (κ.1 * (F side (x, θ)).1 + (b θ).1,
        κ.2 * (F side (x, θ)).2 + (b θ).2))
    {x : ℝ} (hx : x ∈ Icc l r) (θ : ℝ) :
    n06RelativeChartPatch l r δ F₀ F (x, τ θ) =
      (κ.1 * (n06RelativeChartPatch l r δ F₀ F (x, θ)).1 + (b θ).1,
        κ.2 * (n06RelativeChartPatch l r δ F₀ F (x, θ)).2 + (b θ).2) := by
  apply Prod.ext
  · exact n06RelativeBoundaryPatch_transform hlr
      (fun side θ => (h₀ side θ).fst) (fun side θ => (hF side θ).fst)
      τ κ.1 (fun θ => (b θ).1)
      (fun y hy η => congrArg Prod.fst (h₀transform y hy η))
      (fun side y hy η => congrArg Prod.fst (hFtransform side y hy η)) hx θ
  · exact n06RelativeBoundaryPatch_transform hlr
      (fun side θ => (h₀ side θ).snd) (fun side θ => (hF side θ).snd)
      τ κ.2 (fun θ => (b θ).2)
      (fun y hy η => congrArg Prod.snd (h₀transform y hy η))
      (fun side y hy η => congrArg Prod.snd (hFtransform side y hy η)) hx θ

/-- A common angular invariance of the positive reference and current
heights is retained after logarithmic patching and exponentiation. -/
theorem n06RelativeHeightPatch_transform {l r δ : ℝ} (hlr : l < r)
    {H₀ : ℝ × ℝ → ℝ} {H : Bool → ℝ × ℝ → ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ),
      ContDiffAt ℝ ∞ H₀ (if side then r else l, θ))
    (hH : ∀ (side : Bool) (θ : ℝ),
      ContDiffAt ℝ ∞ (H side) (if side then r else l, θ))
    (h₀pos : ∀ (side : Bool) (θ : ℝ), 0 < H₀ (if side then r else l, θ))
    (hHpos : ∀ (side : Bool) (θ : ℝ), 0 < H side (if side then r else l, θ))
    (τ : ℝ → ℝ)
    (h₀transform : ∀ x ∈ Icc l r, ∀ θ, H₀ (x, τ θ) = H₀ (x, θ))
    (hHtransform : ∀ side x, x ∈ Icc l r → ∀ θ, H side (x, τ θ) = H side (x, θ))
    {x : ℝ} (hx : x ∈ Icc l r) (θ : ℝ) :
    n06RelativeHeightPatch l r δ H₀ H (x, τ θ) =
      n06RelativeHeightPatch l r δ H₀ H (x, θ) := by
  have hlog := n06RelativeBoundaryPatch_transform (n := 3) (δ := δ) hlr
    (fun side θ => (h₀ side θ).log (h₀pos side θ).ne')
    (fun side θ => (hH side θ).log (hHpos side θ).ne') τ 1 (fun _ => 0)
    (fun y hy η => by simp only [h₀transform y hy η, one_mul, add_zero])
    (fun side y hy η => by simp only [hHtransform side y hy η, one_mul, add_zero]) hx θ
  simp only [one_mul, add_zero] at hlog
  exact congrArg Real.exp hlog

end ContinuousFlexibility.Analysis
