import ContinuousFlexibility.Statements.Radial
import ContinuousFlexibility.Radial.Gauge
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# A normalized terminal cap lift and its actual residual

The lift is the cutoff of the actual stand-in solution, divided by the
square root of its boundary scale. Its residual is derived from the
radial Jacobi expression. The estimate assumes bounds for the solution,
its derivative, the coefficient and the cutoff jets, never a bound for
the residual itself. Support separation gives the actual scalar row.

This file does not construct the cap, prove its attenuation, or assemble
a global inverse. Those geometric and ODE inputs must concern the same
functions and scale used here.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff

def terminalCapLift (lam : ℝ) (χ u : ℝ → ℝ) (r : ℝ) : ℝ :=
  χ r * u r / sqrt lam

theorem terminalCapLift_eq (lam : ℝ) (χ u : ℝ → ℝ) :
    terminalCapLift lam χ u = fun r => (sqrt lam)⁻¹ * (χ r * u r) := by
  funext r
  dsimp only [terminalCapLift]
  ring

theorem terminalCapLift_smooth (lam : ℝ) {χ u : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (terminalCapLift lam χ u) := by
  rw [terminalCapLift_eq]
  exact contDiff_const.mul (hχ.mul hu)

theorem terminalCapLift_support (lam : ℝ) (χ u : ℝ → ℝ) :
    Function.support (terminalCapLift lam χ u) ⊆ Function.support χ := by
  intro r hr hzero
  exact hr (by simp only [terminalCapLift, hzero, zero_mul, zero_div])

theorem terminalCapLift_tsupport (lam : ℝ) (χ u : ℝ → ℝ) :
    tsupport (terminalCapLift lam χ u) ⊆ tsupport χ :=
  closure_mono (terminalCapLift_support lam χ u)

theorem terminalCapLift_value {lam r : ℝ} {χ u : ℝ → ℝ} (hχ : χ r = 1) :
    terminalCapLift lam χ u r = u r / sqrt lam := by
  simp only [terminalCapLift, hχ, one_mul]

theorem terminalCapLift_normalized_trace {lam r : ℝ} (hlam : 0 < lam)
    {χ u : ℝ → ℝ} (hχ : χ r = 1) (hu : u r = 1) :
    sqrt lam * terminalCapLift lam χ u r = 1 := by
  rw [terminalCapLift_value hχ, hu]
  field_simp [(sqrt_pos.mpr hlam).ne'] <;> ring

/-- A cutoff equal to one near the cut preserves the actual normal derivative. -/
theorem terminalCapLift_deriv_eq {lam r : ℝ} {χ u : ℝ → ℝ}
    (hχ : χ =ᶠ[𝓝 r] fun _ => (1 : ℝ)) :
    deriv (terminalCapLift lam χ u) r = deriv u r / sqrt lam := by
  have hnear : terminalCapLift lam χ u =ᶠ[𝓝 r] fun x => (sqrt lam)⁻¹ * u x := by
    filter_upwards [hχ] with x hx
    simp only [terminalCapLift, hx, one_mul]
    ring
  rw [hnear.deriv_eq, deriv_const_mul_field]
  ring

theorem terminalCapLift_normalized_flux {lam r : ℝ} (hlam : 0 < lam)
    {w χ u : ℝ → ℝ} (hχ : χ =ᶠ[𝓝 r] fun _ => (1 : ℝ)) :
    w r * deriv (terminalCapLift lam χ u) r / sqrt lam = w r * deriv u r / lam := by
  rw [terminalCapLift_deriv_eq hχ]
  calc
    _ = w r * deriv u r / (sqrt lam * sqrt lam) := by
      field_simp [(sqrt_pos.mpr hlam).ne'] <;> ring
    _ = _ := by rw [mul_self_sqrt hlam.le]

/-- Constant normalization commutes with the actual differential expression,
including at points where a derivative is defined by its total convention. -/
theorem terminalCap_radialJacobi_const_mul (a k : ℝ) (w u : ℝ → ℝ) (r : ℝ) :
    radialJacobi a w (fun x => k * u x) r = k * radialJacobi a w u r := by
  have hd : deriv (fun x => k * u x) = fun x => k * deriv u x := by
    funext x
    exact deriv_const_mul_field k
  have hf : (fun x => w x * (k * deriv u x)) = fun x => k * (w x * deriv u x) := by
    funext x
    ring
  unfold radialJacobi
  rw [hd, hf, deriv_const_mul_field]
  ring

/-- The full product rule in the original radial coordinate. -/
theorem terminalCap_radialJacobi_mul (a r : ℝ) {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    radialJacobi a w (fun x => χ x * u x) r =
      χ r * radialJacobi a w u r + 2 * w r * deriv χ r * deriv u r +
        (deriv w r * deriv χ r + w r * deriv (deriv χ) r) * u r := by
  have hwD := hw.differentiable (by simp)
  have hχD := hχ.differentiable (by simp)
  have huD := hu.differentiable (by simp)
  have hχ₂ := (contDiff_infty_iff_deriv.mp hχ).2.differentiable (by simp)
  have hu₂ := (contDiff_infty_iff_deriv.mp hu).2.differentiable (by simp)
  have hd : deriv (fun x => χ x * u x) =
      fun x => deriv χ x * u x + χ x * deriv u x := by
    funext x
    exact deriv_fun_mul (hχD x) (huD x)
  have hf : (fun x => w x * deriv (fun y => χ y * u y) x) =
      fun x => w x * deriv χ x * u x + w x * χ x * deriv u x := by
    funext x
    rw [congrFun hd x]
    ring
  have hflux : deriv (fun x => w x * deriv χ x * u x + w x * χ x * deriv u x) r =
      ((deriv w r * deriv χ r + w r * deriv (deriv χ) r) * u r +
        w r * deriv χ r * deriv u r) +
      ((deriv w r * χ r + w r * deriv χ r) * deriv u r +
        w r * χ r * deriv (deriv u) r) :=
    ((((hwD r).hasDerivAt.mul (hχ₂ r).hasDerivAt).mul (huD r).hasDerivAt).add
      (((hwD r).hasDerivAt.mul (hχD r).hasDerivAt).mul (hu₂ r).hasDerivAt)).deriv
  have hbase : deriv (fun x => w x * deriv u x) r =
      deriv w r * deriv u r + w r * deriv (deriv u) r :=
    ((hwD r).hasDerivAt.mul (hu₂ r).hasDerivAt).deriv
  unfold radialJacobi
  rw [hf, hflux, hbase]
  ring

def terminalCapResidual (lam : ℝ) (w χ u : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(2 * w r * deriv χ r * deriv u r +
    (deriv w r * deriv χ r + w r * deriv (deriv χ) r) * u r) / sqrt lam

/-- This is the commutator in the paper, with the negative Jacobi sign. -/
theorem terminalCapResidual_eq (lam r : ℝ) {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) :
    terminalCapResidual lam w χ u r =
      (-2 * w r * deriv χ r * deriv u r -
        deriv (fun x => w x * deriv χ x) r * u r) / sqrt lam := by
  have hwd := hw.differentiable (by simp) r
  have hχd := (contDiff_infty_iff_deriv.mp hχ).2.differentiable (by simp) r
  rw [deriv_fun_mul hwd hχd]
  dsimp only [terminalCapResidual]
  ring

theorem terminalCapLift_jacobi (a lam r : ℝ) {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    radialJacobi a w (terminalCapLift lam χ u) r =
      χ r * radialJacobi a w u r / sqrt lam - terminalCapResidual lam w χ u r := by
  rw [terminalCapLift_eq, terminalCap_radialJacobi_const_mul,
    terminalCap_radialJacobi_mul a r hw hχ hu]
  dsimp only [terminalCapResidual]
  ring

theorem terminalCapLift_homogeneous_residual {a lam r : ℝ} {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (heq : radialJacobi a w u r = 0) :
    -radialJacobi a w (terminalCapLift lam χ u) r = terminalCapResidual lam w χ u r := by
  rw [terminalCapLift_jacobi a lam r hw hχ hu, heq, mul_zero, zero_div, zero_sub, neg_neg]

theorem terminalCapResidual_zero_of_not_mem {lam r : ℝ} {w χ u : ℝ → ℝ}
    (hr : r ∉ tsupport (deriv χ)) : terminalCapResidual lam w χ u r = 0 := by
  have h₁ : deriv χ r = 0 := image_eq_zero_of_notMem_tsupport hr
  have h₂ : deriv (deriv χ) r = 0 := deriv_of_notMem_tsupport hr
  simp only [terminalCapResidual, h₁, h₂, mul_zero, zero_mul, zero_add, add_zero,
    neg_zero, zero_div]

/-- The forcing lives only in the transition layer, even where the lift
itself is nonzero and the cutoff is constant one. -/
theorem terminalCapResidual_support (lam : ℝ) (w χ u : ℝ → ℝ) :
    Function.support (terminalCapResidual lam w χ u) ⊆ tsupport (deriv χ) := by
  intro r hr
  by_contra hout
  exact hr (terminalCapResidual_zero_of_not_mem hout)

/-- Raw coefficient and jet bounds imply the attenuated residual bound. -/
theorem terminalCapResidual_abs_le {lam r W W₁ C₁ C₂ A B σ : ℝ}
    {w χ u : ℝ → ℝ} (hlam : 0 < lam)
    (hw : |w r| ≤ W) (hw₁ : |deriv w r| ≤ W₁)
    (hχ₁ : |deriv χ r| ≤ C₁) (hχ₂ : |deriv (deriv χ) r| ≤ C₂)
    (hu : |u r| ≤ A * exp (-σ)) (hu₁ : |deriv u r| ≤ B * exp (-σ)) :
    |terminalCapResidual lam w χ u r| ≤
      ((2 * W * C₁ * B + (W₁ * C₁ + W * C₂) * A) / sqrt lam) * exp (-σ) := by
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  have hW₁ : 0 ≤ W₁ := (abs_nonneg _).trans hw₁
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans hχ₁
  have hC₂ : 0 ≤ C₂ := (abs_nonneg _).trans hχ₂
  have hb : |deriv w r * deriv χ r + w r * deriv (deriv χ) r| ≤ W₁ * C₁ + W * C₂ := by
    calc
      _ ≤ |deriv w r * deriv χ r| + |w r * deriv (deriv χ) r| := abs_add_le _ _
      _ = |deriv w r| * |deriv χ r| + |w r| * |deriv (deriv χ) r| := by
        rw [abs_mul, abs_mul]
      _ ≤ _ := add_le_add (mul_le_mul hw₁ hχ₁ (abs_nonneg _) hW₁)
        (mul_le_mul hw hχ₂ (abs_nonneg _) hW)
  have hfirst : |2 * w r * deriv χ r * deriv u r| ≤
      (2 * W * C₁) * (B * exp (-σ)) := by
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul _ hu₁ (abs_nonneg _) (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw (by norm_num)) hχ₁
      (abs_nonneg _) (by positivity)
  have hsecond : |(deriv w r * deriv χ r + w r * deriv (deriv χ) r) * u r| ≤
      (W₁ * C₁ + W * C₂) * (A * exp (-σ)) := by
    rw [abs_mul]
    exact mul_le_mul hb hu (abs_nonneg _) (by positivity)
  rw [terminalCapResidual, abs_div, abs_neg, abs_of_pos (sqrt_pos.mpr hlam)]
  calc
    _ ≤ ((2 * W * C₁) * (B * exp (-σ)) +
        (W₁ * C₁ + W * C₂) * (A * exp (-σ))) / sqrt lam :=
      div_le_div_of_nonneg_right
        ((abs_add_le _ _).trans (add_le_add hfirst hsecond)) (sqrt_nonneg _)
    _ = _ := by ring

/-- Conversion to the source convention of the radial weighted Hilbert
space: its density is 12 w / r². -/
def terminalCapHilbertSource (lam : ℝ) (w χ u : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ 2 / (12 * w r) * terminalCapResidual lam w χ u r

theorem terminalCapHilbertSource_density {lam r : ℝ} {w χ u : ℝ → ℝ}
    (hr : r ≠ 0) (hw : w r ≠ 0) :
    (12 * w r / r ^ 2) * terminalCapHilbertSource lam w χ u r =
      terminalCapResidual lam w χ u r := by
  dsimp only [terminalCapHilbertSource]
  field_simp [hr, hw] <;> ring

theorem terminalCapHilbertSource_support (lam : ℝ) (w χ u : ℝ → ℝ) :
    Function.support (terminalCapHilbertSource lam w χ u) ⊆ tsupport (deriv χ) := by
  intro r hr
  by_contra hout
  exact hr (by simp only [terminalCapHilbertSource,
    terminalCapResidual_zero_of_not_mem hout, mul_zero])

theorem terminalCapHilbertSource_abs_le {lam r R W W₁ C₁ C₂ A B σ : ℝ}
    {w χ u : ℝ → ℝ} (hlam : 0 < lam) (hρ : |r ^ 2 / (12 * w r)| ≤ R)
    (hw : |w r| ≤ W) (hw₁ : |deriv w r| ≤ W₁)
    (hχ₁ : |deriv χ r| ≤ C₁) (hχ₂ : |deriv (deriv χ) r| ≤ C₂)
    (hu : |u r| ≤ A * exp (-σ)) (hu₁ : |deriv u r| ≤ B * exp (-σ)) :
    |terminalCapHilbertSource lam w χ u r| ≤
      R * ((2 * W * C₁ * B + (W₁ * C₁ + W * C₂) * A) / sqrt lam) * exp (-σ) := by
  rw [terminalCapHilbertSource, abs_mul]
  calc
    _ ≤ R * (((2 * W * C₁ * B + (W₁ * C₁ + W * C₂) * A) / sqrt lam) * exp (-σ)) :=
      mul_le_mul hρ (terminalCapResidual_abs_le hlam hw hw₁ hχ₁ hχ₂ hu hu₁)
        (abs_nonneg _) ((abs_nonneg _).trans hρ)
    _ = _ := by ring

theorem terminalCapLift_weighted_equation {a lam r : ℝ} {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hr : r ≠ 0) (hw₀ : w r ≠ 0) (heq : radialJacobi a w u r = 0) :
    radialJacobi a w (terminalCapLift lam χ u) r =
      -(12 * w r / r ^ 2) * terminalCapHilbertSource lam w χ u r := by
  have h := terminalCapLift_homogeneous_residual hw hχ hu heq
  have hρ := terminalCapHilbertSource_density (lam := lam) (χ := χ) (u := u) hr hw₀
  linarith only [h, hρ]

/-- Separation from the actual true border gives its scalar row exactly,
without assuming any orthogonality or bounded-inverse identity. -/
theorem terminalCapLift_scalar_pairing_zero (D : Statements.ReferenceData)
    (lam : ℝ) (χ u : ℝ → ℝ)
    (hsep : Disjoint (Function.support (Statements.referenceColumn D)) (Function.support χ)) :
    (∫ r in D.a..D.b, Statements.referenceColumn D r * terminalCapLift lam χ u r) = 0 := by
  have hz : (fun r => Statements.referenceColumn D r * terminalCapLift lam χ u r) =
      fun _ => (0 : ℝ) := by
    funext r
    by_cases hc : Statements.referenceColumn D r = 0
    · rw [hc, zero_mul]
    · have hχ : χ r = 0 := by
        by_contra hne
        exact Set.disjoint_left.mp hsep hc hne
      simp only [terminalCapLift, hχ, zero_mul, zero_div, mul_zero]
  rw [hz, intervalIntegral.integral_zero]

/-- The two terminal lifts inherit the disjoint supports of their cutoffs. -/
theorem terminalCapLift_disjoint {lam μ : ℝ} {χ η u v : ℝ → ℝ}
    (hsep : Disjoint (Function.support χ) (Function.support η)) :
    Disjoint (Function.support (terminalCapLift lam χ u))
      (Function.support (terminalCapLift μ η v)) :=
  hsep.mono (terminalCapLift_support lam χ u) (terminalCapLift_support μ η v)

end ContinuousFlexibility.Radial
