module

public import ContinuousFlexibility.Radial.Gauge
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The outer Green kernel of the radial Jacobi operator

Section 6 of the manuscript (`06-global-reference-inverse.tex`, equations
`eq:rad-eq-tm1`, `eq:outer-robin-new`, `eq:rad-eq-tm2`) inverts the radial Jacobi
operator `L_j u = (w u')' - j² w' u / r` on the outer region by the kernel
`K_o(r,t) = λ⁻¹ U(min(r,t)) V(max(r,t))`, built from two homogeneous solutions
with the exact normalization `w (U V' - U' V) = -λ`.

This file works in the plain (increasing) radius `r` on an open interval
`Ioo α β` and proves:

* `radialWronskian_const`: the weighted Wronskian `w (U V' - U' V)` of two
  homogeneous solutions is constant on the interval;
* `radialJacobi_outerSolution`: variation of parameters, i.e. the function
  `outerSolution` solves `L_j u = f` for every continuous source `f`;
* `outerSolution_base_robin`: with `cA = 0` the state of `outerSolution` at the
  base point is proportional to the state of `U`, so it inherits the
  complementary Robin condition of `U` (the boundary identity behind
  `eq:rad-eq-tm2`).

Remark (kernel form).  With `cA = 0` and `cB = ∫ t in c..b₀, V t * f t`, for a
source supported in `(c, b₀)` and `c ≤ r ≤ b₀` one has
`outerSolution r = -λ⁻¹ (V r ∫_c^r U f + U r ∫_r^{b₀} V f) = -∫ K_o(r,t) f(t) dt`,
which is the original-source inverse `G_o f` of `eq:outer-robin-new`.  The kernel
integral itself is not formalized here.  Nothing in this file asserts the
existence of the homogeneous solutions `U`, `V`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology

/-- The weighted Wronskian `w (U V' - U' V)`. -/
def radialWronskian (w U V : ℝ → ℝ) (r : ℝ) : ℝ :=
  w r * (U r * deriv V r - deriv U r * V r)

/-- For a homogeneous solution the flux `w u'` has derivative `J w' u / r`. -/
theorem hasDerivAt_flux_of_radialJacobi_eq_zero {J r : ℝ} {w u : ℝ → ℝ}
    (hw : DifferentiableAt ℝ w r) (hu : DifferentiableAt ℝ (deriv u) r)
    (h : radialJacobi J w u r = 0) :
    HasDerivAt (fun t => w t * deriv u t) (J * deriv w r / r * u r) r := by
  have hd : DifferentiableAt ℝ (fun t => w t * deriv u t) r := hw.mul hu
  have heq : deriv (fun t => w t * deriv u t) r = J * deriv w r / r * u r := by
    unfold radialJacobi at h
    linarith
  exact heq ▸ hd.hasDerivAt

/-- The weighted Wronskian of two homogeneous solutions has derivative zero. -/
theorem hasDerivAt_radialWronskian {α β J : ℝ} {w U V : ℝ → ℝ}
    (hreg : ∀ r ∈ Ioo α β, DifferentiableAt ℝ w r ∧ DifferentiableAt ℝ U r ∧
      DifferentiableAt ℝ (deriv U) r ∧ DifferentiableAt ℝ V r ∧
      DifferentiableAt ℝ (deriv V) r)
    (hU : ∀ r ∈ Ioo α β, radialJacobi J w U r = 0)
    (hV : ∀ r ∈ Ioo α β, radialJacobi J w V r = 0) :
    ∀ r ∈ Ioo α β, HasDerivAt (radialWronskian w U V) 0 r := by
  intro r hr
  obtain ⟨hw, hU1, hU2, hV1, hV2⟩ := hreg r hr
  have hp := hasDerivAt_flux_of_radialJacobi_eq_zero hw hU2 (hU r hr)
  have hq := hasDerivAt_flux_of_radialJacobi_eq_zero hw hV2 (hV r hr)
  have h := (hU1.hasDerivAt.mul hq).sub (hV1.hasDerivAt.mul hp)
  have heq : radialWronskian w U V =
      fun t => U t * (w t * deriv V t) - V t * (w t * deriv U t) := by
    funext t
    unfold radialWronskian
    ring
  rw [heq]
  exact h.congr_deriv (by ring)

/-- The weighted Wronskian of two homogeneous solutions is constant on the interval. -/
theorem radialWronskian_const {α β J : ℝ} {w U V : ℝ → ℝ}
    (hreg : ∀ r ∈ Ioo α β, DifferentiableAt ℝ w r ∧ DifferentiableAt ℝ U r ∧
      DifferentiableAt ℝ (deriv U) r ∧ DifferentiableAt ℝ V r ∧
      DifferentiableAt ℝ (deriv V) r)
    (hU : ∀ r ∈ Ioo α β, radialJacobi J w U r = 0)
    (hV : ∀ r ∈ Ioo α β, radialJacobi J w V r = 0) :
    ∀ r ∈ Ioo α β, ∀ s ∈ Ioo α β,
      radialWronskian w U V r = radialWronskian w U V s := by
  intro r hr s hs
  have hd := hasDerivAt_radialWronskian hreg hU hV
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) hr hs

/-- Variation of parameters for the radial Jacobi operator, based at `c`:
`u = -λ⁻¹ (V (cA + ∫_c^r U f) + U (cB - ∫_c^r V f))`. -/
def outerSolution (lam cA cB c : ℝ) (U V f : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(1 / lam) * (V r * (cA + ∫ t in c..r, U t * f t) +
    U r * (cB - ∫ t in c..r, V t * f t))

/-- Fundamental theorem of calculus on the open interval. -/
theorem hasDerivAt_integral_Ioo {α β c r : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ioo α β)) (hc : c ∈ Ioo α β) (hr : r ∈ Ioo α β) :
    HasDerivAt (fun s => ∫ t in c..s, g t) (g r) r :=
  intervalIntegral.integral_hasDerivAt_right
    (ContinuousOn.intervalIntegrable (hg.mono (ordConnected_Ioo.uIcc_subset hc hr)))
    (hg.stronglyMeasurableAtFilter isOpen_Ioo r hr)
    (hg.continuousAt (isOpen_Ioo.mem_nhds hr))

/-- The first derivative of `outerSolution`: the source terms cancel. -/
theorem hasDerivAt_outerSolution {α β lam cA cB c : ℝ} {U V f : ℝ → ℝ}
    (hUd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ U r)
    (hVd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ V r)
    (hf : ContinuousOn f (Ioo α β)) (hc : c ∈ Ioo α β) :
    ∀ r ∈ Ioo α β, HasDerivAt (outerSolution lam cA cB c U V f)
      (-(1 / lam) * (deriv V r * (cA + ∫ t in c..r, U t * f t) +
        deriv U r * (cB - ∫ t in c..r, V t * f t))) r := by
  intro r hr
  have hUc : ContinuousOn U (Ioo α β) :=
    fun x hx => (hUd x hx).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Ioo α β) :=
    fun x hx => (hVd x hx).continuousAt.continuousWithinAt
  have hUf : ContinuousOn (fun t => U t * f t) (Ioo α β) := hUc.mul hf
  have hVf : ContinuousOn (fun t => V t * f t) (Ioo α β) := hVc.mul hf
  have hA : HasDerivAt (fun s => cA + ∫ t in c..s, U t * f t) (0 + U r * f r) r :=
    (hasDerivAt_const r cA).add (hasDerivAt_integral_Ioo hUf hc hr)
  have hB : HasDerivAt (fun s => cB - ∫ t in c..s, V t * f t) (0 - V r * f r) r :=
    (hasDerivAt_const r cB).sub (hasDerivAt_integral_Ioo hVf hc hr)
  have h : HasDerivAt
      (fun s => -(1 / lam) * (V s * (cA + ∫ t in c..s, U t * f t) +
        U s * (cB - ∫ t in c..s, V t * f t)))
      (-(1 / lam) * ((deriv V r * (cA + ∫ t in c..r, U t * f t) + V r * (0 + U r * f r)) +
        (deriv U r * (cB - ∫ t in c..r, V t * f t) + U r * (0 - V r * f r)))) r :=
    (((hVd r hr).hasDerivAt.mul hA).add ((hUd r hr).hasDerivAt.mul hB)).const_mul
      (-(1 / lam))
  exact h.congr_deriv (by ring)

/-- Variation of parameters: `outerSolution` solves `L_j u = f` on the interval,
for every choice of the constants `cA`, `cB`. -/
theorem radialJacobi_outerSolution {α β J lam cA cB c : ℝ} {w U V f : ℝ → ℝ}
    (hreg : ∀ r ∈ Ioo α β, DifferentiableAt ℝ w r ∧ DifferentiableAt ℝ U r ∧
      DifferentiableAt ℝ (deriv U) r ∧ DifferentiableAt ℝ V r ∧
      DifferentiableAt ℝ (deriv V) r)
    (hU : ∀ r ∈ Ioo α β, radialJacobi J w U r = 0)
    (hV : ∀ r ∈ Ioo α β, radialJacobi J w V r = 0)
    (hW : ∀ r ∈ Ioo α β, radialWronskian w U V r = -lam) (hlam : lam ≠ 0)
    (hf : ContinuousOn f (Ioo α β)) (hc : c ∈ Ioo α β) :
    ∀ r ∈ Ioo α β, radialJacobi J w (outerSolution lam cA cB c U V f) r = f r := by
  intro r hr
  have hUd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ U x := fun x hx => (hreg x hx).2.1
  have hVd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ V x := fun x hx => (hreg x hx).2.2.2.1
  have hderiv := hasDerivAt_outerSolution (cA := cA) (cB := cB) (lam := lam) hUd hVd hf hc
  have hev : (fun t => w t * deriv (outerSolution lam cA cB c U V f) t) =ᶠ[𝓝 r]
      fun t => -(1 / lam) * ((w t * deriv V t) * (cA + ∫ s in c..t, U s * f s) +
        (w t * deriv U t) * (cB - ∫ s in c..t, V s * f s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    rw [(hderiv s hs).deriv]
    ring
  obtain ⟨hw, hU1, hU2, hV1, hV2⟩ := hreg r hr
  have hUc : ContinuousOn U (Ioo α β) :=
    fun x hx => (hUd x hx).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Ioo α β) :=
    fun x hx => (hVd x hx).continuousAt.continuousWithinAt
  have hp := hasDerivAt_flux_of_radialJacobi_eq_zero hw hU2 (hU r hr)
  have hq := hasDerivAt_flux_of_radialJacobi_eq_zero hw hV2 (hV r hr)
  have hUf : ContinuousOn (fun t => U t * f t) (Ioo α β) := hUc.mul hf
  have hVf : ContinuousOn (fun t => V t * f t) (Ioo α β) := hVc.mul hf
  have hA : HasDerivAt (fun s => cA + ∫ t in c..s, U t * f t) (0 + U r * f r) r :=
    (hasDerivAt_const r cA).add (hasDerivAt_integral_Ioo hUf hc hr)
  have hB : HasDerivAt (fun s => cB - ∫ t in c..s, V t * f t) (0 - V r * f r) r :=
    (hasDerivAt_const r cB).sub (hasDerivAt_integral_Ioo hVf hc hr)
  have hg : HasDerivAt
      (fun t => -(1 / lam) * ((w t * deriv V t) * (cA + ∫ s in c..t, U s * f s) +
        (w t * deriv U t) * (cB - ∫ s in c..t, V s * f s)))
      (-(1 / lam) * ((J * deriv w r / r * V r) * (cA + ∫ s in c..r, U s * f s) +
        (w r * deriv V r) * (0 + U r * f r) +
        ((J * deriv w r / r * U r) * (cB - ∫ s in c..r, V s * f s) +
          (w r * deriv U r) * (0 - V r * f r)))) r :=
    ((hq.mul hA).add (hp.mul hB)).const_mul (-(1 / lam))
  have hW' := hW r hr
  unfold radialWronskian at hW'
  have key : -(1 / lam) * (w r * (U r * deriv V r - deriv U r * V r) * f r) = f r := by
    rw [hW', show -(1 / lam) * (-lam * f r) = (1 / lam * lam) * f r by ring,
      one_div_mul_cancel hlam, one_mul]
  unfold radialJacobi
  rw [hev.deriv_eq, hg.deriv]
  unfold outerSolution
  linear_combination key

/-- With `cA = 0`, the value of `outerSolution` at the base point is a multiple of `U c`. -/
theorem outerSolution_base {lam cB c : ℝ} {U V f : ℝ → ℝ} :
    outerSolution lam 0 cB c U V f c = -(cB / lam) * U c := by
  simp only [outerSolution, intervalIntegral.integral_same]
  ring

/-- With `cA = 0`, the derivative of `outerSolution` at the base point is the same
multiple of `deriv U c`. -/
theorem deriv_outerSolution_base {α β lam cB c : ℝ} {U V f : ℝ → ℝ}
    (hUd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ U r)
    (hVd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ V r)
    (hf : ContinuousOn f (Ioo α β)) (hc : c ∈ Ioo α β) :
    deriv (outerSolution lam 0 cB c U V f) c = -(cB / lam) * deriv U c := by
  rw [(hasDerivAt_outerSolution (cA := 0) (cB := cB) (lam := lam) hUd hVd hf hc c hc).deriv]
  simp only [intervalIntegral.integral_same]
  ring

/-- The boundary identity at the base point: with `cA = 0`, `outerSolution` satisfies
every Robin condition `v₁ u + v₂ (w u' / λ) = 0` at `c` that `U` satisfies. -/
theorem outerSolution_base_robin {α β lam cB c v₁ v₂ : ℝ} {w U V f : ℝ → ℝ}
    (hUd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ U r)
    (hVd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ V r)
    (hf : ContinuousOn f (Ioo α β)) (hc : c ∈ Ioo α β)
    (hrobin : v₁ * U c + v₂ * (w c * deriv U c / lam) = 0) :
    v₁ * outerSolution lam 0 cB c U V f c +
      v₂ * (w c * deriv (outerSolution lam 0 cB c U V f) c / lam) = 0 := by
  rw [outerSolution_base, deriv_outerSolution_base hUd hVd hf hc]
  linear_combination (-(cB / lam)) * hrobin

end ContinuousFlexibility.Radial
