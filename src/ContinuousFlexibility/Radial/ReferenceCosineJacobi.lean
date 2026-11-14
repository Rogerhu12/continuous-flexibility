module

public import ContinuousFlexibility.Radial.ReferenceCosineTests
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Cosine projection commutes with the actual radial differential expression

Two ordinary integrations by parts move angular derivatives onto the
cosine basis. Radial derivatives commute with the compact angular
integral. Combining those identities gives the genuine modal Jacobi
equation and finite-projection commutation.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

private theorem reference_periodic_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {T : ℝ} (hp : Function.Periodic f T) : Function.Periodic (deriv f) T := by
  intro x
  have h := ((hf.differentiable (by simp) (x + T)).hasDerivAt).comp x
    ((hasDerivAt_id x).add_const T)
  have he : (f ∘ fun t : ℝ => t + T) = f := funext hp
  change HasDerivAt (f ∘ fun t : ℝ => t + T) (deriv f (x + T) * 1) x at h
  rw [he, mul_one] at h
  exact h.deriv.symm

theorem reference_integral_periodic_mul_second_deriv {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {T : ℝ}
    (hfp : Function.Periodic f T) (hgp : Function.Periodic g T) :
    (∫ θ in (0 : ℝ)..T, f θ * deriv (deriv g) θ) =
      ∫ θ in (0 : ℝ)..T, deriv (deriv f) θ * g θ := by
  have hf₁ := (contDiff_infty_iff_deriv.mp hf).2
  have hg₁ := (contDiff_infty_iff_deriv.mp hg).2
  have hf₂ := (contDiff_infty_iff_deriv.mp hf₁).2
  have hg₂ := (contDiff_infty_iff_deriv.mp hg₁).2
  have hfend : f T = f 0 := by simpa only [zero_add] using hfp 0
  have hgend : g T = g 0 := by simpa only [zero_add] using hgp 0
  have hf₁end : deriv f T = deriv f 0 := by
    simpa only [zero_add] using reference_periodic_deriv hf hfp 0
  have hg₁end : deriv g T = deriv g 0 := by
    simpa only [zero_add] using reference_periodic_deriv hg hgp 0
  have h₁ := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := T) (u := f) (v := deriv g)
    (u' := deriv f) (v' := deriv (deriv g))
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hg₁.differentiable (by simp) x).hasDerivAt)
    (hf₁.continuous.intervalIntegrable _ _) (hg₂.continuous.intervalIntegrable _ _)
  have h₂ := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := T) (u := deriv f) (v := g)
    (u' := deriv (deriv f)) (v' := deriv g)
    (fun x _ => (hf₁.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hg.differentiable (by simp) x).hasDerivAt)
    (hf₂.continuous.intervalIntegrable _ _) (hg₁.continuous.intervalIntegrable _ _)
  rw [hfend, hg₁end, sub_self, zero_sub] at h₁
  rw [hf₁end, hgend, sub_self, zero_sub] at h₂
  rw [h₁, h₂, neg_neg]

theorem referenceAngularBasis_periodic_two_pi (n : ℕ) :
    Function.Periodic (referenceAngularBasis n) (2 * Real.pi) := by
  intro θ
  calc
    referenceAngularBasis n (θ + 2 * Real.pi) =
        referenceAngularBasis n ((θ + Real.pi) + Real.pi) := by congr 1; ring
    _ = referenceAngularBasis n θ :=
      (referenceAngularBasis_periodic n (θ + Real.pi)).trans (referenceAngularBasis_periodic n θ)

theorem deriv_deriv_referenceAngularBasis (n : ℕ) (θ : ℝ) :
    deriv (deriv (referenceAngularBasis n)) θ =
      -(((2 * n : ℕ) : ℝ) ^ 2) * referenceAngularBasis n θ := by
  cases n with
  | zero => simp only [referenceAngularBasis, deriv_const', deriv_const, Nat.mul_zero,
      Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_mul]
  | succ n => exact deriv_deriv_cosineMode (2 * (n + 1)) θ

theorem referenceAngularCoefficient_second_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) (n : ℕ) :
    referenceAngularCoefficient (deriv (deriv f)) n =
      -(((2 * n : ℕ) : ℝ) ^ 2) * referenceAngularCoefficient f n := by
  have h := reference_integral_periodic_mul_second_deriv
    (contDiff_referenceAngularBasis n) hf (referenceAngularBasis_periodic_two_pi n) hp
  have he : (fun θ => deriv (deriv f) θ * referenceAngularBasis n θ) =
      (fun θ => referenceAngularBasis n θ * deriv (deriv f) θ) :=
    funext fun _ => mul_comm _ _
  unfold referenceAngularCoefficient radialAngularMean
  rw [he, h]
  simp_rw [deriv_deriv_referenceAngularBasis]
  have he' : (fun θ => -(((2 * n : ℕ) : ℝ) ^ 2) * referenceAngularBasis n θ * f θ) =
      (fun θ => -(((2 * n : ℕ) : ℝ) ^ 2) * (f θ * referenceAngularBasis n θ)) := by
    funext θ
    ring
  rw [he', intervalIntegral.integral_const_mul]
  ring

theorem referenceRadialCoefficient_angularPartial_twice {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u (0, 2 * Real.pi)) (n : ℕ) (r : ℝ) :
    referenceRadialCoefficient (angularPartial (angularPartial u)) n r =
      -(((2 * n : ℕ) : ℝ) ^ 2) * referenceRadialCoefficient u n r := by
  let f : ℝ → ℝ := fun θ => u (r, θ)
  have hf : ContDiff ℝ ∞ f := hu.comp (contDiff_const.prodMk contDiff_id)
  have hfp : Function.Periodic f (2 * Real.pi) := by
    intro θ
    simpa only [f, Prod.mk_add_mk, add_zero] using hp (r, θ)
  have hα : ContDiff ℝ ∞ (angularPartial u) :=
    r11b_contDiff_directionalPartial hu (0, 1)
  have hdf : deriv f = fun θ => angularPartial u (r, θ) := by
    funext θ
    exact (hasDerivAt_angular_slice (hu.differentiable (by simp) (r, θ))).deriv
  have hddf : deriv (deriv f) = fun θ => angularPartial (angularPartial u) (r, θ) := by
    rw [hdf]
    funext θ
    exact (hasDerivAt_angular_slice (hα.differentiable (by simp) (r, θ))).deriv
  simpa only [referenceRadialCoefficient, hddf, f] using
    referenceAngularCoefficient_second_deriv hf hfp n

/-- The coefficient of the actual PDE is the actual scalar Jacobi operator
applied to that coefficient. -/
theorem referenceRadialCoefficient_radialPDE {w : ℝ → ℝ} {u : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (0, 2 * Real.pi)) (n : ℕ) (r : ℝ) :
    referenceRadialCoefficient
      (fun x => radialPDE w (fun s θ => u (s, θ)) x.1 x.2) n r =
        radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) w (referenceRadialCoefficient u n) r := by
  have hur : ContDiff ℝ ∞ (radialPartial u) := r11b_contDiff_directionalPartial hu (1, 0)
  have hurr : ContDiff ℝ ∞ (radialPartial (radialPartial u)) :=
    r11b_contDiff_directionalPartial hur (1, 0)
  have huθ : ContDiff ℝ ∞ (angularPartial u) := r11b_contDiff_directionalPartial hu (0, 1)
  have huθθ : ContDiff ℝ ∞ (angularPartial (angularPartial u)) :=
    r11b_contDiff_directionalPartial huθ (0, 1)
  have hc : ContDiff ℝ ∞ (referenceRadialCoefficient u n) :=
    contDiff_referenceRadialCoefficient hu n
  have hcd := (contDiff_infty_iff_deriv.mp hc).2
  have hflux : deriv (fun t => w t * deriv (referenceRadialCoefficient u n) t) r =
      deriv w r * deriv (referenceRadialCoefficient u n) r +
        w r * deriv (deriv (referenceRadialCoefficient u n)) r :=
    ((hw.differentiable (by simp) r).hasDerivAt.fun_mul
      (hcd.differentiable (by simp) r).hasDerivAt).deriv
  have h₁ : Continuous (fun θ => deriv w r * radialPartial u (r, θ)) :=
    continuous_const.mul (hur.continuous.comp (continuous_const.prodMk continuous_id))
  have h₂ : Continuous (fun θ => w r * radialPartial (radialPartial u) (r, θ)) :=
    continuous_const.mul (hurr.continuous.comp (continuous_const.prodMk continuous_id))
  have h₃ : Continuous (fun θ => deriv w r / r * angularPartial (angularPartial u) (r, θ)) :=
    continuous_const.mul (huθθ.continuous.comp (continuous_const.prodMk continuous_id))
  have hfun : (fun θ => radialPDE w (fun s φ => u (s, φ)) r θ) =
      (fun θ => (deriv w r * radialPartial u (r, θ) +
        w r * radialPartial (radialPartial u) (r, θ)) +
          deriv w r / r * angularPartial (angularPartial u) (r, θ)) := by
    funext θ
    exact radialPDE_eq_polar_jets (w := w) (η := u) (x := (r, θ))
      (hw.differentiable (by simp) r) hu
  have hcoef : referenceRadialCoefficient
      (fun x => radialPDE w (fun s θ => u (s, θ)) x.1 x.2) n r =
      deriv w r * referenceRadialCoefficient (radialPartial u) n r +
        w r * referenceRadialCoefficient (radialPartial (radialPartial u)) n r +
          (deriv w r / r) * referenceRadialCoefficient (angularPartial (angularPartial u)) n r := by
    change referenceAngularCoefficient (fun θ => radialPDE w (fun s φ => u (s, φ)) r θ) n = _
    have h₁₂ : Continuous (fun θ => deriv w r * radialPartial u (r, θ) +
        w r * radialPartial (radialPartial u) (r, θ)) := h₁.add h₂
    rw [hfun, referenceAngularCoefficient_add
      (memLp_referenceAngular_interval_of_continuous h₁₂)
      (memLp_referenceAngular_interval_of_continuous h₃),
      referenceAngularCoefficient_add (memLp_referenceAngular_interval_of_continuous h₁)
        (memLp_referenceAngular_interval_of_continuous h₂)]
    simp only [referenceAngularCoefficient_const_mul, referenceRadialCoefficient]
  rw [hcoef, radialJacobi, hflux]
  simp only [deriv_referenceRadialCoefficient hu, deriv_referenceRadialCoefficient hur,
    referenceRadialCoefficient_angularPartial_twice hu hp]
  ring

/-- Finite basis separation includes the constant mode without assigning it
the positive-mode normalization. -/
theorem radialPDE_finite_basis_sum {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (I : Finset ℕ) (v : ℕ → ℝ → ℝ) (hv : ∀ n ∈ I, ContDiff ℝ ∞ (v n))
    (r θ : ℝ) :
    radialPDE w (fun s φ => ∑ n ∈ I, v n s * referenceAngularBasis n φ) r θ =
      ∑ n ∈ I, radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) w (v n) r *
        referenceAngularBasis n θ := by
  have hrad (s : ℝ) : deriv (fun t => ∑ n ∈ I, v n t * referenceAngularBasis n θ) s =
      ∑ n ∈ I, deriv (v n) s * referenceAngularBasis n θ :=
    (HasDerivAt.fun_sum fun n hn =>
      ((hv n hn).differentiable (by simp) s).hasDerivAt.mul_const
        (referenceAngularBasis n θ)).deriv
  have hfluxEq : (fun s => w s * deriv
      (fun t => ∑ n ∈ I, v n t * referenceAngularBasis n θ) s) =
        (fun s => ∑ n ∈ I, (w s * deriv (v n) s) * referenceAngularBasis n θ) := by
    funext s
    rw [hrad, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hfluxd (n : ℕ) (hn : n ∈ I) :
      DifferentiableAt ℝ (fun s => w s * deriv (v n) s) r :=
    (hw.mul (contDiff_infty_iff_deriv.mp (hv n hn)).2).differentiable (by simp) r
  have hflux := (HasDerivAt.fun_sum fun n hn =>
    (hfluxd n hn).hasDerivAt.mul_const (referenceAngularBasis n θ)).deriv
  have hang : deriv (fun φ => ∑ n ∈ I, v n r * referenceAngularBasis n φ) =
      (fun φ => ∑ n ∈ I, v n r * deriv (referenceAngularBasis n) φ) := by
    funext φ
    exact (HasDerivAt.fun_sum fun n _hn =>
      ((contDiff_referenceAngularBasis n).differentiable (by simp) φ).hasDerivAt.const_mul
        (v n r)).deriv
  have hang₂ : deriv (deriv (fun φ => ∑ n ∈ I, v n r * referenceAngularBasis n φ)) θ =
      ∑ n ∈ I, v n r * deriv (deriv (referenceAngularBasis n)) θ := by
    rw [hang]
    exact (HasDerivAt.fun_sum fun n _hn =>
      (((contDiff_infty_iff_deriv.mp (contDiff_referenceAngularBasis n)).2).differentiable
        (by simp) θ).hasDerivAt.const_mul (v n r)).deriv
  unfold radialPDE
  rw [hfluxEq, hflux, hang₂, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [deriv_deriv_referenceAngularBasis]
  unfold radialJacobi
  ring

theorem referenceBasisProjection_radialPDE {w : ℝ → ℝ} {u : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (0, 2 * Real.pi)) (I : Finset ℕ) :
    referenceBasisProjection I (fun x => radialPDE w (fun r θ => u (r, θ)) x.1 x.2) =
      (fun x => radialPDE w (fun r θ => referenceBasisProjection I u (r, θ)) x.1 x.2) := by
  funext x
  change (∑ n ∈ I, referenceRadialCoefficient
    (fun y => radialPDE w (fun r θ => u (r, θ)) y.1 y.2) n x.1 *
      referenceAngularBasis n x.2) =
    radialPDE w (fun r θ => ∑ n ∈ I, referenceRadialCoefficient u n r *
      referenceAngularBasis n θ) x.1 x.2
  rw [radialPDE_finite_basis_sum hw I (referenceRadialCoefficient u)
    (fun n _ => contDiff_referenceRadialCoefficient hu n)]
  exact Finset.sum_congr rfl (fun n _ => by rw [referenceRadialCoefficient_radialPDE hw hu hp])

end

end ContinuousFlexibility.Radial
