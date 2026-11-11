import ContinuousFlexibility.Analysis.N06FiniteModes

/-!
# The positive-cylinder graph estimate for actual finite Fourier fields

The two orthonormal angular families are derivative partners. The estimate
below is stated entirely with the actual radial and angular partials of the
synthesized field, and with ordinary square integrals on the cylinder.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

/-- The five weighted graph quantities, expanded into actual angular
derivatives instead of formal frequency multipliers. -/
def n06CylinderGraphSquare (U : PolarPoint → ℝ) : ℝ :=
  n06CylinderSquare 2 (radialPartial U) +
    n06CylinderSquare 3 U + n06CylinderSquare 3 (angularPartial U) +
    n06CylinderSquare 4 (radialPartial (radialPartial U)) +
    n06CylinderSquare 6 U + 2 * n06CylinderSquare 6 (angularPartial U) +
    n06CylinderSquare 6 (angularPartial (angularPartial U)) +
    n06CylinderSquare 5 (radialPartial U) +
    n06CylinderSquare 5 (angularPartial (radialPartial U))

/-- Parseval identifies the actual cylinder graph quantities with the
one-dimensional modal graph quantities. -/
theorem n06CylinderGraphSquare_finite {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u e o : ι → ℝ → ℝ) (ν : ι → ℝ)
    (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (ho : ∀ i ∈ s, ContDiff ℝ ∞ (o i))
    (heLp : ∀ i ∈ s, MemLp (e i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hoLp : ∀ i ∈ s, MemLp (o i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hoorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (o i) (o j) = if i = j then 1 else 0)
    (hde : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (ν i * o i θ) θ)
    (hdo : ∀ i ∈ s, ∀ θ, HasDerivAt (o i) (-ν i * e i θ) θ) :
    n06CylinderGraphSquare (r11bFiniteSynthesis s u e) =
      ∑ i ∈ s,
        ((∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv (u i) y) ^ 2) +
          (1 + ν i ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u i y ^ 2) +
          (∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv (u i)) y) ^ 2) +
          (1 + ν i ^ 2) ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 6 * u i y ^ 2) +
          (1 + ν i ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv (u i) y ^ 2)) := by
  have hu₁ (i : ι) (hi : i ∈ s) : ContDiff ℝ ∞ (deriv (u i)) :=
    (contDiff_infty_iff_deriv.mp (hu i hi)).2
  have hu₂ (i : ι) (hi : i ∈ s) : ContDiff ℝ ∞ (deriv (deriv (u i))) :=
    (contDiff_infty_iff_deriv.mp (hu₁ i hi)).2
  have hr := n06_radialPartial_finiteSynthesis s u e hu he
  have hrr : radialPartial (radialPartial (r11bFiniteSynthesis s u e)) =
      r11bFiniteSynthesis s (fun i => deriv (deriv (u i))) e := by
    rw [hr, n06_radialPartial_finiteSynthesis s _ e hu₁ he]
  have ht := n06_angularPartial_finiteSynthesis s u e o ν hu he hde
  have htt : angularPartial (angularPartial (r11bFiniteSynthesis s u e)) =
      r11bFiniteSynthesis s (fun i y => (-ν i ^ 2) * u i y) e := by
    rw [ht, n06_angularPartial_finiteSynthesis s _ o e (fun i => -ν i)
      (fun i hi => contDiff_const.mul (hu i hi)) ho hdo]
    funext p
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrt : angularPartial (radialPartial (r11bFiniteSynthesis s u e)) =
      r11bFiniteSynthesis s (fun i y => ν i * deriv (u i) y) o := by
    rw [hr, n06_angularPartial_finiteSynthesis s _ e o ν hu₁ he hde]
  unfold n06CylinderGraphSquare
  rw [hrr, htt, hrt]
  simp only [ht, hr]
  rw [n06CylinderSquare_finiteSynthesis s _ e 2
      (fun i hi => (hu₁ i hi).continuous) heLp heorth,
    n06CylinderSquare_finiteSynthesis s u e 3
      (fun i hi => (hu i hi).continuous) heLp heorth,
    n06CylinderSquare_finite_multiplier s u o ν 3
      (fun i hi => (hu i hi).continuous) hoLp hoorth,
    n06CylinderSquare_finiteSynthesis s _ e 4
      (fun i hi => (hu₂ i hi).continuous) heLp heorth,
    n06CylinderSquare_finiteSynthesis s u e 6
      (fun i hi => (hu i hi).continuous) heLp heorth,
    n06CylinderSquare_finite_multiplier s u o ν 6
      (fun i hi => (hu i hi).continuous) hoLp hoorth,
    n06CylinderSquare_finite_multiplier s u e (fun i => -ν i ^ 2) 6
      (fun i hi => (hu i hi).continuous) heLp heorth,
    n06CylinderSquare_finiteSynthesis s _ e 5
      (fun i hi => (hu₁ i hi).continuous) heLp heorth,
    n06CylinderSquare_finite_multiplier s _ o ν 5
      (fun i hi => (hu₁ i hi).continuous) hoLp hoorth]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hfirst : (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 2 * deriv (u i) y ^ 2) =
      ∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv (u i) y) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hsecond :
      (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 4 * deriv (deriv (u i)) y ^ 2) =
      ∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv (u i)) y) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [hfirst, hsecond]
  ring

/-- The finite-cylinder graph bound has the same constant as the scalar
mode estimate. No boundary condition on the synthesized solution is used. -/
theorem n06_finite_cylinder_graph_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u F e o : ι → ℝ → ℝ) (ν : ι → ℝ)
    {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hF : ∀ i ∈ s, ∀ y, F i y =
      -deriv (fun t => a t * deriv (u i) t) y +
        ν i ^ 2 * c y * u i y + V y * u i y)
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (ho : ∀ i ∈ s, ContDiff ℝ ∞ (o i))
    (heLp : ∀ i ∈ s, MemLp (e i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hoLp : ∀ i ∈ s, MemLp (o i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hoorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (o i) (o j) = if i = j then 1 else 0)
    (hde : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (ν i * o i θ) θ)
    (hdo : ∀ i ∈ s, ∀ θ, HasDerivAt (o i) (-ν i * e i θ) θ)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    n06CylinderGraphSquare (r11bFiniteSynthesis s u e) ≤
      16384 * K ^ 10 *
        (n06CylinderSquare 0 (r11bFiniteSynthesis s F e) +
          n06CylinderSquare 0 (r11bFiniteSynthesis s u e)) := by
  have hu₂ (i : ι) (hi : i ∈ s) : ContDiff ℝ 2 (u i) :=
    (hu i hi).of_le (by simp)
  have hFc (i : ι) (hi : i ∈ s) : Continuous (F i) :=
    continuous_forcing ha (hu₂ i hi) hc hV (hF i hi)
  rw [n06CylinderGraphSquare_finite s u e o ν hu he ho heLp hoLp heorth hoorth hde hdo,
    n06CylinderSquare_finiteSynthesis s F e 0 hFc heLp heorth,
    n06CylinderSquare_finiteSynthesis s u e 0
      (fun i hi => (hu i hi).continuous) heLp heorth]
  simp only [pow_zero, one_mul]
  have h := n06_finite_weighted_graph_sum s u F ν (fun _ => 1) ha hu₂ hc hV hq hF
    (fun _ _ => zero_le_one) hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
  simpa only [one_mul, Finset.sum_add_distrib] using h

end ContinuousFlexibility.Analysis
