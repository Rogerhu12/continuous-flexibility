import ContinuousFlexibility.Analysis.N06DegenerateGraph
import ContinuousFlexibility.Analysis.CylinderSobolev
import ContinuousFlexibility.Radial.R11bFiniteSynthesis
import ContinuousFlexibility.Radial.FiniteFourierProjection

/-!
# Finite-mode transfer of the weighted graph estimate

Finite synthesis is the existing actual function `r11bFiniteSynthesis`.
Parseval is applied to the angular variable before radial integration.
All coordinate derivatives below are the actual Fréchet partials.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

/-- The normalized angular square integral on the unit radial cylinder,
with an integral power of the vanishing endpoint weight. -/
def n06CylinderSquare (k : ℕ) (f : PolarPoint → ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, cylinderWeight y ^ k *
    angularAverage (fun θ => f (y, θ) ^ 2)

/-- Actual finite-dimensional Parseval, with any radial endpoint weight. -/
theorem n06CylinderSquare_finiteSynthesis {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u e : ι → ℝ → ℝ) (k : ℕ)
    (hu : ∀ i ∈ s, Continuous (u i))
    (he : ∀ i ∈ s, MemLp (e i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    n06CylinderSquare k (r11bFiniteSynthesis s u e) =
      ∑ i ∈ s, ∫ y in (0 : ℝ)..1, cylinderWeight y ^ k * u i y ^ 2 := by
  unfold n06CylinderSquare
  have hpoint (y : ℝ) :
      cylinderWeight y ^ k *
        angularAverage (fun θ => r11bFiniteSynthesis s u e (y, θ) ^ 2) =
      ∑ i ∈ s, cylinderWeight y ^ k * u i y ^ 2 := by
    unfold r11bFiniteSynthesis
    rw [angularAverage_sq_finite_sum s e he horth (fun i => u i y),
      Finset.mul_sum]
  simp_rw [hpoint]
  apply intervalIntegral.integral_finsetSum
  intro i hi
  exact ((cylinderWeight_continuous.pow k).mul ((hu i hi).pow 2)).intervalIntegrable _ _

/-- Constant mode multipliers pass through the same Parseval identity. -/
theorem n06CylinderSquare_finite_multiplier {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u e : ι → ℝ → ℝ) (a : ι → ℝ) (k : ℕ)
    (hu : ∀ i ∈ s, Continuous (u i))
    (he : ∀ i ∈ s, MemLp (e i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    n06CylinderSquare k (r11bFiniteSynthesis s (fun i y => a i * u i y) e) =
      ∑ i ∈ s, a i ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ k * u i y ^ 2) := by
  rw [n06CylinderSquare_finiteSynthesis s (fun i y => a i * u i y) e k
    (fun i hi => continuous_const.mul (hu i hi)) he horth]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  ring

/-- Summing the one-dimensional estimate allows any nonnegative angular
spectral weight, in particular every fixed Sobolev order. -/
theorem n06_finite_weighted_graph_sum {ι : Type*}
    (s : Finset ι) (u F : ι → ℝ → ℝ) (ν w : ι → ℝ)
    {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ∀ i ∈ s, ContDiff ℝ 2 (u i))
    (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hF : ∀ i ∈ s, ∀ y, F i y =
      -deriv (fun t => a t * deriv (u i) t) y +
        ν i ^ 2 * c y * u i y + V y * u i y)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    (∑ i ∈ s, w i *
      ((∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv (u i) y) ^ 2) +
        (1 + ν i ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u i y ^ 2) +
        (∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv (u i)) y) ^ 2) +
        (1 + ν i ^ 2) ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 6 * u i y ^ 2) +
        (1 + ν i ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv (u i) y ^ 2))) ≤
      16384 * K ^ 10 * ∑ i ∈ s, w i *
        ((∫ y in (0 : ℝ)..1, F i y ^ 2) + ∫ y in (0 : ℝ)..1, u i y ^ 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left
    (n06_smooth_cubic_graph_bound ha (hu i hi) hc hV hq (hF i hi)
      hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂) (hw i hi)
  convert h using 1 <;> ring

theorem n06_contDiff_finiteSynthesis {ι : Type*}
    (s : Finset ι) (u e : ι → ℝ → ℝ)
    (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i)) :
    ContDiff ℝ ∞ (r11bFiniteSynthesis s u e) :=
  ContDiff.sum (fun i hi =>
    ((hu i hi).comp contDiff_fst).mul ((he i hi).comp contDiff_snd))

/-- The actual radial partial is the finite synthesis of radial derivatives. -/
theorem n06_radialPartial_finiteSynthesis {ι : Type*}
    (s : Finset ι) (u e : ι → ℝ → ℝ)
    (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i)) :
    radialPartial (r11bFiniteSynthesis s u e) =
      r11bFiniteSynthesis s (fun i => deriv (u i)) e := by
  funext p
  rw [← deriv_cylinder_radial_slice
    ((n06_contDiff_finiteSynthesis s u e hu he).differentiable (by simp)) p.1 p.2]
  exact (HasDerivAt.fun_sum (fun i hi =>
    (((hu i hi).differentiable (by simp) p.1).hasDerivAt.mul_const (e i p.2)))).deriv

/-- The actual angular partial is the finite synthesis in the partner family. -/
theorem n06_angularPartial_finiteSynthesis {ι : Type*}
    (s : Finset ι) (u e o : ι → ℝ → ℝ) (ν : ι → ℝ)
    (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (hderiv : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (ν i * o i θ) θ) :
    angularPartial (r11bFiniteSynthesis s u e) =
      r11bFiniteSynthesis s (fun i y => ν i * u i y) o := by
  funext p
  rw [← deriv_cylinder_angular_slice
    ((n06_contDiff_finiteSynthesis s u e hu he).differentiable (by simp)) p.1 p.2]
  have h := (HasDerivAt.fun_sum
    (fun i hi => (hderiv i hi p.2).const_mul (u i p.1))).deriv
  calc
    deriv (fun θ => r11bFiniteSynthesis s u e (p.1, θ)) p.2 =
        ∑ i ∈ s, u i p.1 * (ν i * o i p.2) := h
    _ = r11bFiniteSynthesis s (fun i y => ν i * u i y) o p := by
      apply Finset.sum_congr rfl
      intro i _
      ring

end ContinuousFlexibility.Analysis
