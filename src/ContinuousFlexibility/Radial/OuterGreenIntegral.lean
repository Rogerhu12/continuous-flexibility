import ContinuousFlexibility.Radial.OuterKernelL2
import Mathlib.Topology.Order.Lattice

/-!
# The normalized outer Green kernel and its core operator

The same min/max formula is used on the radial interval and on its compact
core.  The core operator is constructed from that kernel by the `L²`
construction, with its mass estimate proved explicitly.  The tail algebra
proves the Dirichlet-plus-rank-one decomposition without division by any
boundary value.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

section Kernel

variable {X : Type*} [LinearOrder X]

/-- The outer Green kernel, normalized by the full-state flux scale. -/
def outerGreenKernel (lam : ℝ) (U V : X → ℝ) (x y : X) : ℝ :=
  lam⁻¹ * (U (min x y) * V (max x y))

theorem outerGreenKernel_symm (lam : ℝ) (U V : X → ℝ) (x y : X) :
    outerGreenKernel lam U V x y = outerGreenKernel lam U V y x := by
  simp only [outerGreenKernel, min_comm x y, max_comm x y]

theorem outerGreenKernel_of_le {lam : ℝ} {U V : X → ℝ} {x y : X} (hxy : x ≤ y) :
    outerGreenKernel lam U V x y = lam⁻¹ * (U x * V y) := by
  simp only [outerGreenKernel, min_eq_left hxy, max_eq_right hxy]

theorem outerGreenKernel_self (lam : ℝ) (U V : X → ℝ) (x : X) :
    outerGreenKernel lam U V x x = lam⁻¹ * (U x * V x) := by
  simp only [outerGreenKernel, min_self, max_self]

/-- The core pointwise estimate uses only the transfer bounds on the two solutions. -/
theorem abs_outerGreenKernel_le {lam K : ℝ} {U V : X → ℝ}
    (hlam : 0 < lam) (hK : 0 ≤ K) (hU : ∀ x, |U x| ≤ K) (hV : ∀ x, |V x| ≤ K)
    (x y : X) : |outerGreenKernel lam U V x y| ≤ K ^ 2 / lam := by
  rw [outerGreenKernel, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hlam)]
  calc
    lam⁻¹ * (|U (min x y)| * |V (max x y)|) ≤ lam⁻¹ * (K * K) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (hU _) (hV _) (abs_nonneg _) hK) (inv_nonneg.mpr hlam.le)
    _ = K ^ 2 / lam := by ring

/-- The core/tail block is a separated kernel, using the actual tail Poisson solution. -/
theorem outerGreenKernel_core_tail {lam : ℝ} {U V P : X → ℝ} {c x y : X}
    (hx : x ≤ c) (hy : c ≤ y) (hV : V y = V c * P y) :
    outerGreenKernel lam U V x y = (V c / lam) * U x * P y := by
  rw [outerGreenKernel_of_le (hx.trans hy), hV]
  ring

/-- The full tail kernel is the Dirichlet kernel plus one rank-one kernel.
The homogeneous state identity is used in a form that never divides by `V c`. -/
theorem outerGreenKernel_tail_decomposition {lam : ℝ} {U V P Q : X → ℝ} {c : X}
    (hlam : lam ≠ 0)
    (hV : ∀ x, c ≤ x → V x = V c * P x)
    (hQ : ∀ x, c ≤ x → V c * U x - U c * V x = lam * Q x)
    {x y : X} (hx : c ≤ x) (hy : c ≤ y) :
    outerGreenKernel lam U V x y = Q (min x y) * P (max x y) +
      outerGreenKernel lam U V c c * (P x * P y) := by
  have hmin : c ≤ min x y := le_min hx hy
  have hmax : c ≤ max x y := hx.trans (le_max_left _ _)
  have hleft : V c * U (min x y) =
      lam * Q (min x y) + U c * V c * P (min x y) := by
    have h := hQ (min x y) hmin
    rw [hV (min x y) hmin] at h
    linear_combination h
  have hprod : P (min x y) * P (max x y) = P x * P y := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy, max_eq_right hxy]
    · rw [min_eq_right hyx, max_eq_left hyx, mul_comm]
  calc
    outerGreenKernel lam U V x y = lam⁻¹ * ((V c * U (min x y)) * P (max x y)) := by
      rw [outerGreenKernel, hV (max x y) hmax]
      ring
    _ = lam⁻¹ * ((lam * Q (min x y) + U c * V c * P (min x y)) * P (max x y)) := by
      rw [hleft]
    _ = Q (min x y) * P (max x y) +
        (lam⁻¹ * (U c * V c)) * (P (min x y) * P (max x y)) := by
      field_simp [hlam] <;> ring
    _ = Q (min x y) * P (max x y) +
        outerGreenKernel lam U V c c * (P x * P y) := by
      rw [hprod, outerGreenKernel_self]

end Kernel

section ContinuousCore

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderClosedTopology X]
  [CompactSpace X] [LocallyCompactSpace X]

/-- The actual normalized Green kernel as a continuous family of continuous rows. -/
def outerContinuousGreenKernel (lam : ℝ) (U V : C(X, ℝ)) : C(X, C(X, ℝ)) :=
  (⟨fun xy : X × X => outerGreenKernel lam U V xy.1 xy.2,
    continuous_const.mul
      ((U.continuous.comp (continuous_fst.min continuous_snd)).mul
        (V.continuous.comp (continuous_fst.max continuous_snd)))⟩ : C(X × X, ℝ)).curry

theorem outerContinuousGreenKernel_apply (lam : ℝ) (U V : C(X, ℝ)) (x y : X) :
    outerContinuousGreenKernel lam U V x y = outerGreenKernel lam U V x y := by
  rw [outerContinuousGreenKernel, ContinuousMap.curry_apply, ContinuousMap.coe_mk]

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- The core/core block, constructed from the actual two homogeneous solutions. -/
def outerCoreGreenOperator (lam : ℝ) (U V : C(X, ℝ)) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  outerKernelL2 μ (outerContinuousGreenKernel lam U V)

theorem outerCoreGreenOperator_ae_eq_integral (lam : ℝ) (U V : C(X, ℝ)) (f : Lp ℝ 2 μ) :
    outerCoreGreenOperator μ lam U V f =ᵐ[μ]
      fun x => ∫ y, outerGreenKernel lam U V x y * f y ∂μ := by
  simpa only [outerCoreGreenOperator, outerContinuousGreenKernel_apply] using
    outerKernelL2_ae_eq_integral μ (outerContinuousGreenKernel lam U V) f

/-- The core estimate before canceling the scale against the core mass. -/
theorem norm_outerCoreGreenOperator_le {lam K : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K)
    (U V : C(X, ℝ)) (hU : ∀ x, |U x| ≤ K) (hV : ∀ x, |V x| ≤ K) :
    ‖outerCoreGreenOperator μ lam U V‖ ≤ (measureUnivNNReal μ : ℝ) * (K ^ 2 / lam) := by
  apply norm_outerKernelL2_le_of_bound μ (outerContinuousGreenKernel lam U V)
    (div_nonneg (sq_nonneg K) hlam.le)
  intro x y
  rw [outerContinuousGreenKernel_apply]
  exact abs_outerGreenKernel_le hlam hK hU hV x y

/-- Core mass cancels `λ⁻¹` in the actual integral operator. -/
theorem norm_outerCoreGreenOperator_scale_cancel {lam A K : ℝ}
    (hlam : 0 < lam) (hK : 0 ≤ K)
    (U V : C(X, ℝ)) (hU : ∀ x, |U x| ≤ K) (hV : ∀ x, |V x| ≤ K)
    (hmass : (measureUnivNNReal μ : ℝ) ≤ lam * A ^ 2) :
    ‖outerCoreGreenOperator μ lam U V‖ ≤ A ^ 2 * K ^ 2 := by
  calc
    ‖outerCoreGreenOperator μ lam U V‖ ≤ (measureUnivNNReal μ : ℝ) * (K ^ 2 / lam) :=
      norm_outerCoreGreenOperator_le μ hlam hK U V hU hV
    _ ≤ (lam * A ^ 2) * (K ^ 2 / lam) :=
      mul_le_mul_of_nonneg_right hmass (div_nonneg (sq_nonneg K) hlam.le)
    _ = A ^ 2 * K ^ 2 := by field_simp [hlam.ne'] <;> ring

end ContinuousCore

end ContinuousFlexibility.Radial
