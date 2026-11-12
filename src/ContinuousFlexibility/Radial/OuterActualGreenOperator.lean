import ContinuousFlexibility.Radial.OuterBlockOperator
import ContinuousFlexibility.Radial.OuterGreenIntegral

/-!
# Assembling the actual core kernel and deep-tail resolvent

The core block is the actual Green integral operator and the core vector is
the actual left homogeneous solution in L².  The two coupling coefficients
are values of the same homogeneous pair at the deep-tail entrance.  Thus
the operator bound requires neither an assumed outer inverse nor an assumed
bounded core operator.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderClosedTopology X]
  [CompactSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The constructed outer operator from the actual core homogeneous pair
and the already constructed deep Dirichlet inverse and Poisson solution. -/
def outerActualGreenOperator (lam : ℝ) (c : X) (U V : C(X, ℝ))
    (D : H →L[ℝ] H) (p : H) :
    (Lp ℝ 2 μ × H) →L[ℝ] (Lp ℝ 2 μ × H) :=
  outerBlockOperator (outerCoreGreenOperator μ lam U V) D
    (ContinuousMap.toLp 2 μ ℝ U) p (V c / lam) (U c * V c / lam)

/-- The deep block is the actual Dirichlet inverse plus the kernel diagonal
times the Poisson rank-one operator. -/
theorem outerActualGreenOperator_tail (lam : ℝ) (c : X) (U V : C(X, ℝ))
    (D : H →L[ℝ] H) (p g : H) :
    (outerActualGreenOperator μ lam c U V D p (0, g)).2 =
      D g + outerGreenKernel lam U V c c • (inner ℝ p g • p) := by
  rw [outerActualGreenOperator, outerBlockOperator_tail_apply, outerGreenKernel_self]
  congr 2
  ring

/-- Core values and core mass give the actual left-vector norm. -/
theorem norm_outerActualCoreVector_le {lam A K : ℝ} (hlam : 0 < lam)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (U : C(X, ℝ))
    (hU : ∀ x, |U x| ≤ K) (hmass : (measureUnivNNReal μ : ℝ) ≤ lam * A ^ 2) :
    ‖ContinuousMap.toLp 2 μ ℝ U‖ ≤ Real.sqrt lam * A * K := by
  have hsqrt : Real.sqrt (measureUnivNNReal μ : ℝ) ≤ Real.sqrt lam * A := by
    calc
      Real.sqrt (measureUnivNNReal μ : ℝ) ≤ Real.sqrt (lam * A ^ 2) :=
        Real.sqrt_le_sqrt hmass
      _ = Real.sqrt lam * A := by rw [Real.sqrt_mul hlam.le, Real.sqrt_sq hA]
  exact (norm_outerCoreFunction_le_of_bound μ U hK hU).trans
    (mul_le_mul_of_nonneg_right hsqrt hK)

/-- The complete scale-free estimate for the constructed outer operator. -/
theorem norm_outerActualGreenOperator_le {lam A K d : ℝ}
    (hlam : 0 < lam) (hA : 0 ≤ A) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (c : X) (U V : C(X, ℝ)) (D : H →L[ℝ] H) (p : H)
    (hU : ∀ x, |U x| ≤ K) (hV : ∀ x, |V x| ≤ K)
    (hmass : (measureUnivNNReal μ : ℝ) ≤ lam * A ^ 2)
    (hD : ‖D‖ ≤ d) (hp : ‖p‖ ≤ Real.sqrt lam * A) :
    ‖outerActualGreenOperator μ lam c U V D p‖ ≤ d + 2 * A ^ 2 * K ^ 2 := by
  have halpha : |V c / lam| ≤ K / lam := by
    rw [abs_div, abs_of_pos hlam]
    exact div_le_div_of_nonneg_right (hV c) hlam.le
  have hbeta : |U c * V c / lam| ≤ K ^ 2 / lam := by
    rw [abs_div, abs_mul, abs_of_pos hlam]
    apply div_le_div_of_nonneg_right _ hlam.le
    simpa only [pow_two] using mul_le_mul (hU c) (hV c) (abs_nonneg _) hK
  exact norm_outerBlockOperator_le hlam hA hK hd
    (outerCoreGreenOperator μ lam U V) D (ContinuousMap.toLp 2 μ ℝ U) p
    (norm_outerCoreGreenOperator_scale_cancel μ hlam hK U V hU hV hmass)
    hD halpha hbeta (norm_outerActualCoreVector_le μ hlam hA hK U hU hmass) hp

/-- The core component has a canonical continuous representative for every
core/tail L² source pair. -/
theorem outerActualGreenOperator_core_rep (lam : ℝ) (c : X) (U V : C(X, ℝ))
    (D : H →L[ℝ] H) (p : H) (f : Lp ℝ 2 μ × H) :
    (outerActualGreenOperator μ lam c U V D p f).1 =
      ContinuousMap.toLp 2 μ ℝ
        (outerKernelRepresentative μ (outerContinuousGreenKernel lam U V) f.1 +
          ((V c / lam) * inner ℝ p f.2) • U) := by
  rw [outerActualGreenOperator, outerBlockOperator_apply]
  rw [outerCoreGreenOperator, outerKernelL2_apply, map_add, map_smul]
  simp only [mul_smul]

end ContinuousFlexibility.Radial
