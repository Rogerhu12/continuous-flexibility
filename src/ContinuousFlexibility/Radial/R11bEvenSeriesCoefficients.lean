import ContinuousFlexibility.Radial.R11bEvenPartialSums
import ContinuousFlexibility.Radial.R11bCoefficientContinuity

/-!
# Actual coefficients of an L² even Fourier series

Continuity of each coefficient map passes the finite integral identity to
the strong Hilbert-space limit. No pointwise convergence of the series is used.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem r11bEvenPartialSum_coefficientLp
    (c : ℕ → α → ℝ) (hc : ∀ n, MemLp (c n) 2 μ)
    (N n : ℕ) (hn : n < N) :
    r11bModeCoefficientLp (evenCosineBasis_memLp n)
      ((r11bEvenPartialSum_memLp c hc N).toLp (r11bEvenPartialSum c N)) =
        (hc n).toLp (c n) := by
  rw [r11bModeCoefficientLp_toLp]
  apply MemLp.toLp_congr
  exact Eventually.of_forall fun r => by
    have h := r11bEvenPartialSum_coefficient c N n r
    rw [if_pos hn, evenFourierCoefficient_eq_integral] at h
    exact h

theorem r11bEvenSeries_coefficientLp
    (c : ℕ → α → ℝ) (hc : ∀ n, MemLp (c n) 2 μ)
    (hsq : Summable (fun n => ∫ r, c n r ^ 2 ∂μ)) (n : ℕ) :
    r11bModeCoefficientLp (evenCosineBasis_memLp n)
      (∑' i, r11bTensorL2 (hc i) (evenCosineBasis_memLp i)) =
        (hc n).toLp (c n) := by
  have hlim :
      Tendsto (fun N => r11bModeCoefficientLp (evenCosineBasis_memLp n)
        ((r11bEvenPartialSum_memLp c hc N).toLp (r11bEvenPartialSum c N)))
        atTop (𝓝 (r11bModeCoefficientLp (evenCosineBasis_memLp n)
          (∑' i, r11bTensorL2 (hc i) (evenCosineBasis_memLp i)))) :=
    ((r11bModeCoefficientLp_continuous (evenCosineBasis_memLp n)
      (integral_sq_evenCosineBasis n)).tendsto _).comp (r11bEvenPartialSum_tendsto c hc hsq)
  have hevent :
      (fun N => r11bModeCoefficientLp (evenCosineBasis_memLp n)
        ((r11bEvenPartialSum_memLp c hc N).toLp (r11bEvenPartialSum c N)))
        =ᶠ[atTop] (fun _ => (hc n).toLp (c n)) := by
    filter_upwards [eventually_gt_atTop n] with N hN
    exact r11bEvenPartialSum_coefficientLp c hc N n hN
  exact tendsto_nhds_unique hlim ((tendsto_congr' hevent).mpr tendsto_const_nhds)

end

end ContinuousFlexibility.Radial
