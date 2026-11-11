import ContinuousFlexibility.Radial.R11bEvenPartialSums
import ContinuousFlexibility.Radial.R11bPhysicalL2Convergence
import ContinuousFlexibility.Radial.R11bSymmetricLimit

/-!
# A symmetric physical representative of an even L² mode series

Square-summable radial L² data give a physical L² limit of the original
finite sums. The representative is pointwise even and pi-periodic at every
radius, including outside the physical core.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_evenSeries_symmetric_physical_limit
    {D : ReferenceData} (d : ℕ → ℝ → ℝ)
    (hd : ∀ n, MemLp (d n) 2 (volume.restrict (radialCore D)))
    (hsq : Summable (fun n => ∫ r, d n r ^ 2 ∂volume.restrict (radialCore D))) :
    ∃ v : PolarPoint → ℝ, ∃ hv : MemLp v 2 (radialPhysicalMeasure D),
      ∃ hP : ∀ N, MemLp (r11bEvenPartialSum d N) 2 (radialPhysicalMeasure D),
        (∀ r, Function.Periodic (fun θ => v (r, θ)) Real.pi) ∧
        (∀ r, Function.Even (fun θ => v (r, θ))) ∧
        Tendsto (fun N => (hP N).toLp (r11bEvenPartialSum d N))
          atTop (𝓝 (hv.toLp v)) := by
  let μ : Measure ℝ := volume.restrict (radialCore D)
  let V : Lp ℝ 2 (μ.prod angularMeanMeasure) :=
    ∑' n, r11bTensorL2 (hd n) (evenCosineBasis_memLp n)
  have hP (N : ℕ) : MemLp (r11bEvenPartialSum d N) 2 (μ.prod angularMeanMeasure) :=
    r11bEvenPartialSum_memLp d hd N
  have hlim : Tendsto (fun N => (hP N).toLp (r11bEvenPartialSum d N))
      atTop (𝓝 V) :=
    r11bEvenPartialSum_tendsto d hd hsq
  obtain ⟨v, hv, hvV, hp, he⟩ :=
    r11b_symmetric_representative_of_L2_tendsto hP
      (r11bEvenPartialSum_periodic d) (r11bEvenPartialSum_even d) hlim
  have hvLp : hv.toLp v = V := by
    apply Lp.ext
    exact hv.coeFn_toLp.trans hvV
  have hlimv : Tendsto (fun N => (hP N).toLp (r11bEvenPartialSum d N))
      atTop (𝓝 (hv.toLp v)) := by
    rw [hvLp]
    exact hlim
  exact ⟨v, r11b_memLp_of_radial_angularMean (D := D) hv,
    fun N => r11b_memLp_of_radial_angularMean (D := D) (hP N), hp, he,
    r11b_tendsto_toLp_physical_of_radial_angularMean (D := D) hP hv hlimv⟩

end

end ContinuousFlexibility.Radial
