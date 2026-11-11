import ContinuousFlexibility.Radial.R11bPhysicalCompleteness
import ContinuousFlexibility.Radial.R11bLpConvergence
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Continuity of actual product L² coefficients

A unit L² angular factor defines a contraction from product L² to radial
L². Its value on an actual representative is the original angular integral.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

theorem r11b_modeCoefficient_congr_ae {f g : α × β → ℝ}
    (hfg : f =ᵐ[μ.prod ν] g) (e : β → ℝ) :
    (fun r => ∫ θ, f (r, θ) * e θ ∂ν) =ᵐ[μ]
      (fun r => ∫ θ, g (r, θ) * e θ ∂ν) := by
  filter_upwards [ae_ae_of_ae_prod hfg] with r hr
  apply integral_congr_ae
  filter_upwards [hr] with θ hθ
  exact congrArg (fun t : ℝ => t * e θ) hθ

theorem r11b_modeCoefficient_sub_ae {f g : α × β → ℝ} {e : β → ℝ}
    (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν))
    (he : MemLp e 2 ν) :
    (fun r => ∫ θ, (f (r, θ) - g (r, θ)) * e θ ∂ν) =ᵐ[μ]
      (fun r => (∫ θ, f (r, θ) * e θ ∂ν) - ∫ θ, g (r, θ) * e θ ∂ν) := by
  filter_upwards [r11b_memLp_product_sections hf,
    r11b_memLp_product_sections hg] with r hfr hgr
  simp_rw [sub_mul]
  exact integral_sub (hfr.integrable_mul he) (hgr.integrable_mul he)

def r11bModeCoefficientLp {e : β → ℝ} (he : MemLp e 2 ν)
    (u : Lp ℝ 2 (μ.prod ν)) : Lp ℝ 2 μ :=
  (r11b_memLp_modeCoefficient (Lp.memLp u) he).1.toLp
    (fun r => ∫ θ, u (r, θ) * e θ ∂ν)

theorem r11bModeCoefficientLp_coeFn {e : β → ℝ} (he : MemLp e 2 ν)
    (u : Lp ℝ 2 (μ.prod ν)) :
    (r11bModeCoefficientLp he u : α → ℝ) =ᵐ[μ]
      (fun r => ∫ θ, u (r, θ) * e θ ∂ν) :=
  (r11b_memLp_modeCoefficient (Lp.memLp u) he).1.coeFn_toLp

theorem r11bModeCoefficientLp_toLp {f : α × β → ℝ} {e : β → ℝ}
    (hf : MemLp f 2 (μ.prod ν)) (he : MemLp e 2 ν) :
    r11bModeCoefficientLp he (hf.toLp f) =
      (r11b_memLp_modeCoefficient hf he).1.toLp
        (fun r => ∫ θ, f (r, θ) * e θ ∂ν) := by
  apply Lp.ext
  filter_upwards [r11bModeCoefficientLp_coeFn he (hf.toLp f),
    (r11b_memLp_modeCoefficient hf he).1.coeFn_toLp,
    r11b_modeCoefficient_congr_ae hf.coeFn_toLp e] with r hr₁ hr₂ hr₃
  exact hr₁.trans (hr₃.trans hr₂.symm)

/-- The normalized coefficient map is a contraction on the actual L²
equivalence classes. -/
theorem r11bModeCoefficientLp_lipschitz {e : β → ℝ} (he : MemLp e 2 ν)
    (hunit : (∫ θ, e θ ^ 2 ∂ν) = 1) :
    LipschitzWith 1 (r11bModeCoefficientLp (μ := μ) he) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  let cu : α → ℝ := fun r => ∫ θ, u (r, θ) * e θ ∂ν
  let cv : α → ℝ := fun r => ∫ θ, v (r, θ) * e θ ∂ν
  have hcu : MemLp cu 2 μ := (r11b_memLp_modeCoefficient (Lp.memLp u) he).1
  have hcv : MemLp cv 2 μ := (r11b_memLp_modeCoefficient (Lp.memLp v) he).1
  have hsub : MemLp (fun z => u z - v z) 2 (μ.prod ν) := by
    apply MemLp.ae_eq _ ((Lp.memLp u).sub (Lp.memLp v))
    exact Eventually.of_forall fun _ => rfl
  have hs : ‖hcu.toLp cu - hcv.toLp cv‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
    calc
      ‖hcu.toLp cu - hcv.toLp cv‖ ^ 2 = ∫ r, (cu r - cv r) ^ 2 ∂μ :=
        r11b_norm_toLp_sub_sq hcu hcv
      _ = ∫ r, (∫ θ, (u (r, θ) - v (r, θ)) * e θ ∂ν) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [r11b_modeCoefficient_sub_ae (Lp.memLp u) (Lp.memLp v) he] with r hr
        exact congrArg (fun t : ℝ => t ^ 2) hr.symm
      _ ≤ ∫ z, (u z - v z) ^ 2 ∂μ.prod ν :=
        (r11b_modeCoefficient_contraction hsub he hunit).2
      _ = ‖u - v‖ ^ 2 := by
        symm
        simpa only [Lp.toLp_coeFn] using
          r11b_norm_toLp_sub_sq (Lp.memLp u) (Lp.memLp v)
  change ‖hcu.toLp cu - hcv.toLp cv‖ ≤ ‖u - v‖
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem r11bModeCoefficientLp_continuous {e : β → ℝ} (he : MemLp e 2 ν)
    (hunit : (∫ θ, e θ ^ 2 ∂ν) = 1) :
    Continuous (r11bModeCoefficientLp (μ := μ) he) :=
  (r11bModeCoefficientLp_lipschitz he hunit).continuous

end

end ContinuousFlexibility.Radial
