import ContinuousFlexibility.Radial.FourierCompleteness
import ContinuousFlexibility.Radial.AngularMeanProbability

/-! # Uniqueness from the actual angular cosine coefficients -/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory

theorem angularAverage_sub_of_memLp {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    angularAverage (fun θ => f θ - g θ) = angularAverage f - angularAverage g := by
  rw [angularAverage_eq_integral_angularMeanMeasure,
    angularAverage_eq_integral_angularMeanMeasure, angularAverage_eq_integral_angularMeanMeasure]
  exact integral_sub
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (memLp_angularMeanMeasure hf))
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (memLp_angularMeanMeasure hg))

theorem angularPairing_sub_left_of_memLp {f g e : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (he : MemLp e 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    angularPairing (fun θ => f θ - g θ) e = angularPairing f e - angularPairing g e := by
  simp only [angularPairing, angularAverage_eq_integral_angularMeanMeasure, sub_mul]
  exact integral_sub
    ((memLp_angularMeanMeasure hf).integrable_mul (memLp_angularMeanMeasure he))
    ((memLp_angularMeanMeasure hg).integrable_mul (memLp_angularMeanMeasure he))

/-- Equality of the mean and all positive even cosine moments implies a.e.
equality of raw even, π-periodic L² functions on an angular period. -/
theorem even_periodic_ae_eq_of_cosine_coefficients {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hfe : Function.Even f) (hge : Function.Even g)
    (hfp : Function.Periodic f Real.pi) (hgp : Function.Periodic g Real.pi)
    (hmean : angularAverage f = angularAverage g)
    (hcoeff : ∀ j : ℕ, 0 < j → Even j →
      angularPairing f (cosineMode j) = angularPairing g (cosineMode j)) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] g := by
  have he : Function.Even (fun θ => f θ - g θ) := by
    intro θ
    rw [hfe θ, hge θ]
  have hp : Function.Periodic (fun θ => f θ - g θ) Real.pi := by
    intro θ
    rw [hfp θ, hgp θ]
  have hm : angularAverage (fun θ => f θ - g θ) = 0 := by
    rw [angularAverage_sub_of_memLp hf hg, hmean, sub_self]
  have hz := even_periodic_ae_eq_zero_of_cosine_coefficients (hf.sub hg) he hp hm
    (fun j hj hjEven => by
      have hjLp : MemLp (cosineMode j) 2
          (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
        apply angularInterval_memLp_of_continuous
        exact continuous_const.mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      rw [angularPairing_sub_left_of_memLp hf hg hjLp, hcoeff j hj hjEven, sub_self])
  filter_upwards [hz] with θ hθ
  change f θ - g θ = 0 at hθ
  exact sub_eq_zero.mp hθ

end

end ContinuousFlexibility.Radial
