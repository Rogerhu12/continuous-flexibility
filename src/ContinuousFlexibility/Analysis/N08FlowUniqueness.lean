import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Uniqueness with differential equations only in the open interval

The ordinary nonlinear flows are continuous at the turning points, and
their time equations are specified only in the interior.  A squared
difference multiplied by an exponential proves uniqueness in precisely
that setting, without assuming an extra derivative at either endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

theorem n08_scalarTrajectory_unique {a b K : ℝ} (hab : a ≤ b)
    {f g df dg : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : ∀ t ∈ Ioo a b, HasDerivAt f (df t) t)
    (hdg : ∀ t ∈ Ioo a b, HasDerivAt g (dg t) t)
    (hbound : ∀ t ∈ Ioo a b, |df t - dg t| ≤ K * |f t - g t|)
    (hinit : f a = g a) : EqOn f g (Icc a b) := by
  let E : ℝ → ℝ := fun t => (f t - g t) ^ 2 * Real.exp (-(2 * K) * t)
  let E' : ℝ → ℝ := fun t =>
    (2 * (f t - g t) * (df t - dg t) - 2 * K * (f t - g t) ^ 2) *
      Real.exp (-(2 * K) * t)
  have hE : ContinuousOn E (Icc a b) :=
    ((hf.sub hg).pow 2).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  have hdE (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt E (E' t) t := by
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(2 * K) * s))
        (Real.exp (-(2 * K) * t) * (-(2 * K))) t := by
      simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul (-(2 * K))).exp
    convert (((hdf t ht).sub (hdg t ht)).pow 2).mul hexp using 1 <;>
      simp only [E, E', Pi.sub_apply, Pi.pow_apply] <;> ring
  have hnonpos (t : ℝ) (ht : t ∈ Ioo a b) : E' t ≤ 0 := by
    have habs := mul_le_mul_of_nonneg_left (hbound t ht) (abs_nonneg (f t - g t))
    have hsquare : |f t - g t| * |f t - g t| = (f t - g t) ^ 2 := by
      rw [← pow_two, sq_abs]
    have hprod : (f t - g t) * (df t - dg t) ≤ K * (f t - g t) ^ 2 := by
      calc
        _ ≤ |(f t - g t) * (df t - dg t)| := le_abs_self _
        _ = |f t - g t| * |df t - dg t| := abs_mul _ _
        _ ≤ |f t - g t| * (K * |f t - g t|) := habs
        _ = K * (f t - g t) ^ 2 := by rw [← hsquare]; ring
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hprod]) (Real.exp_pos _).le
  have hanti : AntitoneOn E (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hE
      (fun t ht => (hdE t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
      (fun t ht => hnonpos t (by simpa only [interior_Icc] using ht))
  intro t ht
  have hle := hanti ⟨le_rfl, hab⟩ ht ht.1
  have hzero : E a = 0 := by simp only [E, hinit, sub_self, zero_pow two_ne_zero, zero_mul]
  rw [hzero] at hle
  have hs : (f t - g t) ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_left hle (Real.exp_pos _)
  have he : (f t - g t) ^ 2 = 0 := le_antisymm hs (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp he)

end ContinuousFlexibility.Analysis
