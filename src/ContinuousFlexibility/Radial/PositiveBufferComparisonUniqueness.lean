import ContinuousFlexibility.Radial.PositiveBufferComparison

/-!
# Uniqueness and conormal proportionality on a positive half-line

Bounded homogeneous solutions are fixed by their finite endpoint trace.
The derivative identity at that endpoint follows from the ordinary
one-sided derivative, without any hypothesis on derivatives at infinity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real

theorem positiveBuffer_halfline_proportional {a m Mu Mp : ℝ}
    {u du p dp q : ℝ → ℝ} (hm : 0 < m) (hMu : 0 ≤ Mu) (hMp : 0 ≤ Mp)
    (huc : ContinuousOn u (Ici a)) (hpc : ContinuousOn p (Ici a))
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioi a, HasDerivAt du (q x * u x) x)
    (hp : ∀ x ∈ Ioi a, HasDerivAt p (dp x) x)
    (hdp : ∀ x ∈ Ioi a, HasDerivAt dp (q x * p x) x)
    (hq : ∀ x ∈ Ioi a, m ^ 2 ≤ q x) (hp0 : p a = 1)
    (hub : ∀ x ∈ Ici a, |u x| ≤ Mu) (hpb : ∀ x ∈ Ici a, |p x| ≤ Mp) :
    ∀ x ∈ Ici a, u x = u a * p x := by
  have hdb : ∀ x ∈ Ici a, |u x - u a * p x| ≤ Mu + |u a| * Mp := by
    intro x hx
    calc
      _ ≤ |u x| + |u a * p x| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (u x) (-(u a * p x))
      _ ≤ Mu + |u a| * Mp := by
        rw [abs_mul]
        exact add_le_add (hub x hx) (mul_le_mul_of_nonneg_left (hpb x hx) (abs_nonneg _))
  have h := positiveBuffer_halfline_abs_exponential_bound
    (u := fun x => u x - u a * p x) (du := fun x => du x - u a * dp x) (q := q)
    hm (show 0 ≤ Mu + |u a| * Mp by positivity)
    (huc.sub (hpc.const_mul (u a)))
    (fun x hx => (hu x hx).fun_sub ((hp x hx).const_mul (u a)))
    (fun x hx => by
      convert (hdu x hx).fun_sub ((hdp x hx).const_mul (u a)) using 1 <;> ring)
    hq hdb
  intro x hx
  have hz : |u x - u a * p x| ≤ 0 := by
    simpa only [hp0, mul_one, sub_self, abs_zero, zero_mul] using h x hx
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

theorem positiveBuffer_derivative_eq_of_eqOn_right {a du dv : ℝ} {u v : ℝ → ℝ}
    (hu : HasDerivAt u du a) (hv : HasDerivAt v dv a)
    (he : EqOn u v (Ici a)) : du = dv := by
  have ha : a ∈ Ici a := by change a ≤ a; exact le_rfl
  have hzero : u a - v a = 0 := sub_eq_zero.mpr (he ha)
  have hd := hu.fun_sub hv
  have hle := positiveBuffer_right_derivative_nonpos hd hzero (fun x hx => by
    rw [he (Ioi_subset_Ici_self hx), sub_self])
  have hge := positiveBuffer_right_derivative_nonpos hd.fun_neg
    (by rw [hzero, neg_zero]) (fun x hx => by
      rw [he (Ioi_subset_Ici_self hx), sub_self, neg_zero])
  linarith

theorem positiveBuffer_halfline_proportional_derivative {a m Mu Mp : ℝ}
    {u du p dp q : ℝ → ℝ} (hm : 0 < m) (hMu : 0 ≤ Mu) (hMp : 0 ≤ Mp)
    (huc : ContinuousOn u (Ici a)) (hpc : ContinuousOn p (Ici a))
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioi a, HasDerivAt du (q x * u x) x)
    (hp : ∀ x ∈ Ioi a, HasDerivAt p (dp x) x)
    (hdp : ∀ x ∈ Ioi a, HasDerivAt dp (q x * p x) x)
    (hq : ∀ x ∈ Ioi a, m ^ 2 ≤ q x) (hp0 : p a = 1)
    (hub : ∀ x ∈ Ici a, |u x| ≤ Mu) (hpb : ∀ x ∈ Ici a, |p x| ≤ Mp)
    (hu0 : HasDerivAt u (du a) a) (hp0d : HasDerivAt p (dp a) a) :
    du a = u a * dp a := by
  exact positiveBuffer_derivative_eq_of_eqOn_right hu0 (hp0d.const_mul (u a))
    (fun _ hx => positiveBuffer_halfline_proportional hm hMu hMp huc hpc hu hdu hp hdp
      hq hp0 hub hpb _ hx)

end ContinuousFlexibility.Radial
