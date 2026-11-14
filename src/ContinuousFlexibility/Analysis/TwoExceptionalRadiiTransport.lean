module

public import ContinuousFlexibility.Analysis.AiryHalfHolonomy

/-!
# Constancy with two exceptional physical radii

A continuous scalar trajectory with zero actual derivative off two
interior radii has equal endpoint values. The proof applies the ordinary
mean value theorem on the three intervals determined by the two radii.
There is no condition on how often the original trajectory meets a
geometric interface and no regularity assumption at the exceptional radii.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem endpoint_eq_of_hasDerivAt_zero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) : f b = f a := by
  rcases hab.eq_or_lt with he | hlt
  · rw [he]
  · obtain ⟨t, _, ht⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hlt hc hd
    have hz : 0 * (b - a) = f b - f a :=
      (eq_div_iff (sub_ne_zero.mpr hlt.ne')).mp ht
    linarith only [hz]

private theorem endpoint_eq_of_hasDerivAt_zero_off_ordered_pair
    {f : ℝ → ℝ} {a b c d : ℝ} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b)
    (hcd : c ≤ d) (hf : ContinuousOn f (Icc a b))
    (hzero : ∀ t ∈ Ioo a b, t ≠ c → t ≠ d → HasDerivAt f 0 t) :
    f b = f a := by
  have hleft : f c = f a := endpoint_eq_of_hasDerivAt_zero hc.1.le
    (hf.mono (Icc_subset_Icc le_rfl hc.2.le)) (fun t ht =>
      hzero t ⟨ht.1, ht.2.trans hc.2⟩ ht.2.ne (ht.2.trans_le hcd).ne)
  have hmiddle : f d = f c := endpoint_eq_of_hasDerivAt_zero hcd
    (hf.mono (Icc_subset_Icc hc.1.le hd.2.le)) (fun t ht =>
      hzero t ⟨hc.1.trans ht.1, ht.2.trans hd.2⟩ ht.1.ne' ht.2.ne)
  have hright : f b = f d := endpoint_eq_of_hasDerivAt_zero hd.2.le
    (hf.mono (Icc_subset_Icc hd.1.le le_rfl)) (fun t ht =>
      hzero t ⟨hd.1.trans ht.1, ht.2⟩ (hcd.trans_lt ht.1).ne' ht.1.ne')
  exact hright.trans (hmiddle.trans hleft)

/-- The two excluded radii may coincide and need not be given in order.
Continuity is enough at each of them. -/
theorem endpoint_eq_of_hasDerivAt_zero_off_pair
    {f : ℝ → ℝ} {a b c d : ℝ} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b))
    (hzero : ∀ t ∈ Ioo a b, t ≠ c → t ≠ d → HasDerivAt f 0 t) :
    f b = f a := by
  rcases le_total c d with hcd | hdc
  · exact endpoint_eq_of_hasDerivAt_zero_off_ordered_pair hc hd hcd hf hzero
  · exact endpoint_eq_of_hasDerivAt_zero_off_ordered_pair hd hc hdc hf
      (fun t ht htd htc => hzero t ht htc htd)

end ContinuousFlexibility.Analysis
