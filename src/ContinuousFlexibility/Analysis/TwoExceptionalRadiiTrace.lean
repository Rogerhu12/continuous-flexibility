module

public import ContinuousFlexibility.Analysis.TwoExceptionalRadiiTransport

/-!
# True endpoint traces with two exceptional radii

The piecewise physical first integral is only used in the open component.
Its two true one-sided limits are equal once its derivative vanishes away
from the two fixed exceptional radii. No arbitrary total value of a
canonical chart outside its own physical half enters this assertion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

private theorem eqOn_constant_of_hasDerivAt_zero_off_ordered_pair
    {f : ℝ → ℝ} {a b c d : ℝ} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b)
    (hcd : c ≤ d) (hf : ContinuousOn f (Ioo a b))
    (hzero : ∀ t ∈ Ioo a b, t ≠ c → t ≠ d → HasDerivAt f 0 t) :
    EqOn f (fun _ => f c) (Ioo a b) := by
  have hsub {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : Icc x y ⊆ Ioo a b :=
    fun t ht => ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
  have hmiddle : f d = f c := endpoint_eq_of_hasDerivAt_zero hcd
    (hf.mono (hsub hc hd)) (fun t ht =>
      hzero t ⟨hc.1.trans ht.1, ht.2.trans hd.2⟩ ht.1.ne' ht.2.ne)
  intro t ht
  by_cases htc : t ≤ c
  · exact (endpoint_eq_of_hasDerivAt_zero htc (hf.mono (hsub ht hc))
      (fun r hr => hzero r ⟨ht.1.trans hr.1, hr.2.trans hc.2⟩
        hr.2.ne (hr.2.trans_le hcd).ne)).symm
  · by_cases hdt : d ≤ t
    · exact (endpoint_eq_of_hasDerivAt_zero hdt (hf.mono (hsub hd ht))
        (fun r hr => hzero r ⟨hd.1.trans hr.1, hr.2.trans ht.2⟩
          (hcd.trans_lt hr.1).ne' hr.1.ne')).trans hmiddle
    · have hct : c < t := lt_of_not_ge htc
      have htd : t < d := lt_of_not_ge hdt
      exact endpoint_eq_of_hasDerivAt_zero hct.le (hf.mono (hsub hc ht))
        (fun r hr => hzero r ⟨hc.1.trans hr.1, hr.2.trans ht.2⟩
          hr.1.ne' (hr.2.trans htd).ne)

/-- Vanishing actual derivative off the two radii makes the open-interval
function constant, with no prescribed endpoint values. -/
theorem exists_constant_of_hasDerivAt_zero_off_pair
    {f : ℝ → ℝ} {a b c d : ℝ} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b)
    (hf : ContinuousOn f (Ioo a b))
    (hzero : ∀ t ∈ Ioo a b, t ≠ c → t ≠ d → HasDerivAt f 0 t) :
    ∃ v : ℝ, EqOn f (fun _ => v) (Ioo a b) := by
  rcases le_total c d with hcd | hdc
  · exact ⟨f c, eqOn_constant_of_hasDerivAt_zero_off_ordered_pair hc hd hcd hf hzero⟩
  · exact ⟨f d, eqOn_constant_of_hasDerivAt_zero_off_ordered_pair hd hc hdc hf
      (fun t ht htd htc => hzero t ht htc htd)⟩

/-- The two actual one-sided limits agree. The values of `f` at the two
endpoints are deliberately absent from the hypotheses and conclusion. -/
theorem endpoint_traces_eq_of_hasDerivAt_zero_off_pair
    {f : ℝ → ℝ} {a b c d A B : ℝ} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b)
    (hf : ContinuousOn f (Ioo a b))
    (hzero : ∀ t ∈ Ioo a b, t ≠ c → t ≠ d → HasDerivAt f 0 t)
    (hleft : Tendsto f (𝓝[Ioo a b] a) (𝓝 A))
    (hright : Tendsto f (𝓝[Ioo a b] b) (𝓝 B)) : B = A := by
  obtain ⟨v, he⟩ := exists_constant_of_hasDerivAt_zero_off_pair hc hd hf hzero
  have hab : a < b := hc.1.trans hc.2
  have hca : a ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨le_rfl, hab.le⟩
  have hcb : b ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  haveI : NeBot (𝓝[Ioo a b] a) := mem_closure_iff_nhdsWithin_neBot.mp hca
  haveI : NeBot (𝓝[Ioo a b] b) := mem_closure_iff_nhdsWithin_neBot.mp hcb
  have hA : A = v := tendsto_nhds_unique_of_eventuallyEq hleft tendsto_const_nhds
    (he.eventuallyEq_of_mem self_mem_nhdsWithin)
  have hB : B = v := tendsto_nhds_unique_of_eventuallyEq hright tendsto_const_nhds
    (he.eventuallyEq_of_mem self_mem_nhdsWithin)
  exact hB.trans hA.symm

end ContinuousFlexibility.Analysis
