module

public import ContinuousFlexibility.Radial.MorseNegativeCover

/-!
# The actual labeled negative components of a retained Morse tail

The existence statement keeps the starting index and the exact turning
endpoints.  In particular the label is the label of the model containing
the point, before any control enumeration or material sample is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

/-- Every negative tail point is in the explicit turning component of
a model whose label is at least the chosen start.  The component remains
strictly beyond the same positive entrance. -/
theorem n01c_morse_negative_tail_model_component
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {N : ℕ} (hN : T.index ≤ N) {r : ℝ}
    (hr : r ∈ radialTailInterval D side (morseChainSeam T side N))
    (hneg : deriv D.w r < 0) :
    ∃ n : ℕ, N ≤ n ∧
      r ∈ Ioo
        (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
        (T.radius side n (morseChainRightTurn T n)) ∧
      Icc
        (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
        (T.radius side n (morseChainRightTurn T n)) ⊆
          radialTailInterval D side (morseChainSeam T side N) := by
  obtain ⟨n, hNn, x, hx, rfl⟩ :=
    morseRealization_negative_tail_model_from_start hreal side hN hr hneg
  have hn : T.index ≤ n := hN.trans hNn
  have hxin := (morseRealization_negative_at_radius_iff hreal hσ side hn hx).mp hneg
  obtain ⟨hleft, hab, hright⟩ := morseRealization_turns_retained hreal side hn
  have hsub := Icc_subset_Icc hleft.le hright.le
  have ha := hsub (left_mem_Icc.mpr hab.le)
  have hb := hsub (right_mem_Icc.mpr hab.le)
  have hm := hreal.radius_strictMonoOn side n hn
  have hrI := And.intro (hm ha hx hxin.1) (hm hx hb hxin.2)
  have hcomponent := (morseRealization_model_return hreal hσ side hn).1
  refine ⟨n, hNn, hrI, ?_⟩
  exact negativeRadialComponent_closed_subset_tail hcomponent hrI hr
    (morseRealization_seam_deriv_pos hreal hσ side hN)

end ContinuousFlexibility.Radial
