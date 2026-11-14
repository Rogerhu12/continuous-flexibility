module

public import ContinuousFlexibility.Analysis.N05SeedOpticalLowerTransport

/-!
# Exhaustion of the actual seed's negative components

The pointwise three-piece construction and uniqueness of a negative
component identify its whole interval with one retained Morse interval
or the retained central interval. No new enumeration is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Real
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {q : ℝ} (P : SeedReferenceConstruction q)

theorem n05_tail_component (side : Bool) {l h : ℝ}
    (hcomponent : NegativeRadialComponent (P.selected.family P.selected.sigma) l h)
    (hclosed : Icc l h ⊆ radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index)) :
    NegativeRadialComponent P.reference (P.n05TailScale side * l)
      (P.n05TailScale side * h) := by
  have hscale := P.n05TailScale_pos side
  have hheight : 0 < (if side then P.glued.heightR else P.glued.heightL) := by
    cases side
    · exact P.glued.heightL_pos
    · exact P.glued.heightR_pos
  have hlh := hcomponent.2.1
  have hl := P.n05_tail_scaled_mem_core side (hclosed (left_mem_Icc.mpr hlh.le))
  have hh := P.n05_tail_scaled_mem_core side (hclosed (right_mem_Icc.mpr hlh.le))
  have htail : radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index) =
      Ioo (if side then P.selected.entry side P.selected.chain.index
        else (P.selected.family P.selected.sigma).a)
        (if side then (P.selected.family P.selected.sigma).b
        else P.selected.entry side P.selected.chain.index) := by
    cases side <;> rfl
  exact (negativeRadialComponent_travel_of_tail_identity hscale hheight hcomponent
    hl.1 hh.2 P.realization.geometry.2.2.1.1 P.accumulating.choose_spec.1.2.2.1.1
    (by simpa only [htail] using hclosed)
    (by
      intro r hr
      exact P.tail_profile side (by simpa only [htail] using hr))).1

/-- A negative point on either retained tail determines a complete model
component whose closure remains inside that same tail. -/
theorem n05_tail_negative_point (side : Bool) {r : ℝ}
    (hr : r ∈ radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index))
    (hneg : deriv (P.selected.family P.selected.sigma).w r < 0) :
    ∃ n : ℕ, P.selected.chain.index ≤ n ∧
      r ∈ Ioo (P.n05ModelLeft side n) (P.n05ModelRight side n) ∧
      Icc (P.n05ModelLeft side n) (P.n05ModelRight side n) ⊆
        radialTailInterval (P.selected.family P.selected.sigma) side
          (P.selected.entry side P.selected.chain.index) := by
  have hrseam : r ∈ radialTailInterval (P.selected.family P.selected.sigma) side
      (morseChainSeam P.selected.chain side P.retainedIndex) := by
    simpa only [P.entry_seam side] using hr
  obtain ⟨n, hn, x, hx, rfl⟩ := morseRealization_negative_tail_model P.realization side
    P.retainedIndex_ge hrseam hneg
  have hxin := (morseRealization_negative_at_radius_iff P.realization
    P.selected_spec.2.2.1 side hn hx).mp hneg
  obtain ⟨hleft, hab, hright⟩ := morseRealization_turns_retained P.realization side hn
  have hsub := Icc_subset_Icc hleft.le hright.le
  have ha := hsub (left_mem_Icc.mpr hab.le)
  have hb := hsub (right_mem_Icc.mpr hab.le)
  have hm := P.realization.radius_strictMonoOn side n hn
  have hmem : P.selected.chain.radius side n x ∈
      Ioo (P.n05ModelLeft side n) (P.n05ModelRight side n) :=
    ⟨hm ha hx hxin.1, hm hx hb hxin.2⟩
  have hentry : 0 < deriv (P.selected.family P.selected.sigma).w
      (P.selected.entry side P.selected.chain.index) := by
    rw [P.entry_seam side]
    exact morseRealization_seam_deriv_pos P.realization P.selected_spec.2.2.1 side
      P.retainedIndex_ge
  exact ⟨n, hn, hmem,
    negativeRadialComponent_closed_subset_tail (P.n05_model_component side hn) hmem hr hentry⟩

/-- The actual component endpoints, with the actual radius scaling. -/
theorem n05_component_cases (hq : 0 < q) {l h : ℝ}
    (hcomponent : NegativeRadialComponent P.reference l h) :
    (l = centralRadius (-sqrt centralOscillatorA) ∧
      h = centralRadius (sqrt centralOscillatorA)) ∨
    ∃ (side : Bool) (n : ℕ), P.selected.chain.index ≤ n ∧
      l = P.n05TailScale side * P.n05ModelLeft side n ∧
      h = P.n05TailScale side * P.n05ModelRight side n ∧
      Icc (P.n05ModelLeft side n) (P.n05ModelRight side n) ⊆
        radialTailInterval (P.selected.family P.selected.sigma) side
          (P.selected.entry side P.selected.chain.index) := by
  let r : ℝ := (l + h) / 2
  have hr : r ∈ Ioo l h := by
    dsimp only [r]
    constructor <;> linarith only [hcomponent.2.1]
  have hrCore : r ∈ radialCore P.reference :=
    ⟨hcomponent.1.trans hr.1, hr.2.trans hcomponent.2.2.1⟩
  have hrG : r ∈ Ioo (P.glued.radiusL * (P.selected.family P.selected.sigma).a)
      (P.glued.radiusR * (P.selected.family P.selected.sigma).b) := by
    simpa only [radialCore, mem_Ioo, P.left_endpoint, P.right_endpoint] using hrCore
  have hnegG : deriv P.glued.profile r < 0 := by
    simpa only [P.profile] using hcomponent.2.2.2.2.2 r hr
  have htail (side : Bool) (s : ℝ)
      (hs : s ∈ radialTailInterval (P.selected.family P.selected.sigma) side
        (P.selected.entry side P.selected.chain.index))
      (hrs : r = P.n05TailScale side * s)
      (hsneg : deriv (P.selected.family P.selected.sigma).w s < 0) :
      ∃ n : ℕ, P.selected.chain.index ≤ n ∧
        l = P.n05TailScale side * P.n05ModelLeft side n ∧
        h = P.n05TailScale side * P.n05ModelRight side n ∧
        Icc (P.n05ModelLeft side n) (P.n05ModelRight side n) ⊆
          radialTailInterval (P.selected.family P.selected.sigma) side
            (P.selected.entry side P.selected.chain.index) := by
    obtain ⟨n, hn, hsn, hclosed⟩ := P.n05_tail_negative_point side hs hsneg
    have hnew := P.n05_tail_component side (P.n05_model_component side hn) hclosed
    have hrnew : r ∈ Ioo (P.n05TailScale side * P.n05ModelLeft side n)
        (P.n05TailScale side * P.n05ModelRight side n) := by
      rw [hrs]
      exact ⟨mul_lt_mul_of_pos_left hsn.1 (P.n05TailScale_pos side),
        mul_lt_mul_of_pos_left hsn.2 (P.n05TailScale_pos side)⟩
    have he := negativeRadialComponent_unique_of_mem hcomponent hnew hr hrnew
    exact ⟨n, hn, he.1, he.2, hclosed⟩
  rcases P.glued.negative_deriv_cases hq hrG hnegG with hleft | hmiddle | hright
  · obtain ⟨s, hs, hrs, hsneg⟩ := hleft
    obtain ⟨n, hn, hl, hh, hclosed⟩ := htail false s hs hrs hsneg
    exact Or.inr ⟨false, n, hn, hl, hh, hclosed⟩
  · obtain ⟨hrMiddle, hnegCentral⟩ := hmiddle
    have hrpos : 0 < r := (exp_pos P.cutoff.left).trans hrMiddle.1
    have hx : centralModelCoordinate r ^ 2 < centralOscillatorA := by
      apply (centralRadialProfile_deriv_neg_iff (by norm_num : (0 : ℝ) < 1) _).mp
      rw [centralRadius_modelCoordinate hrpos]
      exact hnegCentral
    have hxI := sq_lt.mp hx
    have hrCentral : r ∈ Ioo (centralRadius (-sqrt centralOscillatorA))
        (centralRadius (sqrt centralOscillatorA)) :=
      ⟨(strictMono_centralRadius hxI.1).trans_eq (centralRadius_modelCoordinate hrpos),
        (centralRadius_modelCoordinate hrpos).symm.trans_lt
          (strictMono_centralRadius hxI.2)⟩
    have hcentral : NegativeRadialComponent P.reference
        (centralRadius (-sqrt centralOscillatorA))
        (centralRadius (sqrt centralOscillatorA)) := by
      simpa only [NegativeRadialComponent, P.left_endpoint, P.right_endpoint, P.profile]
        using (P.glued.central_model_return hq (P.entry_core false) (P.entry_core true)).1
    exact Or.inl (negativeRadialComponent_unique_of_mem hcomponent hcentral hr hrCentral)
  · obtain ⟨s, hs, hrs, hsneg⟩ := hright
    obtain ⟨n, hn, hl, hh, hclosed⟩ := htail true s hs hrs hsneg
    exact Or.inr ⟨true, n, hn, hl, hh, hclosed⟩

end ContinuousFlexibility.Radial.SeedReferenceConstruction
