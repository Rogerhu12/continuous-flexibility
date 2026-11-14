module

public import ContinuousFlexibility.Analysis.N07aClosedRectangleJets
public import ContinuousFlexibility.Analysis.N07aNormalRecurrence

/-!
# Transmission of genuine closed jets across a noncharacteristic interface

The equation is used only on the two open halves. Its differentiated
identities extend to the interface through continuity of the actual
within Taylor jets. Equality of the value and first differential then
determines every normal jet, while angular differentiation determines
the mixed jets. No smooth extension of either solution is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

namespace N07aClosedRectangleJets

/-- The radial Leibniz expansion, with the solution jets supplied explicitly. -/
def normalRhs (A : Fin 6 → PolarPoint → ℝ) (f : PolarPoint → ℝ)
    (J : ℕ → ℕ → PolarPoint → ℝ) (n : ℕ) (x : PolarPoint) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), ∑ i : Fin 5,
    n07aNormalBinomial n 0 k 0 * mixedDerivative k 0 (A i.castSucc) x *
      J (n - k + (n07aNormalShift i).1) (n07aNormalShift i).2 x) +
    ∑ k ∈ Finset.range (n + 1),
      n07aNormalBinomial n 0 k 0 * mixedDerivative k 0 (A 5) x *
        mixedDerivative (n - k) 0 f x

theorem normalRhs_congr {A : Fin 6 → PolarPoint → ℝ} {f : PolarPoint → ℝ}
    {J K : ℕ → ℕ → PolarPoint → ℝ} {n : ℕ} {x : PolarPoint}
    (h : ∀ i < n + 2, ∀ j, J i j x = K i j x) :
    normalRhs A f J n x = normalRhs A f K n x := by
  unfold normalRhs
  apply congrArg₂ (· + ·) _ rfl
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [h (n - k + (n07aNormalShift i).1)
    (by have := n07aNormalShift_radial_le i; omega) (n07aNormalShift i).2]

/-- Radially differentiated equations hold for the true one-sided jets
at all closed-rectangle points where the coefficients and source are smooth. -/
theorem normal_recursion {l r a b : ℝ} (hlr : l < r) (hab : a < b)
    {O : Set PolarPoint} (hO : IsOpen O) (hsub : openRect l r a b ⊆ O)
    {A : Fin 6 → PolarPoint → ℝ} {u f : PolarPoint → ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) O)
    (hu : ContDiffOn ℝ ∞ u (closedRect l r a b))
    (hf : ContDiffOn ℝ ∞ f O)
    (heq : EqOn (mixedDerivative 2 0 u) (n07aNormalRhs A u f) (openRect l r a b))
    (n : ℕ) {x : PolarPoint} (hx : x ∈ closedRect l r a b) (hxO : x ∈ O) :
    mixed l r a b u (n + 2) 0 x = normalRhs A f (mixed l r a b u) n x := by
  classical
  let Q := closedRect l r a b ∩ O
  have hopen : IsOpen (openRect l r a b) := isOpen_Ioo.prod isOpen_Ioo
  have huopen := hu.mono (open_subset_closed l r a b)
  have he : EqOn (mixed l r a b u (n + 2) 0)
      (normalRhs A f (mixed l r a b u) n) (openRect l r a b) := by
    intro p hp
    have hrec := n07a_normal_mixed_recursion hopen (fun i => (hA i).mono hsub)
      huopen (hf.mono hsub) heq n 0 hp
    simp only [Nat.zero_add, Nat.zero_sub, Finset.sum_range_one] at hrec
    rw [mixed_agrees hlr hab hu _ _ hp]
    refine hrec.trans ?_
    unfold normalRhs
    apply congrArg₂ (· + ·) _ rfl
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    rw [mixed_agrees hlr hab hu _ _ hp]
  have hleft : ContinuousOn (mixed l r a b u (n + 2) 0) Q :=
    (continuousOn_mixed hlr hab hu _ _).mono inter_subset_left
  have hcoeff (k : ℕ) (i : Fin 6) : ContinuousOn (mixedDerivative k 0 (A i)) Q :=
    (contDiffOn_mixedDerivative hO (hA i) k 0).continuousOn.mono inter_subset_right
  have hsource (k : ℕ) : ContinuousOn (mixedDerivative k 0 f) Q :=
    (contDiffOn_mixedDerivative hO hf k 0).continuousOn.mono inter_subset_right
  have hjet (i j : ℕ) : ContinuousOn (mixed l r a b u i j) Q :=
    (continuousOn_mixed hlr hab hu i j).mono inter_subset_left
  have hright : ContinuousOn (normalRhs A f (mixed l r a b u) n) Q := by
    unfold normalRhs
    apply ContinuousOn.add
    · apply continuousOn_finsetSum (Finset.range (n + 1))
      intro k _
      apply continuousOn_finsetSum Finset.univ
      intro i _
      exact (continuousOn_const.mul (hcoeff k i.castSucc)).mul (hjet _ _)
    · apply continuousOn_finsetSum (Finset.range (n + 1))
      intro k _
      exact (continuousOn_const.mul (hcoeff k 5)).mul (hsource (n - k))
  have hSQ : openRect l r a b ⊆ Q :=
    fun p hp => ⟨open_subset_closed l r a b hp, hsub hp⟩
  have hQS : Q ⊆ closure (openRect l r a b) := by
    rw [closure_openRect hlr hab]
    exact inter_subset_left
  exact he.of_subset_closure hleft hright hSQ hQS ⟨hx, hxO⟩

/-- Equality of one normal trace gives equality of all its angular jets.
The trace derivatives come from each side's own closed Taylor series. -/
theorem angular_trace_eq {l c r a b : ℝ} (hlc : l < c) (hcr : c < r)
    (hab : a < b) {u v : PolarPoint → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedRect l c a b))
    (hv : ContDiffOn ℝ ∞ v (closedRect c r a b)) (i : ℕ)
    (hzero : ∀ θ ∈ Ioo a b, mixed l c a b u i 0 (c, θ) =
      mixed c r a b v i 0 (c, θ)) :
    ∀ j, ∀ θ ∈ Ioo a b, mixed l c a b u i j (c, θ) =
      mixed c r a b v i j (c, θ) := by
  intro j
  induction j with
  | zero => exact hzero
  | succ j ih =>
    intro θ hθ
    have hdu := mixed_angular_hasDerivAt hlc hab hu i j ⟨hlc.le, le_rfl⟩ hθ
    have hdv := mixed_angular_hasDerivAt hcr hab hv i j ⟨le_rfl, hcr.le⟩ hθ
    have he : (fun s => mixed c r a b v i j (c, s)) =ᶠ[𝓝 θ]
        (fun s => mixed l c a b u i j (c, s)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
      exact (ih s hs).symm
    exact (hdu.congr_of_eventuallyEq he).unique hdv

end N07aClosedRectangleJets

open N07aClosedRectangleJets

/-- A common smooth normalized second-order equation transmits all true
closed Taylor jets from matching value and first differential traces. -/
theorem n07a_closedRectangle_normalTransmission_matching_jets
    {l c r a b : ℝ} (hlc : l < c) (hcr : c < r) (hab : a < b)
    {A : Fin 6 → PolarPoint → ℝ} {u v f : PolarPoint → ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (Ioo l r ×ˢ Ioo a b))
    (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ Ioo a b))
    (hu : ContDiffOn ℝ ∞ u (Icc l c ×ˢ Icc a b))
    (hv : ContDiffOn ℝ ∞ v (Icc c r ×ˢ Icc a b))
    (hequ : EqOn (mixedDerivative 2 0 u) (n07aNormalRhs A u f)
      (Ioo l c ×ˢ Ioo a b))
    (heqv : EqOn (mixedDerivative 2 0 v) (n07aNormalRhs A v f)
      (Ioo c r ×ˢ Ioo a b))
    (hvalue : ∀ θ ∈ Ioo a b, u (c, θ) = v (c, θ))
    (hfirst : ∀ θ ∈ Ioo a b,
      fderivWithin ℝ u (Icc l c ×ˢ Icc a b) (c, θ) =
        fderivWithin ℝ v (Icc c r ×ˢ Icc a b) (c, θ)) :
    ∀ n : ℕ, ∀ θ ∈ Ioo a b,
      iteratedFDerivWithin ℝ n u (Icc l c ×ˢ Icc a b) (c, θ) =
        iteratedFDerivWithin ℝ n v (Icc c r ×ˢ Icc a b) (c, θ) := by
  have hmixed : ∀ i j, ∀ θ ∈ Ioo a b,
      mixed l c a b u i j (c, θ) = mixed c r a b v i j (c, θ) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      apply angular_trace_eq hlc hcr hab hu hv i
      intro θ hθ
      have hleft : (c, θ) ∈ closedRect l c a b :=
        ⟨⟨hlc.le, le_rfl⟩, Ioo_subset_Icc_self hθ⟩
      have hright : (c, θ) ∈ closedRect c r a b :=
        ⟨⟨le_rfl, hcr.le⟩, Ioo_subset_Icc_self hθ⟩
      rcases i with _ | i
      · simpa only [mixed_zero] using hvalue θ hθ
      rcases i with _ | i
      · rw [mixed_one_radial hlc hab hleft, mixed_one_radial hcr hab hright]
        exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) (hfirst θ hθ)
      · have hO : IsOpen (Ioo l r ×ˢ Ioo a b) := isOpen_Ioo.prod isOpen_Ioo
        have hsubleft : openRect l c a b ⊆ Ioo l r ×ˢ Ioo a b :=
          fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hcr⟩, hp.2⟩
        have hsubright : openRect c r a b ⊆ Ioo l r ×ˢ Ioo a b :=
          fun p hp => ⟨⟨hlc.trans hp.1.1, hp.1.2⟩, hp.2⟩
        have hxO : (c, θ) ∈ Ioo l r ×ˢ Ioo a b := ⟨⟨hlc, hcr⟩, hθ⟩
        change mixed l c a b u (i + 2) 0 (c, θ) = mixed c r a b v (i + 2) 0 (c, θ)
        rw [normal_recursion hlc hab hO hsubleft hA hu hf hequ i hleft hxO,
          normal_recursion hcr hab hO hsubright hA hv hf heqv i hright hxO]
        apply normalRhs_congr
        intro k hk j
        exact ih k hk j θ hθ
  intro n θ hθ
  apply N07aClosedRectangleJets.multilinear_ext_coordinate_words
  intro w
  have hleft := N07aClosedRectangleJets.word_eq_mixed hlc hab hu n w (p := (c, θ))
    ⟨⟨hlc.le, le_rfl⟩, Ioo_subset_Icc_self hθ⟩
  have hright := N07aClosedRectangleJets.word_eq_mixed hcr hab hv n w (p := (c, θ))
    ⟨⟨le_rfl, hcr.le⟩, Ioo_subset_Icc_self hθ⟩
  exact hleft.trans ((hmixed _ _ θ hθ).trans hright.symm)

end ContinuousFlexibility.Analysis
