import ContinuousFlexibility.Analysis.RootChartExtension
import ContinuousFlexibility.Analysis.RootCompositionBounds

/-!
# Ordinary bounds for the genuine extended root coordinates

The raw root formulas have the finite-order bounds already proved by the
root-composition theorem. On the open physical half-plane they agree with
the genuine smooth extensions. Continuity of the ordinary derivatives of
those extensions gives the same bounds at the root. No derivative of a
totalized, nonsmooth formula at the root is used for this passage.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A bound for genuine ordinary derivatives on an open radial strip
passes to both radial endpoints by continuity. The angular set is arbitrary. -/
theorem csBound_closedRadialStrip_of_open
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b M : ℝ} (hab : a < b) {K : Set ℝ} {s : ℕ}
    (hbound : CSBound s (Ioo a b ×ˢ K) f M) :
    CSBound s (Icc a b ×ˢ K) f M := by
  intro n hn p hp
  have hclosed : IsClosed {q : PolarPoint | ‖iteratedFDeriv ℝ n f q‖ ≤ M} :=
    isClosed_le (hf.continuous_iteratedFDeriv (by simp)).norm continuous_const
  have hsub : Ioo a b ×ˢ K ⊆
      {q : PolarPoint | ‖iteratedFDeriv ℝ n f q‖ ≤ M} :=
    fun q hq => hbound n hn q hq
  have hclosure : p ∈ closure (Ioo a b ×ˢ K) := by
    rw [closure_prod_eq, closure_Ioo hab.ne]
    exact ⟨hp.1, subset_closure hp.2⟩
  exact closure_minimal hsub hclosed hclosure

local notation "sourceBox" =>
  Set.prod (Icc (0 : ℝ) 1) (Set.prod (Icc (-1 : ℝ) 1) (Icc (-Real.pi) Real.pi))
local notation "targetBox" => Set.prod (Icc (0 : ℝ) 1) (Icc (-Real.pi) Real.pi)

/-- The actual smooth angular extension preserves the finite input order,
including its genuine ordinary derivatives at the root. -/
theorem exists_csBound_extendedRootEven (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
      ∀ T : ℝ, T ≠ 0 →
      (∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T) →
      ∀ M : ℝ, CSBound s sourceBox G M →
        CSBound s targetBox (extendedRootEven G) (C * M) := by
  obtain ⟨C, hC, hraw⟩ := exists_csBound_rootEven s
  refine ⟨C, hC, ?_⟩
  intro G hG T hT hperiod M hbound
  apply csBound_closedRadialStrip_of_open
    (contDiff_extendedRootEven hG hT hperiod) zero_lt_one
  intro n hn p hp
  have he : EqOn (extendedRootEven G) (rootEven G)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    fun q hq => extendedRootEven_of_nonneg G hq.1.le
  rw [iteratedFDeriv_eqOn_of_isOpen (isOpen_Ioi.prod isOpen_univ)
    he n (show p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hp.1.1, mem_univ _⟩)]
  exact hraw G hG M hbound n hn p ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩

/-- The actual smooth odd-coefficient extension loses exactly one input
derivative, with the same constant before all inputs and periods. -/
theorem exists_csBound_extendedRootOddCoefficient (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
      ∀ T : ℝ, T ≠ 0 →
      (∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T) →
      ∀ M : ℝ, CSBound (s + 1) sourceBox G M →
        CSBound s targetBox (extendedRootOddCoefficient G) (C * M) := by
  obtain ⟨C, hC, hraw⟩ := exists_rootComposition_csBound s
  refine ⟨C, hC, ?_⟩
  intro G hG T hT hperiod M hbound
  apply csBound_closedRadialStrip_of_open
    (contDiff_extendedRootOddCoefficient hG hT hperiod) zero_lt_one
  intro n hn p hp
  have he : EqOn (extendedRootOddCoefficient G) (fun q => -rootOdd G q)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    fun q hq => extendedRootOddCoefficient_of_nonneg G hq.1.le
  rw [iteratedFDeriv_eqOn_of_isOpen (isOpen_Ioi.prod isOpen_univ)
    he n (show p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hp.1.1, mem_univ _⟩)]
  have hneg : (fun q : PolarPoint => -rootOdd G q) = -rootOdd G := by
    funext q
    exact (Pi.neg_apply (rootOdd G) q).symm
  rw [hneg, iteratedFDeriv_neg_apply, norm_neg]
  exact (hraw G hG M).2 hbound n hn p ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩

/-- Comparing two genuine smooth extensions retains the input difference.
The same finite-order constants work for every pair of root flows. -/
theorem exists_csBound_extendedRoot_differences (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G G₀ : ℝ × ℝ × ℝ → ℝ,
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ G₀ → ∀ T : ℝ, T ≠ 0 →
      (∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T) →
      (∀ r, 0 ≤ r → ∀ θ, rootEven G₀ (r, θ + T) = rootEven G₀ (r, θ) + T) →
      (∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T) →
      (∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G₀ (r, θ)) T) →
      ∀ M : ℝ,
        (CSBound s sourceBox (fun q => G q - G₀ q) M →
          CSBound s targetBox
            (fun p => extendedRootEven G p - extendedRootEven G₀ p) (C * M)) ∧
        (CSBound (s + 1) sourceBox (fun q => G q - G₀ q) M →
          CSBound s targetBox
            (fun p => extendedRootOddCoefficient G p - extendedRootOddCoefficient G₀ p)
            (C * M)) := by
  obtain ⟨C, hC, hraw⟩ := exists_rootComposition_csBound s
  refine ⟨C, hC, ?_⟩
  intro G G₀ hG hG₀ T hT hφ hφ₀ hχ hχ₀ M
  constructor
  · intro hbound
    apply csBound_closedRadialStrip_of_open
      ((contDiff_extendedRootEven hG hT hφ).sub
        (contDiff_extendedRootEven hG₀ hT hφ₀)) zero_lt_one
    intro n hn p hp
    have he : EqOn
        (fun q => extendedRootEven G q - extendedRootEven G₀ q)
        (rootEven (fun q => G q - G₀ q))
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
      intro q hq
      change extendedRootEven G q - extendedRootEven G₀ q =
        rootEven (fun q => G q - G₀ q) q
      rw [extendedRootEven_of_nonneg G hq.1.le,
        extendedRootEven_of_nonneg G₀ hq.1.le]
      unfold rootEven
      ring
    rw [iteratedFDeriv_eqOn_of_isOpen (isOpen_Ioi.prod isOpen_univ)
      he n (show p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hp.1.1, mem_univ _⟩)]
    exact (hraw _ (hG.sub hG₀) M).1 hbound n hn p
      ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩
  · intro hbound
    apply csBound_closedRadialStrip_of_open
      ((contDiff_extendedRootOddCoefficient hG hT hχ).sub
        (contDiff_extendedRootOddCoefficient hG₀ hT hχ₀)) zero_lt_one
    intro n hn p hp
    have he : EqOn
        (fun q => extendedRootOddCoefficient G q - extendedRootOddCoefficient G₀ q)
        (fun q => -rootOdd (fun y => G y - G₀ y) q)
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
      intro q hq
      change extendedRootOddCoefficient G q - extendedRootOddCoefficient G₀ q =
        -rootOdd (fun y => G y - G₀ y) q
      rw [extendedRootOddCoefficient_of_nonneg G hq.1.le,
        extendedRootOddCoefficient_of_nonneg G₀ hq.1.le]
      simp only [rootOddCoefficient, rootOdd, if_neg hq.1.ne']
      ring
    rw [iteratedFDeriv_eqOn_of_isOpen (isOpen_Ioi.prod isOpen_univ)
      he n (show p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hp.1.1, mem_univ _⟩)]
    have hneg : (fun q : PolarPoint => -rootOdd (fun y => G y - G₀ y) q) =
        -rootOdd (fun y => G y - G₀ y) := by
      funext q
      exact (Pi.neg_apply (rootOdd (fun y => G y - G₀ y)) q).symm
    rw [hneg, iteratedFDeriv_neg_apply, norm_neg]
    exact (hraw _ (hG.sub hG₀) M).2 hbound n hn p
      ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩

end ContinuousFlexibility.Analysis
