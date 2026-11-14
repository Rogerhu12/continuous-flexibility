module

public import ContinuousFlexibility.Radial.HeightSelectionPrinciple
public import ContinuousFlexibility.Radial.MorseHeightAngleExclusion

/-!
# All matching angles at once

This is `lem:radial-product-selection` (manuscript §5) with its analytic inputs
isolated as hypotheses about three families of functions on the cube of height
ratios.  Condition `k` (an endpoint, a transition cell and a frequency in its
band) is attached to the coordinate `c k`.

* `Y k σ` is the true incoming state at the outer end of the selected join, in
  the common frame of `eq:rad-eq-js7`.  It lies within `η k` of the ideal state
  `(1, a k σ)`, whose slope is in `[-3/2, -1/2]` (`eq:rad-eq-js6`) and does not
  depend on the coordinate `c k`.
* `B k σ` spans the natural endpoint line in its local frame, and `Ξ k σ` is
  the height contrast (`eq:rad-eq-js4`).  Neither depends on the coordinate
  `c k`; the common-frame state is `(B₁, σ_{c k} Ξ B₂)`.
* Both states are continuous on the cube for the product topology.

The conclusion selects one sequence of heights for which every angle sine is
at least `δ k`.  The public angle is `Statements.radialAngleSine`, the one used
in `Statements.IsSelectedTail`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Function MeasureTheory Real
open scoped ENNReal Topology

private theorem sqrt_sq_add_sq_ne_zero {v : ℝ × ℝ} (hv : v ≠ (0, 0)) :
    sqrt (v.1 ^ 2 + v.2 ^ 2) ≠ 0 := by
  refine (sqrt_pos.mpr ?_).ne'
  by_cases h₁ : v.1 = 0
  · have h₂ : v.2 ≠ 0 := fun hz => hv (Prod.ext h₁ hz)
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h₂)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h₁) (sq_nonneg _)

private theorem outerState_ne_zero {Ξ σ : ℝ} {B : ℝ × ℝ}
    (hΞ : 0 < Ξ) (hσ : σ ∈ Icc (1 : ℝ) 2) (hB : B ≠ (0, 0)) :
    morseHeightOuterState Ξ σ B ≠ (0, 0) := by
  intro h
  have h₁ : B.1 = 0 := congrArg Prod.fst h
  have h₂ : σ * Ξ * B.2 = 0 := congrArg Prod.snd h
  exact hB (Prod.ext h₁ ((mul_eq_zero.mp h₂).resolve_left
    (mul_ne_zero (zero_lt_one.trans_le hσ.1).ne' hΞ.ne')))

/-- The angle sine is continuous along continuous families of nonzero states. -/
private theorem continuousOn_radialAngleSine {X : Type*} [TopologicalSpace X] {s : Set X}
    {P Q : X → ℝ × ℝ} (hP : ContinuousOn P s) (hQ : ContinuousOn Q s)
    (hP₀ : ∀ x ∈ s, P x ≠ (0, 0)) (hQ₀ : ∀ x ∈ s, Q x ≠ (0, 0)) :
    ContinuousOn (fun x => Statements.radialAngleSine (P x) (Q x)) s := by
  have hP₁ : ContinuousOn (fun x => (P x).1) s := continuous_fst.comp_continuousOn hP
  have hP₂ : ContinuousOn (fun x => (P x).2) s := continuous_snd.comp_continuousOn hP
  have hQ₁ : ContinuousOn (fun x => (Q x).1) s := continuous_fst.comp_continuousOn hQ
  have hQ₂ : ContinuousOn (fun x => (Q x).2) s := continuous_snd.comp_continuousOn hQ
  have hnum : ContinuousOn (fun x => |(P x).1 * (Q x).2 - (P x).2 * (Q x).1|) s :=
    ((hP₁.mul hQ₂).sub (hP₂.mul hQ₁)).abs
  have hden : ContinuousOn (fun x => sqrt ((P x).1 ^ 2 + (P x).2 ^ 2) *
      sqrt ((Q x).1 ^ 2 + (Q x).2 ^ 2)) s :=
    (continuous_sqrt.comp_continuousOn ((hP₁.pow 2).add (hP₂.pow 2))).mul
      (continuous_sqrt.comp_continuousOn ((hQ₁.pow 2).add (hQ₂.pow 2)))
  exact hnum.div hden fun x hx =>
    mul_ne_zero (sqrt_sq_add_sq_ne_zero (hP₀ x hx)) (sqrt_sq_add_sq_ne_zero (hQ₀ x hx))

/-- **Simultaneous height selection, abstract form.**  One sequence of height
ratios keeps every incoming state at angle sine at least `δ k` from the
corresponding natural endpoint line. -/
theorem exists_heights_all_angles_separated {κ : Type*} [Countable κ]
    (c : κ → ℕ) (δ η : κ → ℝ)
    (a Ξ : κ → (ℕ → ℝ) → ℝ) (Y B : κ → (ℕ → ℝ) → ℝ × ℝ)
    (hδ : ∀ k, 0 < δ k ∧ δ k ≤ 1 / 48)
    (hη : ∀ k, 0 ≤ η k ∧ η k ≤ δ k / 4)
    (ha : ∀ k, ∀ σ ∈ heightCube, a k σ ∈ Icc (-(3 : ℝ) / 2) (-1 / 2))
    (hΞ : ∀ k, ∀ σ ∈ heightCube, 0 < Ξ k σ)
    (hB : ∀ k, ∀ σ ∈ heightCube, B k σ ≠ (0, 0))
    (hY : ∀ k, ∀ σ ∈ heightCube, |(Y k σ).1 - 1| ≤ η k ∧ |(Y k σ).2 - a k σ| ≤ η k)
    (ha_indep : ∀ k, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      a k (update σ (c k) t) = a k σ)
    (hΞ_indep : ∀ k, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      Ξ k (update σ (c k) t) = Ξ k σ)
    (hB_indep : ∀ k, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      B k (update σ (c k) t) = B k σ)
    (hYcont : ∀ k, ContinuousOn (Y k) heightCube)
    (hΞcont : ∀ k, ContinuousOn (Ξ k) heightCube)
    (hBcont : ∀ k, ContinuousOn (B k) heightCube)
    (hsum : ∑' k, ENNReal.ofReal (192 * δ k) < 1) :
    ∃ σ ∈ heightCube, ∀ k,
      δ k ≤ Statements.radialAngleSine (Y k σ)
        (morseHeightOuterState (Ξ k σ) (σ (c k)) (B k σ)) := by
  let g : κ → (ℕ → ℝ) → ℝ := fun k σ =>
    Statements.radialAngleSine (Y k σ) (morseHeightOuterState (Ξ k σ) (σ (c k)) (B k σ))
  have hYne : ∀ k, ∀ σ ∈ heightCube, Y k σ ≠ (0, 0) := by
    intro k σ hσ h
    have h₁ : (Y k σ).1 = 0 := congrArg Prod.fst h
    have hn := (abs_le.mp (hY k σ hσ).1).1
    rw [h₁, zero_sub] at hn
    linarith only [hn, (hη k).2, (hδ k).2]
  have hgcont : ∀ k, ContinuousOn (g k) heightCube := by
    intro k
    have hcoord : ContinuousOn (fun σ : ℕ → ℝ => σ (c k)) heightCube :=
      (continuous_apply (c k)).continuousOn
    have hB₁ : ContinuousOn (fun σ => (B k σ).1) heightCube :=
      continuous_fst.comp_continuousOn (hBcont k)
    have hB₂ : ContinuousOn (fun σ => (B k σ).2) heightCube :=
      continuous_snd.comp_continuousOn (hBcont k)
    have hQ : ContinuousOn
        (fun σ => morseHeightOuterState (Ξ k σ) (σ (c k)) (B k σ)) heightCube :=
      hB₁.prodMk ((hcoord.mul (hΞcont k)).mul hB₂)
    exact continuousOn_radialAngleSine (hYcont k) hQ (hYne k) fun σ hσ =>
      outerState_ne_zero (hΞ k σ hσ) (mem_heightCube.mp hσ (c k)) (hB k σ hσ)
  obtain ⟨σ, hσ, hgood⟩ := exists_simultaneous_selection c
    (fun k => {σ | g k σ < δ k}) (fun k => ENNReal.ofReal (192 * δ k))
    (fun k => by
      have hset : heightCube \ {σ | g k σ < δ k} = heightCube ∩ g k ⁻¹' Ici (δ k) := by
        ext σ
        refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
        · have h2 : ¬ g k σ < δ k := h.2
          exact not_lt.mp h2
        · have h2 : δ k ≤ g k σ := h.2
          intro hlt
          have hlt' : g k σ < δ k := hlt
          exact (not_lt.mpr h2) hlt'
      rw [hset]
      exact (hgcont k).preimage_isClosed_of_isClosed isClosed_heightCube isClosed_Ici)
    (fun k σ hσ => by
      refine (measure_mono ?_).trans (morseHeightAngle_true_bad_measure_le
        (Y := fun t => Y k (update σ (c k) t)) (ha k σ hσ) (hΞ k σ hσ) (hB k σ hσ)
        (hδ k).1 (hδ k).2 (hη k).1 (hη k).2 fun t ht => by
          have h := hY k _ (update_mem_heightCube hσ (c k) ht)
          rwa [ha_indep k σ hσ t ht] at h)
      rintro t ⟨ht, hbad⟩
      refine ⟨ht, ?_⟩
      have hbad' : g k (update σ (c k) t) < δ k := hbad
      simpa only [g, hΞ_indep k σ hσ t ht, hB_indep k σ hσ t ht, update_self] using hbad')
    hsum
  exact ⟨σ, hσ, fun k => not_lt.mp (hgood k)⟩

end ContinuousFlexibility.Radial
