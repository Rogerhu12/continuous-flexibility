module

public import ContinuousFlexibility.Analysis.N01cFullNeighborhood
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Uniform outer jets at the actual normalized denominators

The scalar reciprocal, reciprocal square root, and inverse three-halves
power are smooth near the fixed compact interval [1/2, 3/2]. Their
ordinary Frechet jets therefore have one uniform finite-order bound.
N01b places its actual Q/w and D arguments in this interval throughout
the full common state neighbourhood.

These are bounds for the outer scalar functions. The chain rule must
still include every spatial and parameter derivative of their actual
arguments; this module does not assume or assert those composed bounds.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

/-- Local smoothness at each point of a compact set bounds every actual
Frechet derivative through a specified finite order, including order zero. -/
theorem compact_iteratedFDeriv_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K : Set E} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, n ≤ s → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ n f x‖ ≤ B := by
  classical
  have hone (j : Fin (s + 1)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j.val f x‖ ≤ B := by
    have hc : ContinuousOn (fun x => ‖iteratedFDeriv ℝ j.val f x‖) K :=
      fun x hx => ((hf x hx).continuousAt_iteratedFDeriv (by simp)).norm.continuousWithinAt
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max 0 B, le_max_left _ _, fun x hx => ?_⟩
    have hb := hB x hx
    rw [Real.norm_of_nonneg (norm_nonneg _)] at hb
    exact hb.trans (le_max_right _ _)
  choose B hB hbound using hone
  let C : ℝ := 1 + ∑ j : Fin (s + 1), B j
  have hsum : 0 ≤ ∑ j : Fin (s + 1), B j :=
    Finset.sum_nonneg (fun j _ => hB j)
  refine ⟨C, add_pos_of_pos_of_nonneg zero_lt_one hsum, fun n hn x hx => ?_⟩
  let j : Fin (s + 1) := ⟨n, by omega⟩
  have hj : B j ≤ ∑ i : Fin (s + 1), B i :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ j)
  exact (hbound j x hx).trans
    (hj.trans (le_add_of_nonneg_left zero_le_one))

/-- The outer functions that occur in the normalized original coefficients
have uniformly bounded finite jets on the same fixed scalar interval. -/
theorem normalizedDenominator_outerJets_bound (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, n ≤ s →
      ∀ d ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
        ‖iteratedFDeriv ℝ n (fun x : ℝ => x⁻¹) d‖ ≤ B ∧
        ‖iteratedFDeriv ℝ n (fun x : ℝ => 1 / Real.sqrt x) d‖ ≤ B ∧
        ‖iteratedFDeriv ℝ n inverseDThreeHalves d‖ ≤ B := by
  have hpos (d : ℝ) (hd : d ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ)) : 0 < d :=
    lt_of_lt_of_le (by norm_num) hd.1
  have hinv (d : ℝ) (hd : d ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ)) :
      ContDiffAt ℝ ∞ (fun x : ℝ => x⁻¹) d :=
    contDiffAt_id.inv (hpos d hd).ne'
  have hsqrt (d : ℝ) (hd : d ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ)) :
      ContDiffAt ℝ ∞ (fun x : ℝ => 1 / Real.sqrt x) d :=
    contDiffAt_const.div (contDiffAt_id.sqrt (hpos d hd).ne')
      (Real.sqrt_pos.mpr (hpos d hd)).ne'
  have hthree (d : ℝ) (hd : d ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ)) :
      ContDiffAt ℝ ∞ inverseDThreeHalves d :=
    contDiffAt_const.div
      (contDiffAt_id.mul (contDiffAt_id.sqrt (hpos d hd).ne'))
      (mul_ne_zero (hpos d hd).ne' (Real.sqrt_pos.mpr (hpos d hd)).ne')
  obtain ⟨C₁, hC₁, hb₁⟩ := compact_iteratedFDeriv_bound isCompact_Icc hinv s
  obtain ⟨C₂, hC₂, hb₂⟩ := compact_iteratedFDeriv_bound isCompact_Icc hsqrt s
  obtain ⟨C₃, hC₃, hb₃⟩ := compact_iteratedFDeriv_bound isCompact_Icc hthree s
  refine ⟨C₁ + C₂ + C₃, add_pos (add_pos hC₁ hC₂) hC₃, fun n hn d hd => ?_⟩
  refine ⟨(hb₁ n hn d hd).trans ?_, (hb₂ n hn d hd).trans ?_,
    (hb₃ n hn d hd).trans ?_⟩ <;> linarith only [hC₁, hC₂, hC₃]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- N01b gives one scalar outer-jet constant at all actual Q/w and D
arguments, independent of the component, point, and parameter state. -/
theorem n01PartB_outerDenominatorJets_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hB : N01PartB D S C base ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, n ≤ s →
      ∀ z ∈ stateNeighborhood S C base ε, ∀ p ∈ annularOpen D,
        let w := stateProfile D S C z.1
        let h := stateHeight D S C z
        let q := heightQ (profileEnergy w p) (heightRadial h p)
          (angularPartial (heightAngular h) p) / w p.1
        let d := polarDiscriminant w h p
        ‖iteratedFDeriv ℝ n (fun x : ℝ => x⁻¹) q‖ ≤ B ∧
        ‖iteratedFDeriv ℝ n (fun x : ℝ => 1 / Real.sqrt x) d‖ ≤ B ∧
        ‖iteratedFDeriv ℝ n inverseDThreeHalves d‖ ≤ B := by
  obtain ⟨B, hBpos, hbound⟩ := normalizedDenominator_outerJets_bound s
  refine ⟨B, hBpos, fun n hn z hz p hp => ?_⟩
  have hb := n01PartB_denominator_bounds hS href hB hz hp
  have hq : heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) /
        stateProfile D S C z.1 p.1 ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ) :=
    ⟨(by norm_num : (1 / 2 : ℝ) ≤ 7 / 8).trans hb.2.2.1,
      hb.2.2.2.1.trans (by norm_num : (9 / 8 : ℝ) ≤ 3 / 2)⟩
  have hd : polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∈
      Icc (1 / 2 : ℝ) (3 / 2 : ℝ) := ⟨hb.2.2.2.2.1, hb.2.2.2.2.2⟩
  exact ⟨(hbound n hn _ hq).1, (hbound n hn _ hd).2⟩

end ContinuousFlexibility.Statements
