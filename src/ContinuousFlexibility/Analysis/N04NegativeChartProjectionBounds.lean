module

public import ContinuousFlexibility.Analysis.RootCompositionBounds
public import ContinuousFlexibility.Analysis.RootChartWithin

/-!
# Root projections of the actual positive state slices

Angular translation makes the finite-order root estimate available at
every real angle. The input slice may be periodic, a lift, or neither;
the proof uses only its actual smooth jets on the displayed source box.
This is the form needed for positive state derivatives of the root label.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem rootProjection_angular_translate
    (odd : Bool) (G : ℝ × ℝ × ℝ → ℝ) (θ : ℝ) :
    (fun p : PolarPoint => if odd then
      rootOddCoefficient (fun q => G (q + (0, 0, θ))) p
      else rootEven (fun q => G (q + (0, 0, θ))) p) =
    (fun p : PolarPoint => (if odd then rootOddCoefficient G else rootEven G)
      (p + (0, θ))) := by
  funext p
  cases odd <;> simp only [Bool.false_eq_true, ↓reduceIte, rootOddCoefficient,
    rootOdd, rootEven, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, add_zero]

/-- The even projection costs `s` source derivatives; the divided odd
projection costs `s + 1`. The constant is uniform in the angle and input. -/
theorem n04NegativeChart_rootProjection_allAngle_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (odd : Bool) (G : ℝ × ℝ × ℝ → ℝ),
      ContDiff ℝ ∞ G → ∀ M : ℝ,
      CSBound (s + if odd then 1 else 0)
        (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℝ)) G M →
      ∀ x ∈ Ioc (0 : ℝ) 1, ∀ θ : ℝ,
        ‖iteratedFDeriv ℝ s
          (if odd then rootOddCoefficient G else rootEven G) (x, θ)‖ ≤ C * M := by
  obtain ⟨C, hC, hbound⟩ := exists_rootComposition_csBound s
  refine ⟨C, hC, fun odd G hG M hraw x hx θ => ?_⟩
  let g : ℝ × ℝ × ℝ → ℝ := fun q => G (q + (0, 0, θ))
  have hg : ContDiff ℝ ∞ g := hG.comp (contDiff_id.add contDiff_const)
  have hinput : CSBound (s + if odd then 1 else 0)
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) g M := by
    intro n hn q hq
    rw [iteratedFDeriv_comp_add_right]
    exact hraw n hn (q + (0, 0, θ))
      ⟨by simpa only [Prod.fst_add, add_zero] using hq.1,
        by simpa only [Prod.snd_add, Prod.fst_add, add_zero] using hq.2.1,
        mem_univ _⟩
  have hp : (x, (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
    ⟨⟨hx.1.le, hx.2⟩, neg_nonpos.mpr Real.pi_pos.le, Real.pi_pos.le⟩
  have hb : ‖iteratedFDeriv ℝ s
      (if odd then rootOddCoefficient g else rootEven g) (x, 0)‖ ≤ C * M := by
    cases odd with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hinput ⊢
        exact (hbound g hg M).1 hinput s le_rfl (x, 0) hp
    | true =>
        simp only [↓reduceIte] at hinput ⊢
        have he : rootOddCoefficient g = -rootOdd g := rfl
        rw [he, iteratedFDeriv_neg_apply, norm_neg]
        exact (hbound g hg M).2 hinput s le_rfl (x, 0) hp
  have he : (if odd then rootOddCoefficient g else rootEven g) =
      fun p : PolarPoint => (if odd then rootOddCoefficient G else rootEven G)
        (p + (0, θ)) := by
    cases odd with
    | false => simpa only [g, Bool.false_eq_true, ↓reduceIte] using
        rootProjection_angular_translate false G θ
    | true => simpa only [g, ↓reduceIte] using rootProjection_angular_translate true G θ
  rw [he, iteratedFDeriv_comp_add_right] at hb
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using hb

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_rootProjection_allAngle_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_rootProjection_allAngle_bound
