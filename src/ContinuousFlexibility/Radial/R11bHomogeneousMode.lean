module

public import ContinuousFlexibility.Radial.R11bHilbertRepresentatives

/-!
# Homogeneous physical mode uniqueness from the given modal inverse

The scalar in the frozen modal graph is the negative of the physical border
scalar. The raw function is lifted to the actual radial Hilbert space, and
the modal inverse's maximal-graph uniqueness then excludes every homogeneous
solution satisfying the corresponding row.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_homogeneous_mode_eq_zero {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {j : ℕ}
    {G : RadialModePair D →L[ℝ] RadialModePair D} (hG : ModeInverseProperties D j G)
    {u : ℝ → ℝ} (hu : MemLp u 2 (radialHilbertMeasure D)) (κ : ℝ)
    (hκ : j ≠ 2 → κ = 0)
    (hrow : j = 2 → (∫ r in D.a..D.b, referenceColumn D r * u r) = 0)
    (heq : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Function.support φ ⊆ radialCore D →
        (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w φ r) +
          κ * (∫ r in D.a..D.b, referenceColumn D r * φ r) = 0) :
    u =ᵐ[volume.restrict (radialCore D)] 0 ∧ κ = 0 := by
  let U : RadialModePair D := (hu.toLp u, -κ)
  have hueq := r11b_toLp_radialHilbert_ae hgeom hu
  have hzero := r11b_zero_radialHilbert_ae hgeom
  have hgraph : ModeFullGraph D j U 0 := by
    refine ⟨?_, ?_⟩
    · intro φ hφ hφc hφs
      have hsource :
          (∫ r in D.a..D.b, (12 * D.w r / r ^ 2) *
            (0 : RadialModeL2 D) r * φ r) = 0 := by
        calc
          _ = ∫ _r in D.a..D.b, (0 : ℝ) :=
            r11b_intervalIntegral_congr_core hgeom.2.1.le
              (hzero.mono fun r hr => by
                change (0 : RadialModeL2 D) r = 0 at hr
                change (12 * D.w r / r ^ 2) * (0 : RadialModeL2 D) r * φ r = 0
                rw [hr, mul_zero, zero_mul])
          _ = 0 := intervalIntegral.integral_zero
      have hleft :
          (∫ r in D.a..D.b, (hu.toLp u) r * radialJacobi ((j : ℝ) ^ 2) D.w φ r) =
            ∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w φ r :=
        r11b_intervalIntegral_congr_core hgeom.2.1.le
          (hueq.mono fun r hr => congrArg (fun z => z * radialJacobi ((j : ℝ) ^ 2) D.w φ r) hr)
      change (∫ r in D.a..D.b, (hu.toLp u) r * radialJacobi ((j : ℝ) ^ 2) D.w φ r) -
        (-κ) * (∫ r in D.a..D.b, referenceColumn D r * φ r) =
          -(∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * (0 : RadialModeL2 D) r * φ r)
      rw [hleft, hsource]
      linarith [heq φ hφ hφc hφs]
    · by_cases hj : j = 2
      · simp only [hj, ite_true]
        change (∫ r in D.a..D.b, referenceColumn D r * (hu.toLp u) r) = 0
        calc
          _ = ∫ r in D.a..D.b, referenceColumn D r * u r :=
            r11b_intervalIntegral_congr_core hgeom.2.1.le
              (hueq.mono fun r hr => congrArg (fun z => referenceColumn D r * z) hr)
          _ = 0 := hrow hj
      · simp only [hj, ite_false]
        exact ⟨by change -κ = 0; rw [hκ hj, neg_zero], rfl⟩
  have hU : U = 0 := by
    have h := hG.2 U 0 hgraph
    simpa only [map_zero] using h.symm
  have hfield : hu.toLp u = (0 : RadialModeL2 D) := congrArg Prod.fst hU
  have hscalar : -κ = 0 := congrArg Prod.snd hU
  refine ⟨hueq.symm.trans ?_, by linarith⟩
  rw [hfield]
  exact hzero

end ContinuousFlexibility.Radial
