module

public import ContinuousFlexibility.Analysis.NeighborhoodCommonBounds
public import ContinuousFlexibility.Analysis.NeighborhoodCharacteristicSpeedExtension
public import ContinuousFlexibility.Analysis.NeighborhoodCircleFlowRegularity
public import ContinuousFlexibility.Analysis.NeighborhoodFlowGeometry
public import ContinuousFlexibility.Analysis.NeighborhoodRootGerms

/-!
# Construction of the common nonlinear neighborhood

The reference and controls determine one order-four neighborhood. Actual
ordinary characteristic flows are constructed there, and their genuine
return and right-chart inverses are installed without changing the profile
or its controls. Strict support gives the exact reference germ at every
root of the reference slope.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ContDiff

/-- The first nonlinear construction already supplies all the data needed
to build the actual ordinary flows and the common neighborhood. -/
theorem n01bStatement_of_n01a (hN01a : N01aStatement) : N01bStatement := by
  classical
  obtain ⟨A, T, S, C, hT, hS, hPartA, hPrimitive⟩ := hN01a
  have hD : IsAccumulatingProfile A.val := hPartA.1.1
  have hControl : controlGeometryConditions A.val S C := hPartA.2.2.1
  obtain ⟨ε, hε, _, hsmooth, hprofile, hden, hchart, hparity⟩ :=
    exists_common_stateNeighborhood_bounds hD hT hS hPartA
  let Flow (z : AnnularState S × ℝ) (m : ℕ) (Φ : ℝ → ℝ → ℝ) : Prop :=
    ∀ θ, Φ (C.left m) θ = θ ∧
      ContinuousOn (fun r => Φ r θ) (Icc (C.left m) (C.right m)) ∧
      (∀ r ∈ Ioo (C.left m) (C.right m),
        HasDerivAt (fun s => Φ s θ)
          (minusCharacteristicSpeed (originalCoefficients A.val S C z) (r, Φ r θ)) r) ∧
      (∀ r ∈ Icc (C.left m) (C.right m),
        0 < deriv (Φ r) θ ∧ Φ r (θ + Real.pi) = Φ r θ + Real.pi)
  have hflows : ∀ z : AnnularState S × ℝ, ∀ m : ℕ,
      ∃ Φ : ℝ → ℝ → ℝ, z ∈ stateNeighborhood S C 4 ε → Flow z m Φ := by
    intro z m
    by_cases hz : z ∈ stateNeighborhood S C 4 ε
    · have hadm : ∀ p ∈ annularOpen A.val,
          0 < polarDiscriminant (stateProfile A.val S C z.1) (stateHeight A.val S C z) p ∧
          heightQ (profileEnergy (stateProfile A.val S C z.1) p)
            (heightRadial (stateHeight A.val S C z) p)
            (angularPartial (heightAngular (stateHeight A.val S C z)) p) ≠ 0 := by
        intro p hp
        have hb := hden z hz p hp
        have hwp : 0 < stateProfile A.val S C z.1 p.1 :=
          mul_pos (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
        have hqratio : 0 < heightQ (profileEnergy (stateProfile A.val S C z.1) p)
            (heightRadial (stateHeight A.val S C z) p)
            (angularPartial (heightAngular (stateHeight A.val S C z)) p) /
              stateProfile A.val S C z.1 p.1 :=
          lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb.1
        exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.2.2.1,
          ((div_pos_iff_of_pos_right hwp).mp hqratio).ne'⟩
      obtain ⟨G, dG, hG, hdG, hder, hperiod, heq⟩ :=
        exists_stateCharacteristicSpeed_extension hD hT hS hControl (hsmooth z.1) hadm m
      obtain ⟨Φ, hinit, htime, hode, hangle⟩ :=
        exists_regular_continuousAngleFlow (hControl.1 m).2.1.le hG hdG hder
          Real.pi_pos hperiod
      refine ⟨fun r θ => Φ (r, θ), fun _ θ => ⟨hinit θ, htime θ, ?_, ?_⟩⟩
      · intro r hr
        have hh := hode r hr θ
        rw [heq r ⟨hr.1.le, hr.2.le⟩ (Φ (r, θ))] at hh
        exact hh
      · intro r hr
        exact hangle r hr θ
    · exact ⟨fun _ θ => θ, fun hz' => (hz hz').elim⟩
  choose Θ hΘ using hflows
  let C' : NonlinearGeometryData S := circleFlowGeometry C Θ
  refine ⟨A, T, S, C', 4, ε, hT, hS, circleFlowGeometry_partA hPartA Θ,
    hε, ?_, hPrimitive⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz m θ
    exact hΘ z m hz θ
  · intro z hz hsector m θ
    exact ⟨(hchart z hz m θ).1, (hchart z hz m θ).2,
      (hparity z hz hsector m θ).1, (hparity z hz hsector m θ).2⟩
  · intro z hz _ m θ
    have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
      ⟨(hControl.1 m).2.1.le, le_rfl⟩
    have hpos (η : ℝ) : 0 < deriv (Θ z m (C.right m)) η :=
      ((hΘ z m hz η).2.2.2 (C.right m) hr).1
    have hRc : Continuous (Θ z m (C.right m)) :=
      continuous_iff_continuousAt.mpr fun η =>
        (differentiableAt_of_deriv_ne_zero (hpos η).ne').continuousAt
    have hRm : StrictMono (Θ z m (C.right m)) := strictMono_of_deriv_pos hpos
    have hRl (η : ℝ) : Θ z m (C.right m) (η + Real.pi) =
        Θ z m (C.right m) η + Real.pi :=
      ((hΘ z m hz η).2.2.2 (C.right m) hr).2
    have hinv := circleFlowGeometry_inverse_identities C Θ z m
      (contDiff_stateLeftChart hS z.1 m).continuous
      (stateLeftChart_strictMono_of_deriv_lower z.1 m (fun η => (hchart z hz m η).1))
      (stateLeftChart_lift hS z.1 m) hRc hRm hRl
    exact ⟨(hinv.1 θ).1, (hinv.1 θ).2, (hinv.2 θ).1, (hinv.2 θ).2⟩
  · intro z hz _ p hp
    have hpbound := hprofile z hz p.1 hp.1
    have hdbound := hden z hz p hp
    exact ⟨hpbound.1, hpbound.2, hdbound.1, hdbound.2.1,
      hdbound.2.2.1, hdbound.2.2.2.1⟩
  · intro z _ r hr hroot
    exact stateProfile_eventuallyEq_reference_at_root hControl
      (fun m => (hControl.2.2.2.2.2.1 m).2.2)
      hPartA.1.2.2.2.1.2.2.1 hr hroot z.1

end ContinuousFlexibility.Blueprint
