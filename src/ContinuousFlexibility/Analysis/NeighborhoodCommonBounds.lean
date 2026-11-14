module

public import ContinuousFlexibility.Analysis.NeighborhoodProfileBounds
public import ContinuousFlexibility.Analysis.NeighborhoodCircleChartsState
public import ContinuousFlexibility.Analysis.SolveStateSpaces
public import ContinuousFlexibility.Blueprint.Statements

/-!
# A single neighbourhood for the profile, denominators and left charts

The three independently constructed radii are intersected at the fixed input
order four.  Profile regularity is obtained from the raw control estimates,
before any flow or inverse-chart property is asserted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem neighborhood_stateNeighborhood_mono {C : NonlinearGeometryData S}
    {base base' : ℕ} {ε ε' : ℝ} (hb : base ≤ base') (hε : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨lt_of_le_of_lt
      (Analysis.solve_stateGrading_monotone S hb (z.1 - C.referenceState))
      (hz.1.trans_le hε), hz.2.trans_le hε⟩

/-- All the elementary geometry is controlled on one order-four state
neighbourhood.  The flow construction can use the conclusions without a
sector restriction; the sector is needed only for oddness of the left chart. -/
theorem exists_common_stateNeighborhood_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {C : NonlinearGeometryData S}
    (hPartA : ContinuousFlexibility.Blueprint.N01PartA D T S C) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (∀ x : AnnularState S, ContDiff ℝ ∞ (stateProfile D S C x)) ∧
      (∀ z ∈ stateNeighborhood S C 4 ε, ∀ r ∈ Ioo D.a D.b,
        (1 / 2 : ℝ) ≤ stateProfile D S C z.1 r / D.w r ∧
        stateProfile D S C z.1 r / D.w r ≤ 2) ∧
      (∀ z ∈ stateNeighborhood S C 4 ε, ∀ p ∈ annularOpen D,
        (7 / 8 : ℝ) ≤ heightQ (profileEnergy (stateProfile D S C z.1) p)
          (heightRadial (stateHeight D S C z) p)
          (angularPartial (heightAngular (stateHeight D S C z)) p) /
            stateProfile D S C z.1 p.1 ∧
        heightQ (profileEnergy (stateProfile D S C z.1) p)
          (heightRadial (stateHeight D S C z) p)
          (angularPartial (heightAngular (stateHeight D S C z)) p) /
            stateProfile D S C z.1 p.1 ≤ (9 / 8 : ℝ) ∧
        (1 / 2 : ℝ) ≤ polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
        polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ≤ (3 / 2 : ℝ) ∧
        (3 / 4 : ℝ) ≤ 1 - heightAngular (stateHeight D S C z) p ^ 2) ∧
      (∀ z ∈ stateNeighborhood S C 4 ε, ∀ m θ,
        (1 / 2 : ℝ) ≤ deriv (stateLeftChart S z.1 m) θ ∧
        deriv (stateLeftChart S z.1 m) θ ≤ 2) ∧
      (∀ z ∈ stateNeighborhood S C 4 ε, stateSector S z.1 → ∀ m θ,
        stateLeftChart S z.1 m (θ + Real.pi) = stateLeftChart S z.1 m θ + Real.pi ∧
        stateLeftChart S z.1 m (-θ) = -stateLeftChart S z.1 m θ) := by
  have href := hPartA.2.1
  have hControl := hPartA.2.2.1
  have hIndex := hPartA.2.2.2.1
  have hJets := hPartA.2.2.2.2
  have hborder : RadialTrueBorder D := hPartA.1.2.2.2.1
  have hsmooth (x : AnnularState S) : ContDiff ℝ ∞ (stateProfile D S C x) :=
    contDiff_stateProfile_of_control_bounds hS hT hD hborder.1 hControl hIndex hJets x
  have hpData :=
    exists_stateNeighborhood_profile_bounds hD hT hS href hborder hControl hIndex hJets
  let εp : ℝ := hpData.choose
  have hεp : 0 < εp := hpData.choose_spec.1
  have hεpOne : εp < 1 := hpData.choose_spec.2.1
  have hprofile := hpData.choose_spec.2.2
  have hdData := exists_stateNeighborhood_denominator_bounds hD hT hS C
  let εd : ℝ := hdData.choose
  have hεd : 0 < εd := hdData.choose_spec.1
  have hdenominator := hdData.choose_spec.2.2
  have hcData := exists_stateNeighborhood_leftChart_deriv_bounds hD hT hS href
  let εc : ℝ := hcData.choose
  have hεc : 0 < εc := hcData.choose_spec.1
  have hchart := hcData.choose_spec.2
  let ε : ℝ := min εp (min εd εc)
  have hε : 0 < ε := lt_min hεp (lt_min hεd hεc)
  have hεp' : ε ≤ εp := min_le_left _ _
  have hεd' : ε ≤ εd := (min_le_right _ _).trans (min_le_left _ _)
  have hεc' : ε ≤ εc := (min_le_right _ _).trans (min_le_right _ _)
  have hp : stateNeighborhood S C 4 ε ⊆ stateNeighborhood S C 4 εp :=
    neighborhood_stateNeighborhood_mono le_rfl hεp'
  have hd : stateNeighborhood S C 4 ε ⊆ stateNeighborhood S C 4 εd :=
    neighborhood_stateNeighborhood_mono le_rfl hεd'
  have hc : stateNeighborhood S C 4 ε ⊆ stateNeighborhood S C 2 εc :=
    neighborhood_stateNeighborhood_mono (by norm_num) hεc'
  refine ⟨ε, hε, hεp'.trans_lt hεpOne, hsmooth,
    fun z hz => hprofile z (hp hz), ?_, fun z hz => hchart z (hc hz), ?_⟩
  · intro z hz
    exact hdenominator z (hd hz) (hsmooth z.1) (hprofile z (hp hz))
  · intro z _ hsector m θ
    exact ⟨stateLeftChart_lift hS z.1 m θ, stateLeftChart_odd hsector m θ⟩

end ContinuousFlexibility.Statements
