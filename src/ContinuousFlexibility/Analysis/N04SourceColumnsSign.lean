import ContinuousFlexibility.Analysis.N04SourceColumnsGeometry
import ContinuousFlexibility.Analysis.N04SourceColumnsData
import ContinuousFlexibility.Analysis.SectorParameterGeometry
import Mathlib.Topology.Order.IntermediateValue

/-!
# One fixed sign for each inverse determinant

The determinant never vanishes on an admissible chart.  Its spatial and
parameter sections are continuous on preconnected sets, so one scalar of
absolute value one removes the absolute value throughout each piece.
Separate continuity suffices; no unproved joint regularity is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

private theorem n04SourceColumns_positive_on_preconnected
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsPreconnected U)
    {f : X → ℝ} (hf : ContinuousOn f U) (hne : ∀ x ∈ U, f x ≠ 0)
    {x₀ : X} (hx₀ : x₀ ∈ U) (hf₀ : 0 < f x₀) {x : X} (hx : x ∈ U) :
    0 < f x := by
  by_contra hnot
  obtain ⟨y, hy, hzero⟩ := hU.intermediate_value hx hx₀ hf
    ⟨le_of_not_gt hnot, hf₀.le⟩
  exact hne y hy hzero

/-- A nonvanishing separately continuous real family on two preconnected
sets has one fixed sign. -/
theorem n04SourceColumns_fixed_sign_separate
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} {V : Set Y} (hU : IsPreconnected U) (hV : IsPreconnected V)
    {f : X → Y → ℝ}
    (hparameter : ∀ y ∈ V, ContinuousOn (fun x => f x y) U)
    (hspatial : ∀ x ∈ U, ContinuousOn (f x) V)
    (hne : ∀ x ∈ U, ∀ y ∈ V, f x y ≠ 0)
    {x₀ : X} (hx₀ : x₀ ∈ U) {y₀ : Y} (hy₀ : y₀ ∈ V) :
    ∃ σ : ℝ, |σ| = 1 ∧ ∀ x ∈ U, ∀ y ∈ V, |f x y| = σ * f x y := by
  have hsign : ∃ σ : ℝ, |σ| = 1 ∧ 0 < σ * f x₀ y₀ := by
    rcases lt_or_gt_of_ne (hne x₀ hx₀ y₀ hy₀) with hneg | hpos
    · exact ⟨-1, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by simpa only [one_mul] using hpos⟩
  obtain ⟨σ, hσ, hpositive⟩ := hsign
  have hσne : σ ≠ 0 := by
    intro hz
    have he : (0 : ℝ) = 1 := by simpa only [hz, abs_zero] using hσ
    exact zero_ne_one he
  have hreference (y : Y) (hy : y ∈ V) : 0 < σ * f x₀ y :=
    n04SourceColumns_positive_on_preconnected hV
      (continuousOn_const.mul (hspatial x₀ hx₀))
      (fun q hq => mul_ne_zero hσne (hne x₀ hx₀ q hq)) hy₀ hpositive hy
  refine ⟨σ, hσ, fun x hx y hy => ?_⟩
  have hcurrent : 0 < σ * f x y :=
    n04SourceColumns_positive_on_preconnected hU
      (continuousOn_const.mul (hparameter y hy))
      (fun z hz => mul_ne_zero hσne (hne z hz y hy)) hx₀ (hreference y hy) hx
  calc |f x y| = |σ| * |f x y| := by rw [hσ, one_mul]
    _ = |σ * f x y| := (abs_mul _ _).symm
    _ = σ * f x y := abs_of_pos hcurrent

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N04RealizationGauge

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

theorem sourceColumns_inverseDeterminant_parameter_continuous {b : ℕ} {ε : ℝ}
    (hG : G.GeometryData η (fun _ => True) b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    ContinuousOn (fun z => G.sourceColumnsInverseDeterminant η z m p)
      (sectorNeighborhood (G.S η) b ε ε) := by
  let R := (hG.1 .inverseRadial trivial).sourceColumns_regularity
    (n04SourceReferenceData_of_referenceJets href .inverseRadial) m
  let A := (hG.1 .inverseAngleDefect trivial).sourceColumns_regularity
    (n04SourceReferenceData_of_referenceJets href .inverseAngleDefect) m
  exact continuousOn_const.mul
    (((R.parameter 1 0 p hp).continuousOn.mul
      (continuousOn_const.add (A.parameter 0 1 p hp).continuousOn)).sub
      ((A.parameter 1 0 p hp).continuousOn.mul (R.parameter 0 1 p hp).continuousOn))

theorem sourceColumns_inverseDeterminant_spatial_continuous {b : ℕ} {ε : ℝ}
    (hG : G.GeometryData η (fun _ => True) b ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε) (m : ℕ) :
    ContinuousOn (G.sourceColumnsInverseDeterminant η z m) unitStrip := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hr := ((hG.1 .inverseRadial trivial).1 z hz m trivial).1
  have ha := ((hG.1 .inverseAngleDefect trivial).1 z hz m trivial).1
  exact continuousOn_const.mul
    (((contDiffOn_mixedDerivative hU hr 1 0).continuousOn.mul
      (continuousOn_const.add (contDiffOn_mixedDerivative hU ha 0 1).continuousOn)).sub
      ((contDiffOn_mixedDerivative hU ha 1 0).continuousOn.mul
        (contDiffOn_mixedDerivative hU hr 0 1).continuousOn))

/-- Current and reference inverse determinants share one fixed scalar
sign on each piece. The sign has no parameter or spatial derivatives. -/
theorem sourceColumns_inverseDeterminant_fixedSign {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (hG : G.GeometryData η (fun _ => True) b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ σ : ℕ → ℝ, (∀ m, |σ m| = 1) ∧
      (∀ z ∈ sectorNeighborhood (G.S η) b ε ε, ∀ m p, p ∈ unitStrip →
        |G.sourceColumnsInverseDeterminant η z m p| =
          σ m * G.sourceColumnsInverseDeterminant η z m p) ∧
      ∀ m p, p ∈ unitStrip → |G.sourceColumnsInverseDeterminantRef η m p| =
        σ m * G.sourceColumnsInverseDeterminantRef η m p := by
  have hU : IsPreconnected (sectorNeighborhood (G.S η) b ε ε) :=
    (sectorNeighborhood_convex (G.S η) b ε ε).isPreconnected
  have hV : IsPreconnected unitStrip := isPreconnected_Ioo.prod isPreconnected_univ
  have hzero : (0 : Parameter (G.S η)) ∈ sectorNeighborhood (G.S η) b ε ε := by
    change sectorGrading (G.S η) b (0 : StateDirections (G.S η)) < ε ∧ |(0 : ℝ)| < ε
    simpa only [map_zero, abs_zero] using And.intro hA.2.1 hA.2.1
  have hmid : ((1 / 2 : ℝ), (0 : ℝ)) ∈ unitStrip := by
    refine ⟨?_, mem_univ _⟩
    norm_num
  have hsign (m : ℕ) := n04SourceColumns_fixed_sign_separate hU hV
    (fun p hp => G.sourceColumns_inverseDeterminant_parameter_continuous η hG href m hp)
    (fun z hz => G.sourceColumns_inverseDeterminant_spatial_continuous η hG hz m)
    (fun z hz p hp => G.sourceColumns_inverseDeterminant_ne_zero η hA hG hz m hp)
    hzero hmid
  let σ : ℕ → ℝ := fun m => (hsign m).choose
  refine ⟨σ, fun m => (hsign m).choose_spec.1,
    fun z hz m p hp => (hsign m).choose_spec.2 z hz p hp, ?_⟩
  intro m p hp
  have he := (hsign m).choose_spec.2 0 hzero p hp
  rw [G.sourceColumns_inverseDeterminant_zero η] at he
  exact he

end N04RealizationGauge

end ContinuousFlexibility.Analysis
