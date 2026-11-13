import ContinuousFlexibility.Analysis.N04PositiveGeometryJacobianPair
import ContinuousFlexibility.Analysis.N04PositiveGeometryReciprocalPairs

/-!
# Collecting all eight positive geometry atoms

Four actual coordinate atoms, the physical height and the pulled height
are sufficient. The Jacobian is their first-jet polynomial, and the two
reciprocals use the supplied reference material certificate. All resulting
neighborhoods are chosen before the derivative orders in current data.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

variable (G : N04RealizationGauge)

theorem positiveGeometryData_of_coordinates_height {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε)
    (hmaterial : N04PositiveReferenceMaterialBounds G.W.T G.X.cell G.Y G.H)
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (hR : G.Data η (G.Pos η) base ε (G.atomFamily η .chartRadial) (G.atomRef η .chartRadial))
    (hT : G.Data η (G.Pos η) base ε
      (G.atomFamily η .chartAngleDefect) (G.atomRef η .chartAngleDefect))
    (hIR : G.Data η (G.Pos η) base ε
      (G.atomFamily η .inverseRadial) (G.atomRef η .inverseRadial))
    (hIT : G.Data η (G.Pos η) base ε
      (G.atomFamily η .inverseAngleDefect) (G.atomRef η .inverseAngleDefect))
    (hH : G.Data η (G.Pos η) base ε (G.atomFamily η .height) (G.atomRef η .height))
    (hP : G.Data η (G.Pos η) base ε (G.pulledHeight η) (G.pulledHeightRef η)) :
    ∃ b : ℕ, base ≤ b ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      G.GeometryData η (G.Pos η) b δ := by
  have pR := G.positiveGeometry_atom_pair_of_data hA hmaterial η .chartRadial trivial hR
  have pT := G.positiveGeometry_atom_pair_of_data hA hmaterial η .chartAngleDefect trivial hT
  have pH := G.positiveGeometry_atom_pair_of_data hA hmaterial η .height trivial hH
  have pJ := G.positiveGeometry_jacobian_pair hA η pR pT
  let jd := G.positiveGeometry_data_of_pair hA η .jacobian trivial pJ
  let hd := G.positiveGeometry_denominator_inverse_pair hA hmaterial η false pH
  let id := G.positiveGeometry_denominator_inverse_pair hA hmaterial η true pJ
  let bH : ℕ := hd.choose
  let δH : ℝ := hd.choose_spec.2.choose
  have hbH : base ≤ bH := hd.choose_spec.1
  have hδH : 0 < δH := hd.choose_spec.2.choose_spec.1
  have hδHε : δH ≤ ε := hd.choose_spec.2.choose_spec.2.1
  have hδHhalf : δH ≤ 1 / 2 := hd.choose_spec.2.choose_spec.2.2.1
  have hAH : G.Admissible bH δH := G.admissible_mono hA hbH hδH hδHε
  let hc := G.positiveGeometry_data_of_pair hAH η .heightInverse trivial
    hd.choose_spec.2.choose_spec.2.2.2
  let bI : ℕ := id.choose
  let δI : ℝ := id.choose_spec.2.choose
  have hbI : base ≤ bI := id.choose_spec.1
  have hδI : 0 < δI := id.choose_spec.2.choose_spec.1
  have hδIε : δI ≤ ε := id.choose_spec.2.choose_spec.2.1
  have hδIhalf : δI ≤ 1 / 2 := id.choose_spec.2.choose_spec.2.2.1
  have hAI : G.Admissible bI δI := G.admissible_mono hA hbI hδI hδIε
  let ic := G.positiveGeometry_data_of_pair hAI η .jacobianInverse trivial
    id.choose_spec.2.choose_spec.2.2.2
  let b : ℕ := max (max jd.choose hc.choose) ic.choose
  let δ : ℝ := min (min ε (1 / 2)) (min δH δI)
  have hbJ : jd.choose ≤ b := (le_max_left _ _).trans (le_max_left _ _)
  have hbHC : hc.choose ≤ b := (le_max_right _ _).trans (le_max_left _ _)
  have hbIC : ic.choose ≤ b := le_max_right _ _
  have hb : base ≤ b := jd.choose_spec.1.trans hbJ
  have hδ : 0 < δ := lt_min (lt_min hA.2.1 (by norm_num)) (lt_min hδH hδI)
  have hδJ : δ ≤ min ε (1 / 2) := min_le_left _ _
  have hδε : δ ≤ ε := hδJ.trans (min_le_left _ _)
  have hδhalf : δ ≤ 1 / 2 := hδJ.trans (min_le_right _ _)
  have hδH' : δ ≤ min δH (1 / 2) :=
    le_min ((min_le_right _ _).trans (min_le_left _ _)) hδhalf
  have hδI' : δ ≤ min δI (1 / 2) :=
    le_min ((min_le_right _ _).trans (min_le_right _ _)) hδhalf
  have hcost := G.cost_nonneg η
  have dR := hR.mono (fun _ h => h) hb hδε hcost.1 hcost.2.1
  have dT := hT.mono (fun _ h => h) hb hδε hcost.1 hcost.2.1
  have dIR := hIR.mono (fun _ h => h) hb hδε hcost.1 hcost.2.1
  have dIT := hIT.mono (fun _ h => h) hb hδε hcost.1 hcost.2.1
  have dH := hH.mono (fun _ h => h) hb hδε hcost.1 hcost.2.1
  have dP := hP.mono (fun _ h => h) hb hδε hcost.1 hcost.2.1
  have dJ := jd.choose_spec.2.mono (fun _ h => h) hbJ hδJ hcost.1 hcost.2.1
  have dHI := hc.choose_spec.2.mono (fun _ h => h) hbHC hδH' hcost.1 hcost.2.1
  have dJI := ic.choose_spec.2.mono (fun _ h => h) hbIC hδI' hcost.1 hcost.2.1
  refine ⟨b, hb, δ, hδ, hδε, hδhalf, ?_, dP⟩
  intro a ha
  cases a
  case chartRadial => exact dR
  case chartAngleDefect => exact dT
  case inverseRadial => exact dIR
  case inverseAngleDefect => exact dIT
  case height => exact dH
  case heightInverse => exact dHI
  case jacobian => exact dJ
  case jacobianInverse => exact dJI
  all_goals exact False.elim ha

end N04RealizationGauge

end ContinuousFlexibility.Analysis
