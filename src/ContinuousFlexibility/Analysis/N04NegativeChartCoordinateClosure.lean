import ContinuousFlexibility.Analysis.N04NegativeChartGeometry
import ContinuousFlexibility.Analysis.N04NegativeChartReferences
import ContinuousFlexibility.Analysis.N04NegativeChartDeterminantData
import ContinuousFlexibility.Analysis.N04NegativeChartAbsoluteData
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# The four chart atoms from the two actual coordinates

The determinant polynomial, its fixed sign and its reciprocal are proved
operations on current data. This closes both Jacobian atoms from the
actual radial coordinate and angle defect. Only negative pieces are
enumerated, and every operation retains their original material samples.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

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

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

private theorem chartData_cases (P : Atom → Prop)
    (hR : P .chartRadial) (hA : P .chartAngleDefect)
    (hJ : P .jacobian) (hI : P .jacobianInverse) :
    ∀ a, atomIsNegativeChart a → P a := by
  intro a ha
  cases a <;> first
    | exact False.elim ha
    | exact hR
    | exact hA
    | exact hJ
    | exact hI

/-- No Jacobian estimate is an input: both Jacobian atoms follow from
the true coordinate current data and the retained reference geometry. -/
set_option diagnostics true in
theorem negativeChart_data_of_coordinates {b : ℕ} {ε : ℝ}
    (hb : G.W.base ≤ b) (hε : 0 < ε) (hεW : ε ≤ G.W.ε)
    (hR : G.Data η (G.Neg η) b ε
      (G.atomFamily η .chartRadial) (G.atomRef η .chartRadial))
    (hA : G.Data η (G.Neg η) b ε
      (G.atomFamily η .chartAngleDefect) (G.atomRef η .chartAngleDefect)) :
    ∃ b' : ℕ, ∃ ε' : ℝ, b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      G.NegativeAtomData η atomIsNegativeChart b' ε' := by
  let r : ℕ → ℕ := G.negativeChartPiece
  have hr (n : ℕ) : G.Neg η (r n) := G.negativeChartPiece_negative η n
  have hD : IsAccumulatingProfile G.W.D := G.W.radial.1
  have hT : IsMaterialData G.W.D G.W.U := isMaterialData_enlargedMaterialData hD G.W.hT
  have hE (n : ℕ) : 1 ≤ G.W.U.E0 (G.W.U.sample ((G.V η).cell (r n))) :=
    (G.cost_nonneg η).2.2 (r n)
  have hH (n : ℕ) : 0 ≤ G.W.U.H (G.W.U.sample ((G.V η).cell (r n))) :=
    (G.cost_nonneg η).2.1 (r n)
  have hI : HasInterpolation (parameterGrading G.W.S) :=
    hasInterpolation_of_hasSmoothing (n07aParameterGrading_monotone G.W.S)
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing G.W.hS) hasSmoothing_realGrading)
  have hR₀ := G.negativeChart_referenceData η .chartRadial trivial
  have hA₀ := G.negativeChart_referenceData η .chartAngleDefect trivial
  have hwidth := G.negativeChart_widthRatio_enumerated η
  have hdet₀ := n04NegativeChart_referenceDeterminant_data hR₀ hA₀ hE
    (fun n => G.negativeChartWidthRatio η (r n)) hwidth
  have hdetExists :=
    n04NegativeChart_currentDeterminant_data hD hT hε hE hI
      (hR.reindex_selected r hr) (hA.reindex_selected r hr) hR₀ hA₀
      (fun n => G.negativeChartWidthRatio η (r n)) hwidth
  let b₁ : ℕ := hdetExists.choose
  let ε₁ : ℝ := hdetExists.choose_spec.choose
  have hb₁ : b ≤ b₁ := hdetExists.choose_spec.choose_spec.1
  have hε₁ : 0 < ε₁ := hdetExists.choose_spec.choose_spec.2.1
  have hε₁ε : ε₁ ≤ ε := hdetExists.choose_spec.choose_spec.2.2.1
  have hd : CurrentJetDataOn G.W.S G.W.U ((G.V η).cell ∘ r) (fun _ => True) b₁ ε₁
      (fun z n => G.negativeChartDeterminant η z (r n))
      (fun n => G.negativeChartDeterminantRef η (r n)) :=
    hdetExists.choose_spec.choose_spec.2.2.2
  have hd₀ : N04SourceReferenceData G.W.U ((G.V η).cell ∘ r)
      (fun n => G.negativeChartDeterminantRef η (r n)) := hdet₀
  have hsub : sectorNeighborhood G.W.S b₁ ε₁ ε₁ ⊆
      sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε :=
    sectorNeighborhood_mono G.W.S (hb.trans hb₁) (hε₁ε.trans hεW) (hε₁ε.trans hεW)
  have hzero : (0 : Parameter G.W.S) ∈
      sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε := by
    change sectorGrading G.W.S G.W.base (0 : StateDirections G.W.S) < G.W.ε ∧
      |(0 : ℝ)| < G.W.ε
    exact ⟨(sectorGrading G.W.S G.W.base).map_zero'.trans_lt G.W.ε_pos,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt G.W.ε_pos⟩
  have habs := hd.negativeChart_abs hd₀ hε₁ hE hH
    (fun n q _ => congrFun (congrFun (G.negativeChartDeterminant_zero η) (r n)) q)
    (fun z hz n q hq => G.negativeChartDeterminant_ne_zero η z (hsub hz) (r n) (hr n) hq)
  have hjref (n : ℕ) {q : PolarPoint} (hq : q ∈ unitStrip) :
      |G.negativeChartDeterminantRef η (r n) q| = G.atomRef η .jacobian (r n) q := by
    have hdq : G.negativeChartDeterminant η 0 (r n) q =
        G.negativeChartDeterminantRef η (r n) q :=
      congrFun (congrFun (G.negativeChartDeterminant_zero η) (r n)) q
    have hjq : G.atomFamily η .jacobian 0 (r n) q = G.atomRef η .jacobian (r n) q :=
      congrFun (congrFun (G.atomFamily_zero η .jacobian) (r n)) q
    exact (congrArg abs hdq).symm.trans
      ((G.negativeChart_jacobian_eq_abs η 0 hzero (r n) (hr n) hq).symm.trans hjq)
  have hj : CurrentJetDataOn G.W.S G.W.U ((G.V η).cell ∘ r) (fun _ => True) b₁ ε₁
      (fun z n => G.atomFamily η .jacobian z (r n))
      (fun n => G.atomRef η .jacobian (r n)) :=
    habs.sourceColumns_congr
      (fun z hz n q hq => (G.negativeChart_jacobian_eq_abs η z (hsub hz) (r n) (hr n) hq).symm)
      (fun n _ hq => hjref n hq)
  have hj₀ := G.negativeChart_referenceData η .jacobian trivial
  have hi₀ : N04SourceReferenceData G.W.U ((G.V η).cell ∘ r)
      (fun n q => (G.atomRef η .jacobian (r n) q)⁻¹) :=
    G.negativeChart_referenceData η .jacobianInverse trivial
  have hpos (n : ℕ) (q : PolarPoint) (hq : q ∈ unitStrip) :
      0 < G.atomRef η .jacobian (r n) q := by
    have hjq : G.atomFamily η .jacobian 0 (r n) q = G.atomRef η .jacobian (r n) q :=
      congrFun (congrFun (G.atomFamily_zero η .jacobian) (r n)) q
    exact (G.negativeChart_jacobian_pos η 0 hzero (r n) (hr n) hq).trans_eq hjq
  have hinvExists := hj.negativeChart_inv hD hT hI hj₀ hi₀ hε₁ hE hpos
  let b₂ : ℕ := hinvExists.choose
  let ε₂ : ℝ := hinvExists.choose_spec.choose
  have hb₂ : b₁ ≤ b₂ := hinvExists.choose_spec.choose_spec.1
  have hε₂ : 0 < ε₂ := hinvExists.choose_spec.choose_spec.2.1
  have hε₂ε₁ : ε₂ ≤ ε₁ := hinvExists.choose_spec.choose_spec.2.2.1
  have hjSelected : G.Data η (G.Neg η) b₁ ε₁
      (G.atomFamily η .jacobian) (G.atomRef η .jacobian) :=
    CurrentJetDataOn.of_reindex_selected r (G.negativeChartPiece_covers η) hj
  have hiSelected : G.Data η (G.Neg η) b₂ ε₂
      (G.atomFamily η .jacobianInverse) (G.atomRef η .jacobianInverse) :=
    CurrentJetDataOn.of_reindex_selected r (G.negativeChartPiece_covers η)
      hinvExists.choose_spec.choose_spec.2.2.2
  have hbb₂ : b ≤ b₂ := hb₁.trans hb₂
  have hε₂ε : ε₂ ≤ ε := hε₂ε₁.trans hε₁ε
  have hR₂ := hR.mono (fun _ h => h) hbb₂ hε₂ε (G.cost_nonneg η).1 (G.cost_nonneg η).2.1
  have hA₂ := hA.mono (fun _ h => h) hbb₂ hε₂ε (G.cost_nonneg η).1 (G.cost_nonneg η).2.1
  have hJ₂ := hjSelected.mono (fun _ h => h) hb₂ hε₂ε₁
    (G.cost_nonneg η).1 (G.cost_nonneg η).2.1
  exact ⟨b₂, ε₂, hbb₂, hε₂, hε₂ε, chartData_cases
    (fun a => G.Data η (G.Neg η) b₂ ε₂ (G.atomFamily η a) (G.atomRef η a))
    hR₂ hA₂ hJ₂ hiSelected⟩

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_data_of_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_data_of_coordinates
