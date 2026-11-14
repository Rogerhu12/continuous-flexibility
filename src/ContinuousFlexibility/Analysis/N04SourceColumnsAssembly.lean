module

public import ContinuousFlexibility.Analysis.N04SourceColumnsFactor
public import ContinuousFlexibility.Analysis.N04SourceColumnsAuxiliary

/-!
# Assembly of the source-column obligation

The same source factor multiplies each supplied physical column. All
four output atoms are independent of the auxiliary column. A reference
witness, if one exists, selects the neighborhood before the universally
quantified auxiliary column; without such a witness the conclusion is
vacuous on the original admissible neighborhood.
-/

@[expose] public section

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

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

theorem sourceColumns_data {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (hG : G.GeometryData η (fun _ => True) b ε)
    (hF : G.FieldData η b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ b' ε', b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ a : Atom, atomIsSourceColumn a →
        G.Data η (fun _ => True) b' ε' (G.atomFamily η a) (G.atomRef η a) := by
  have hD := G.W.radial.1
  have hT := isMaterialData_enlargedMaterialData hD G.W.hT
  have hE := (G.cost_nonneg η).2.2
  have hE₀ := (G.cost_nonneg η).1
  have hH := (G.cost_nonneg η).2.1
  have hI := G.sourceColumns_interpolation η
  have hs := G.sourceColumns_factor_pair_data η hA hG href
  let b₁ : ℕ := hs.choose
  let ε₁ : ℝ := hs.choose_spec.choose
  have hs₁ := hs.choose_spec.choose_spec
  have hF₁ := G.fieldData_mono η hF hs₁.1 hs₁.2.2.1
  have hs₀ := n04SourceReferenceData_of_referenceJets href .sourceFactor
  have hl₀ := G.sourceColumns_pulledLeftRef_data η hA href
  have hn₀ := G.sourceColumns_pulledNuRef_data η hA href
  have hl := CurrentJetDataOn.sourceColumns_mul hD hT hs₁.2.1 hE hI
    hs₁.2.2.2.1 hF₁.2.1 hs₀ hl₀
  let b₂ : ℕ := hl.choose
  let ε₂ : ℝ := hl.choose_spec.choose
  have hl₂ := hl.choose_spec.choose_spec
  have hleft : G.Data η (fun _ => True) b₂ ε₂
      (G.atomFamily η .leftColumn) (G.atomRef η .leftColumn) := by
    exact hl₂.2.2.2.sourceColumns_congr
      (fun z _ m q _ => congrFun (congrFun (congrFun
        (G.sourceColumns_leftFamily_eq η).symm z) m) q)
      (fun m q _ => congrFun (congrFun (G.sourceColumns_leftRef_eq η).symm m) q)
  have hfactor₂ := hs₁.2.2.2.1.mono (fun _ h => h) hl₂.1 hl₂.2.2.1 hE₀ hH
  have hinverse₂ := hs₁.2.2.2.2.mono (fun _ h => h) hl₂.1 hl₂.2.2.1 hE₀ hH
  have hF₂ := G.fieldData_mono η hF₁ hl₂.1 hl₂.2.2.1
  have hn := CurrentJetDataOn.sourceColumns_mul hD hT hl₂.2.1 hE hI
    hfactor₂ hF₂.2.2 hs₀ hn₀
  let b' : ℕ := hn.choose
  let ε' : ℝ := hn.choose_spec.choose
  have hn' := hn.choose_spec.choose_spec
  have hfactor := hfactor₂.mono (fun _ h => h) hn'.1 hn'.2.2.1 hE₀ hH
  have hinverse := hinverse₂.mono (fun _ h => h) hn'.1 hn'.2.2.1 hE₀ hH
  have hleft' := hleft.mono (fun _ h => h) hn'.1 hn'.2.2.1 hE₀ hH
  have hnu : G.Data η (fun _ => True) b' ε'
      (G.atomFamily η .nuColumn) (G.atomRef η .nuColumn) := by
    exact hn'.2.2.2.sourceColumns_congr
      (fun z _ m q _ => congrFun (congrFun (congrFun
        (G.sourceColumns_nuFamily_eq η).symm z) m) q)
      (fun m q _ => congrFun (congrFun (G.sourceColumns_nuRef_eq η).symm m) q)
  refine ⟨b', ε', hs₁.1.trans (hl₂.1.trans hn'.1), hn'.2.1,
    hn'.2.2.1.trans (hl₂.2.2.1.trans hs₁.2.2.1), ?_⟩
  intro a ha
  cases a <;> first
    | exact False.elim ha
    | exact hfactor
    | exact hinverse
    | exact hleft'
    | exact hnu

end N04RealizationGauge

/-- The source-column obligation, retaining the same-atlas reference
premise and the original common-neighborhood quantifier order. -/
theorem n04SourceColumns_obligation : N04RealizationSourceColumnObligation := by
  classical
  intro G b ε hA hG hF
  by_cases hR : ∃ η, ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
  · let η₀ := hR.choose
    have hd := G.sourceColumns_data η₀ hA
      (hG η₀ hR.choose_spec) (hF η₀ hR.choose_spec) hR.choose_spec
    let b' : ℕ := hd.choose
    let ε' : ℝ := hd.choose_spec.choose
    have hd' := hd.choose_spec.choose_spec
    refine ⟨b', ε', hd'.1, hd'.2.1, hd'.2.2.1, ?_⟩
    intro η href a ha
    exact G.sourceColumns_data_auxiliary η₀ η b' ε' a ha (hd'.2.2.2 a ha)
  · refine ⟨b, ε, le_rfl, hA.2.1, le_rfl, ?_⟩
    intro η href
    exact False.elim (hR ⟨η, href⟩)

end ContinuousFlexibility.Analysis
