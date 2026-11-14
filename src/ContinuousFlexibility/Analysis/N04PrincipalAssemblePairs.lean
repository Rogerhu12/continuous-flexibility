import ContinuousFlexibility.Analysis.N04PrincipalCoreData
import ContinuousFlexibility.Analysis.N04PrincipalPositivePotentialPairs

/-!
# Assembling the principal and potential pairs on all pieces

The determinant and the principal A reciprocal each choose one common
smaller neighborhood. All other finite expressions are restricted to
these neighborhoods, so every final atom retains the same atlas and the
same reference member.
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

theorem n04Principal_core_pairs {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (fun _ => True) b ε) (hf : G.FieldData η b ε)
    (hH : G.n04PrincipalPair η b ε (G.pulledHeight η) (G.pulledHeightRef η))
    (hHI : G.n04PrincipalPair η b ε
      (fun z m q => (G.pulledHeight η z m q)⁻¹)
      (fun m q => (G.pulledHeightRef η m q)⁻¹)) :
    ∃ b' : ℕ, b ≤ b' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : Fin 5, G.n04PrincipalPair η b' ε'
        (G.atomFamily η (n04PrincipalCoreAtom i)) (G.atomRef η (n04PrincipalCoreAtom i)) := by
  have hpos := G.n04PrincipalPositive_principal_pairBounds h η href
    (G.geometryData_mono η hg (fun _ _ => trivial) le_rfl le_rfl) hf
  let b₁ : ℕ := hpos.choose
  have hb₁ : b ≤ b₁ := hpos.choose_spec.1
  let ε₁ : ℝ := hpos.choose_spec.2.choose
  have hposinfo := hpos.choose_spec.2.choose_spec
  have hε₁ : 0 < ε₁ := hposinfo.1
  have hε₁ε : ε₁ ≤ ε := hposinfo.2.1
  have h₁ : G.Admissible b₁ ε₁ := G.admissible_mono h hb₁ hε₁ hε₁ε
  have hU₁ := isOpen_sectorNeighborhood (G.S η) b₁ ε₁ ε₁
  have hsub₁ : sectorNeighborhood (G.S η) b₁ ε₁ ε₁ ⊆
      sectorNeighborhood (G.S η) b ε ε := sectorNeighborhood_mono (G.S η) hb₁ hε₁ε hε₁ε
  have hH₁ : G.n04PrincipalPair η b₁ ε₁ (G.pulledHeight η) (G.pulledHeightRef η) :=
    hH.restrict hU₁ hsub₁
  have hHI₁ : G.n04PrincipalPair η b₁ ε₁
      (fun z m q => (G.pulledHeight η z m q)⁻¹)
      (fun m q => (G.pulledHeightRef η m q)⁻¹) := hHI.restrict hU₁ hsub₁
  have hPpos : ∀ v : Fin 3, G.n04PrincipalPositivePair η b₁ ε₁
      (G.atomFamily η (n07aCubicPrincipalAtom v)) (G.atomRef η (n07aCubicPrincipalAtom v)) :=
    hposinfo.2.2.2
  have hP : ∀ v : Fin 3, G.n04PrincipalPair η b₁ ε₁
      (G.atomFamily η (n07aCubicPrincipalAtom v)) (G.atomRef η (n07aCubicPrincipalAtom v)) := by
    intro v
    apply G.n04Principal_pair_union η (hPpos v)
    apply G.n04PrincipalNegative_stationary_pairBounds h₁ η href
    fin_cases v <;> simp [n07aCubicPrincipalAtom, n04PrincipalNegativeStationary]
  have hVpos := G.n04PrincipalPositive_potential_pairBounds h₁ η
    (hH₁.reindex (fun m : {m : ℕ // G.Pos η m} => m.val))
    (hHI₁.reindex (fun m : {m : ℕ // G.Pos η m} => m.val)) hPpos
  have hVneg := G.n04PrincipalNegative_potential_pairBounds h₁ η href
    (G.n04PrincipalPositive_parameter_interpolation η)
    (fun m _ => Real.rpow_pos_of_pos (G.n04PrincipalPositive_sample_height_pos η m) _)
    (hH₁.reindex (fun m : {m : ℕ // G.Neg η m} => m.val))
    (hHI₁.reindex (fun m : {m : ℕ // G.Neg η m} => m.val))
  have hV : G.n04PrincipalPair η b₁ ε₁
      (G.atomFamily η .potential) (G.atomRef η .potential) :=
    G.n04Principal_pair_union η hVpos hVneg
  have hA : G.n04PrincipalPair η b₁ ε₁
      (G.atomFamily η .principalA) (G.atomRef η .principalA) := hP 0
  have hInv := G.n04Principal_inverseA_pair h₁ η href hA
  let b₂ : ℕ := hInv.choose
  have hb₂ : b₁ ≤ b₂ := hInv.choose_spec.1
  let ε₂ : ℝ := hInv.choose_spec.2.choose
  have hInvinfo := hInv.choose_spec.2.choose_spec
  have hε₂ : 0 < ε₂ := hInvinfo.1
  have hε₂ε₁ : ε₂ ≤ ε₁ := hInvinfo.2.1
  have hU₂ := isOpen_sectorNeighborhood (G.S η) b₂ ε₂ ε₂
  have hsub₂ : sectorNeighborhood (G.S η) b₂ ε₂ ε₂ ⊆
      sectorNeighborhood (G.S η) b₁ ε₁ ε₁ :=
    sectorNeighborhood_mono (G.S η) hb₂ hε₂ε₁ hε₂ε₁
  have hP₂ : ∀ v : Fin 3, G.n04PrincipalPair η b₂ ε₂
      (G.atomFamily η (n07aCubicPrincipalAtom v)) (G.atomRef η (n07aCubicPrincipalAtom v)) :=
    fun v => (hP v).restrict hU₂ hsub₂
  have hV₂ : G.n04PrincipalPair η b₂ ε₂
      (G.atomFamily η .potential) (G.atomRef η .potential) := hV.restrict hU₂ hsub₂
  refine ⟨b₂, hb₁.trans hb₂, ε₂, hε₂, hε₂ε₁.trans hε₁ε, ?_⟩
  intro i
  fin_cases i
  · exact hP₂ 0
  · exact hInvinfo.2.2.2
  · exact hP₂ 1
  · exact hP₂ 2
  · exact hV₂

end N04RealizationGauge

end ContinuousFlexibility.Analysis
