module

public import ContinuousFlexibility.Analysis.N04SourceColumnsDeterminant
public import ContinuousFlexibility.Analysis.N04SourceColumnsSign
public import ContinuousFlexibility.Analysis.N04SourceColumnsReferences
public import ContinuousFlexibility.Analysis.N04SourceColumnsSmallness
public import ContinuousFlexibility.Analysis.N04SourceColumnsReciprocal

/-!
# The source factor and its reciprocal

The actual inverse-chart determinant is a first-jet polynomial. Its fixed
sign converts its absolute value to a fixed scalar multiple. The supplied
pulled height then gives the source factor, and one zeroth-order relative
estimate selects a single neighborhood for all reciprocal derivatives.
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

theorem sourceColumns_absDeterminant_data {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (hG : G.GeometryData η (fun _ => True) b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ b' ε', b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      G.Data η (fun _ => True) b' ε'
        (fun z m p => |G.sourceColumnsInverseDeterminant η z m p|)
        (fun m p => |G.sourceColumnsInverseDeterminantRef η m p|) ∧
      N04SourceReferenceData G.W.U (G.V η).cell
        (fun m p => |G.sourceColumnsInverseDeterminantRef η m p|) := by
  have hd := G.sourceColumns_inverseDeterminant_data η hA hG href
  let b' : ℕ := hd.choose
  let ε' : ℝ := hd.choose_spec.choose
  have hdata := hd.choose_spec.choose_spec
  have hs := G.sourceColumns_inverseDeterminant_fixedSign η hA hG href
  let σ : ℕ → ℝ := hs.choose
  have hE := (G.cost_nonneg η).2.2
  have hH := (G.cost_nonneg η).2.1
  have hσ : ∃ A : ℝ, 0 < A ∧ ∀ m,
      |σ m| ≤ A * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A := by
    refine ⟨1, zero_lt_one, fun m => ?_⟩
    rw [hs.choose_spec.1 m, one_mul, Real.rpow_one]
    exact hE m
  have hc := hdata.2.2.2.sourceColumns_constMul hE hH σ hσ
  have hr := (G.sourceColumns_inverseDeterminantRef_data η href).sourceColumns_constMul
    hE σ hσ
  refine ⟨b', ε', hdata.1, hdata.2.1, hdata.2.2.1, ?_, ?_⟩
  · exact hc.sourceColumns_congr
      (fun z hz m p hp => (hs.choose_spec.2.1 z
        (sectorNeighborhood_mono (G.S η) hdata.1 hdata.2.2.1 hdata.2.2.1 hz) m p hp).symm)
      (fun m p hp => (hs.choose_spec.2.2 m p hp).symm)
  · exact hr.sourceColumns_congr (fun m p hp => (hs.choose_spec.2.2 m p hp).symm)

theorem sourceColumns_factor_data {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (hG : G.GeometryData η (fun _ => True) b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ b' ε', b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      G.Data η (fun _ => True) b' ε'
        (G.atomFamily η .sourceFactor) (G.atomRef η .sourceFactor) := by
  have hdet := G.sourceColumns_absDeterminant_data η hA hG href
  let b₁ : ℕ := hdet.choose
  let ε₁ : ℝ := hdet.choose_spec.choose
  have hd := hdet.choose_spec.choose_spec
  have hG₁ := G.geometryData_mono η hG (fun _ h => h) hd.1 hd.2.2.1
  have hh₀ := G.sourceColumns_pulledHeightRef_data η hA href hd.2.2.2.2
  have hp := CurrentJetDataOn.sourceColumns_mul G.W.radial.1
    (isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT) hd.2.1
    (G.cost_nonneg η).2.2 (G.sourceColumns_interpolation η)
    hG₁.2 hd.2.2.2.1 hh₀ hd.2.2.2.2
  let b' : ℕ := hp.choose
  let ε' : ℝ := hp.choose_spec.choose
  have hp' := hp.choose_spec.choose_spec
  have hb : b ≤ b' := hd.1.trans hp'.1
  have hε : ε' ≤ ε := hp'.2.2.1.trans hd.2.2.1
  refine ⟨b', ε', hb, hp'.2.1, hε, ?_⟩
  exact hp'.2.2.2.sourceColumns_congr
    (fun z hz m p hq => (G.sourceColumns_factor_eq_absDeterminant η hA hG
      (sectorNeighborhood_mono (G.S η) hb hε hε hz) m hq).symm)
    (fun m p hp => (G.sourceColumns_factorRef_eq_absDeterminant η hA href m hp).symm)

/-- The inverse reference atom supplies the only zeroth reciprocal
coefficient estimate used to choose the current neighborhood. -/
theorem sourceColumns_factorRef_inverse_bound
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ A : ℝ, 0 < A ∧ ∀ m p, p ∈ unitStrip →
      (G.atomRef η .sourceFactor m p)⁻¹ ≤
        A * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A := by
  have h := (n04SourceReferenceData_of_referenceJets href .sourceFactorInverse).2 0
  refine ⟨h.choose, h.choose_spec.1, fun m p hp => ?_⟩
  have hb := h.choose_spec.2 m p hp 0 0 le_rfl
  simp only [spaces_mixedDerivative_zero] at hb
  exact (le_abs_self _).trans hb

/-- Both factor atoms on one neighborhood, selected before all orders. -/
theorem sourceColumns_factor_pair_data {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (hG : G.GeometryData η (fun _ => True) b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ b' ε', b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      G.Data η (fun _ => True) b' ε'
        (G.atomFamily η .sourceFactor) (G.atomRef η .sourceFactor) ∧
      G.Data η (fun _ => True) b' ε'
        (G.atomFamily η .sourceFactorInverse) (G.atomRef η .sourceFactorInverse) := by
  have hf := G.sourceColumns_factor_data η hA hG href
  let b₁ : ℕ := hf.choose
  let ε₁ : ℝ := hf.choose_spec.choose
  have hf₁ := hf.choose_spec.choose_spec
  have hD := G.W.radial.1
  have hT := isMaterialData_enlargedMaterialData hD G.W.hT
  have hE := (G.cost_nonneg η).2.2
  have hsmall := hf₁.2.2.2.sourceColumns_half_reference hD hT hf₁.2.1
    (fun m p hp => G.sourceColumns_factorRef_pos η hA m hp)
    (G.sourceColumns_factorRef_inverse_bound η href)
  let b₂ : ℕ := hsmall.choose
  let ε₂ : ℝ := hsmall.choose_spec.choose
  let A : ℝ := hsmall.choose_spec.choose_spec.choose
  have hs := hsmall.choose_spec.choose_spec.choose_spec
  have hf₂ := hf₁.2.2.2.mono (fun _ h => h) hs.1 hs.2.2.1
    (G.cost_nonneg η).1 (G.cost_nonneg η).2.1
  have hf₀ := n04SourceReferenceData_of_referenceJets href .sourceFactor
  have hi₀ := n04SourceReferenceData_of_referenceJets href .sourceFactorInverse
  have hi := CurrentJetDataOn.sourceColumns_inv_of_bound hD hT
    (G.sourceColumns_interpolation η) hf₂ hf₀ hi₀ hs.2.1 hE
    (2 * A) A (mul_nonneg (by norm_num) hs.2.2.2.1.le) hs.2.2.2.1.le
    (fun z hz m p hp => (hs.2.2.2.2 z hz m p hp).2)
  let b' : ℕ := hi.choose
  let ε' : ℝ := hi.choose_spec.choose
  have hi' := hi.choose_spec.choose_spec
  refine ⟨b', ε', hf₁.1.trans (hs.1.trans hi'.1), hi'.2.1,
    hi'.2.2.1.trans (hs.2.2.1.trans hf₁.2.2.1), ?_, ?_⟩
  · exact hf₂.mono (fun _ h => h) hi'.1 hi'.2.2.1
      (G.cost_nonneg η).1 (G.cost_nonneg η).2.1
  · exact hi'.2.2.2

end N04RealizationGauge

end ContinuousFlexibility.Analysis
