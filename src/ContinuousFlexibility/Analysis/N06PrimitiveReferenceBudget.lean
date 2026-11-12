import ContinuousFlexibility.Analysis.N06PrimitiveReferenceColumns
import ContinuousFlexibility.Analysis.N07aReferenceEnergyBudget

/-!
# The original reference inverse and its actual right-hand-side budget

The three columns are constructed in the original volume model before
calling the reference energy estimate. All constants precede the input
band and source. This uses N05 and the raw reference jets, with no N06
inverse or controlled reference coordinate hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis CanonicalGeometry
open scoped ENNReal

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

local instance n06ReferenceBudgetLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n06ReferenceBudgetLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n06ReferenceBudgetGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06ReferenceBudgetGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

theorem n06_primitiveReference_energy_outer_budget
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K) :
    ∃ A : ℝ, 0 < A ∧ ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 1 ≤ e m) ∧
      ∀ (hI : ∀ m, K.left m < K.right m) j (F : V.level (3 / 4 : ℝ) 0 b),
      n07aAngularLevelBand h.2.2.1 (3 / 4 : ℝ) 0 hI b j F = F →
      n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 →
      ∃ a : lp (fun _ : ℕ => ℝ) 2, (∀ m, 0 ≤ a m) ∧ ‖a‖ ≤ A * ‖F‖ ∧
        ∀ m, Real.sqrt (n07aAngularJetWeightSq b j) *
          (‖n07aReferenceInverseField (B := B) F m‖ +
            ‖n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
              (V.forget (3 / 4 : ℝ) 0 b F)‖) ≤
          e m * n07aVolumeWeight T K (3 / 4 : ℝ) (0 - B.lossMaterial) m * a m := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hI₀ : ∀ m, K.left m < K.right m := fun m => (h04.1.referenceBounds m).2.1
  obtain ⟨Col, hCol⟩ := n06_primitiveReference_scalarColumnVolumes
    hT hS h href (3 / 4 : ℝ) (0 - B.lossMaterial) hI₀
  obtain ⟨A, hA, e, he, he1, hbudget⟩ :=
    n07a_referenceEnergy_outer_budget h01.1.1 hT href h.2 hI₀ Col hCol
  exact ⟨A, hA, e, he, he1, fun _ => hbudget⟩

end ContinuousFlexibility.Statements
