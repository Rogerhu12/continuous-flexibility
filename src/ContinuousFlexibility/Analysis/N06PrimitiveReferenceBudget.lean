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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

local instance n06ReferenceBudgetLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n06ReferenceBudgetLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n06ReferenceBudgetUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n06ReferenceBudgetUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n06ReferenceBudgetGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06ReferenceBudgetGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

private def N06ReferenceBandBudget
    (hV : IsVolumeModel T S K V) (href : ReferenceJets D T S C L K)
    (A : ℝ) (e : ℕ → ℝ) (hI : ∀ m, K.left m < K.right m) : Prop :=
  ∀ j (F : V.level (3 / 4 : ℝ) 0 b),
    n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b j F = F →
    n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 →
    ∃ a : lp (fun _ : ℕ => ℝ) 2, (∀ m, 0 ≤ a m) ∧ ‖a‖ ≤ A * ‖F‖ ∧
      ∀ m, Real.sqrt (n07aAngularJetWeightSq b j) *
        (‖n07aReferenceInverseField (B := B) F m‖ +
          ‖n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
            (V.forget (3 / 4 : ℝ) 0 b F)‖) ≤
        e m * n07aVolumeWeight T K (3 / 4 : ℝ) (0 - B.lossMaterial) m * a m

private theorem n06_referenceBudget_fixed_columns
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : ReferenceJets D T S C L K) (h05 : N05Properties D T S C K V b B)
    (hI : ∀ m, K.left m < K.right m)
    (Col : Fin 3 → V.level (3 / 4 : ℝ) (0 - B.lossMaterial) 0)
    (hCol : ∀ i, V.forget (3 / 4 : ℝ) (0 - B.lossMaterial) 0 (Col i) =
      fun m => (n07aReferenceScalarOpenCoefficient href m (hI m) i).toLp) :
    ∃ A : ℝ, 0 < A ∧ ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 1 ≤ e m) ∧
        N06ReferenceBandBudget (B := B) h05.2.1 href A e hI :=
  n07a_referenceEnergy_outer_budget (B := B) hD hT href h05 hI Col hCol

private theorem n06_referenceBudget_actual_columns
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hI : ∀ m, K.left m < K.right m) :
    ∃ A : ℝ, 0 < A ∧ ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 1 ≤ e m) ∧
        N06ReferenceBandBudget (B := B) h.2.2.1 href A e hI := by
  have hD : IsAccumulatingProfile D := h.1.1.1.1.1.1
  exact (n06_primitiveReference_scalarColumnVolumes (B := B)
    hT hS h href (3 / 4 : ℝ) (0 - B.lossMaterial) hI).elim
      (fun Col hCol => n06_referenceBudget_fixed_columns
        (B := B) hD hT href h.2 hI Col hCol)

private theorem n06_referenceBudget_uniform_proof
    {P : Prop} {X Y : Type*} (A : X → Prop) (E₁ E₂ : Y → Prop)
    (Q : X → Y → P → Prop) (p : P)
    (h : ∃ x, A x ∧ ∃ y, E₁ y ∧ E₂ y ∧ Q x y p) :
    ∃ x, A x ∧ ∃ y, E₁ y ∧ E₂ y ∧ ∀ q : P, Q x y q :=
  h.elim (fun x hx => hx.2.elim (fun y hy =>
    ⟨x, hx.1, y, hy.1, hy.2.1, fun _ => hy.2.2⟩))

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
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hI₀ : ∀ m, K.left m < K.right m := fun m => (h04.1.referenceBounds m).2.1
  exact n06_referenceBudget_uniform_proof
    (fun A : ℝ => 0 < A) (N07aSampleSubpower T K)
    (fun e : ℕ → ℝ => ∀ m, 1 ≤ e m)
    (N06ReferenceBandBudget (B := B) h.2.2.1 href) hI₀
    (n06_referenceBudget_actual_columns (B := B) hT hS h href hI₀)

end ContinuousFlexibility.Statements
