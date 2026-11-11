import ContinuousFlexibility.Radial.PositiveBufferFullForm
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Lifting the given full inverse to the genuine energy domain

The inverse supplied in R09 is used on its admissible scalar sources. Its
energy coordinates are uniquely determined by the actual field, so lifting
it preserves linearity. No new inverse or invertibility assumption is
introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology InnerProductSpace

def positiveBufferSourceProjection (bordered : Bool) :
    (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ) :=
  if bordered then ContinuousLinearMap.id ℝ (RadialL2 × ℝ)
  else (ContinuousLinearMap.inl ℝ RadialL2 ℝ).comp
    (ContinuousLinearMap.fst ℝ RadialL2 ℝ)

@[simp] theorem positiveBufferSourceProjection_apply (bordered : Bool) (F : RadialL2 × ℝ) :
    positiveBufferSourceProjection bordered F = (F.1, if bordered then F.2 else 0) := by
  cases bordered <;> rfl

theorem positiveBufferSourceProjection_admissible (bordered : Bool) (F : RadialL2 × ℝ) :
    bordered = false → (positiveBufferSourceProjection bordered F).2 = 0 := by
  intro hb
  simp only [positiveBufferSourceProjection_apply, hb, Bool.false_eq_true, ite_false]

theorem positiveBufferSourceProjection_norm_le (bordered : Bool) (F : RadialL2 × ℝ) :
    ‖positiveBufferSourceProjection bordered F‖ ≤ ‖F‖ := by
  cases bordered with
  | false =>
    simp only [positiveBufferSourceProjection_apply, Bool.false_eq_true, ite_false,
      Prod.norm_def, norm_zero, max_eq_left (norm_nonneg F.1)]
    exact le_max_left _ _
  | true =>
    simp only [positiveBufferSourceProjection_apply, ite_true, Prod.mk.eta, le_refl]

theorem positiveBufferSourceProjection_eq (bordered : Bool) (F : RadialL2 × ℝ)
    (hF : bordered = false → F.2 = 0) : positiveBufferSourceProjection bordered F = F := by
  cases bordered with
  | false =>
    have hs := hF rfl
    simp only [positiveBufferSourceProjection_apply, Bool.false_eq_true, ite_false, ← hs,
      Prod.mk.eta]
  | true => simp only [positiveBufferSourceProjection_apply, ite_true, Prod.mk.eta]

theorem positiveBufferStatePairing_project_source (V : ℝ → ℝ) (bordered : Bool)
    (F : RadialL2 × ℝ) (W : PositiveBufferBorderedEnergy V bordered) :
    positiveBufferStatePairing (positiveBufferSourceProjection bordered F)
        (positiveBufferBorderedState V bordered W) =
      positiveBufferStatePairing F (positiveBufferBorderedState V bordered W) := by
  cases bordered with
  | false =>
    have hs := W.property rfl
    simp only [positiveBufferStatePairing_apply, positiveBufferSourceProjection_apply,
      Bool.false_eq_true, ite_false, positiveBufferBorderedState_apply, hs, mul_zero]
  | true => simp only [positiveBufferSourceProjection_apply, ite_true, Prod.mk.eta]

theorem positiveBuffer_fullGraph_energy_lift {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (g : RadialL2) (bordered : Bool)
    (U F : RadialL2 × ℝ) (hU : BorderedFullGraph V g bordered U F) :
    ∃ W : PositiveBufferBorderedEnergy V bordered,
      positiveBufferBorderedState V bordered W = U := by
  cases bordered with
  | false =>
    simp only [BorderedFullGraph, Bool.false_eq_true, ite_false] at hU
    obtain ⟨e, he⟩ := positiveBuffer_exists_energy_of_weak hreal hU.1
    refine ⟨⟨(e, U.2), fun _ => hU.2.1⟩, ?_⟩
    exact Prod.ext he rfl
  | true =>
    simp only [BorderedFullGraph, ite_true] at hU
    obtain ⟨e, he⟩ := positiveBuffer_exists_energy_of_weak hreal hU.1
    refine ⟨⟨(e, U.2), fun hb => Bool.noConfusion hb⟩, ?_⟩
    exact Prod.ext he rfl

def positiveBufferFullGraphEnergyLift {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (g : RadialL2) (bordered : Bool)
    (U F : RadialL2 × ℝ) (hU : BorderedFullGraph V g bordered U F) :
    PositiveBufferBorderedEnergy V bordered :=
  Classical.choose (positiveBuffer_fullGraph_energy_lift hreal g bordered U F hU)

@[simp] theorem positiveBufferFullGraphEnergyLift_state {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (g : RadialL2) (bordered : Bool)
    (U F : RadialL2 × ℝ) (hU : BorderedFullGraph V g bordered U F) :
    positiveBufferBorderedState V bordered (positiveBufferFullGraphEnergyLift hreal g bordered U F hU) = U :=
  Classical.choose_spec (positiveBuffer_fullGraph_energy_lift hreal g bordered U F hU)

def positiveBufferLiftedInverse {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (g : RadialL2) (bordered : Bool)
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (hH : ∀ F, (bordered = false → F.2 = 0) → BorderedFullGraph V g bordered (H F) F) :
    (RadialL2 × ℝ) →ₗ[ℝ] PositiveBufferBorderedEnergy V bordered := by
  let L (F : RadialL2 × ℝ) : PositiveBufferBorderedEnergy V bordered :=
    positiveBufferFullGraphEnergyLift hreal g bordered
      (H (positiveBufferSourceProjection bordered F)) (positiveBufferSourceProjection bordered F)
      (hH _ (positiveBufferSourceProjection_admissible bordered F))
  exact
    { toFun := L
      map_add' := by
        intro F K
        apply positiveBufferBorderedState_injective V bordered
        simp only [map_add, L, positiveBufferFullGraphEnergyLift_state]
      map_smul' := by
        intro a F
        apply positiveBufferBorderedState_injective V bordered
        simp only [map_smul, L, positiveBufferFullGraphEnergyLift_state, RingHom.id_apply] }

@[simp] theorem positiveBufferLiftedInverse_state {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (g : RadialL2) (bordered : Bool)
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (hH : ∀ F, (bordered = false → F.2 = 0) → BorderedFullGraph V g bordered (H F) F)
    (F : RadialL2 × ℝ) :
    positiveBufferBorderedState V bordered (positiveBufferLiftedInverse hreal g bordered H hH F) =
      H (positiveBufferSourceProjection bordered F) :=
  positiveBufferFullGraphEnergyLift_state hreal g bordered _ _ _

theorem positiveBufferLiftedInverse_form {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V) (g : RadialL2) (bordered : Bool)
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (hH : ∀ F, (bordered = false → F.2 = 0) → BorderedFullGraph V g bordered (H F) F)
    (F : RadialL2 × ℝ) (W : PositiveBufferBorderedEnergy V bordered) :
    positiveBufferBorderedForm V hV g bordered (positiveBufferLiftedInverse hreal g bordered H hH F) W =
      positiveBufferStatePairing F (positiveBufferBorderedState V bordered W) := by
  have hgraph : BorderedFullGraph V g bordered
      (positiveBufferBorderedState V bordered (positiveBufferLiftedInverse hreal g bordered H hH F))
      (positiveBufferSourceProjection bordered F) := by
    rw [positiveBufferLiftedInverse_state]
    exact hH _ (positiveBufferSourceProjection_admissible bordered F)
  exact (positiveBufferBorderedForm_of_fullGraph hreal hV g bordered _ _ hgraph W).trans
    (positiveBufferStatePairing_project_source V bordered F W)

theorem positiveBufferLiftedInverse_state_bound {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (g : RadialL2) (bordered : Bool)
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (hH : ∀ F, (bordered = false → F.2 = 0) → BorderedFullGraph V g bordered (H F) F)
    {B₀ : ℝ} (hB : ‖H‖ ≤ B₀) (F : RadialL2 × ℝ) :
    ‖positiveBufferBorderedState V bordered (positiveBufferLiftedInverse hreal g bordered H hH F)‖ ≤
      B₀ * ‖F‖ := by
  rw [positiveBufferLiftedInverse_state]
  exact (H.le_opNorm _).trans (mul_le_mul hB
    (positiveBufferSourceProjection_norm_le bordered F) (norm_nonneg _)
    ((norm_nonneg H).trans hB))

end ContinuousFlexibility.Radial
