module

public import ContinuousFlexibility.Analysis.N06NuAngularDifference
public import ContinuousFlexibility.Analysis.N06NuPhysicalRegularity
public import ContinuousFlexibility.Analysis.N06ControlledReferenceSourceNorm

/-!
# The actual nu difference as a small source in the reference chart

The physical field is the genuine current nu column minus the genuine
reference column. Its fixed compact support meets only finitely many
controlled reference pieces. The actual source formula and finite-source
construction place it in the selected original V.level, with a linear
bound in one fixed state seminorm. This theorem uses the reference chart;
it makes no assertion identifying that chart with a current chart.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- All requested angular derivatives have one common linear bound. -/
theorem n06_nuColumn_finiteAngularDifference_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (b : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z : AnnularState S × ℝ,
      z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
      stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2| ≤ 1 →
      ∀ j, j ≤ b → ∀ p ∈ annularOpen D,
        |mixedDerivative 0 j (fun q => nuColumnField D S C z q -
          nuColumnField D S C (C.referenceState, 0) q) p| ≤
            Q * (stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2|) := by
  classical
  have hchoices (i : Fin (b + 1)) := n06_nuColumn_angularDifference_bound hT hS hN01 i.val
  choose q hq hbound using hchoices
  let Q : ℝ := ∑ i : Fin (b + 1), q i
  refine ⟨Q, Finset.sum_nonneg (fun i _ => hq i), ?_⟩
  intro z hz hs hsmall j hj p hp
  let i : Fin (b + 1) := ⟨j, by omega⟩
  have hgrade : stateGrading S (j + 4) (z.1 - C.referenceState) + |z.2| ≤
      stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2| :=
    add_le_add (solve_stateGrading_monotone S (by omega) (z.1 - C.referenceState))
      (le_refl |z.2|)
  have hi : q i ≤ Q := Finset.single_le_sum (fun k _ => hq k) (Finset.mem_univ i)
  calc
    _ ≤ q i * (stateGrading S (j + 4) (z.1 - C.referenceState) + |z.2|) :=
      hbound i z hz hs (hgrade.trans hsmall) p hp
    _ ≤ q i * (stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2|) :=
      mul_le_mul_of_nonneg_left hgrade (hq i)
    _ ≤ _ := mul_le_mul_of_nonneg_right hi
      (add_nonneg (apply_nonneg _ _) (abs_nonneg _))

/-- The actual nu difference has the physical regularity needed by the
fixed-support source constructor. -/
private theorem n06_nuDifference_source_regular
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    let f : PolarPoint → ℝ := fun p => nuColumnField D S C z p -
      nuColumnField D S C (C.referenceState, 0) p
    ContDiff ℝ ∞ f ∧ Function.Periodic f (0, Real.pi) ∧
      (∀ p : PolarPoint, f (p.1, -p.2) = f p) ∧
      (∀ r, r ∉ tsupport D.chi → ∀ θ, f (r, θ) = 0) := by
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  refine ⟨(n06_nuColumn_contDiff hT hS h01 hz hs).sub
    (n06_nuColumn_contDiff hT hS h01 href hsector),
    (n06_nuColumn_periodic hT hS h01 z).sub
      (n06_nuColumn_periodic hT hS h01 (C.referenceState, 0)), ?_, ?_⟩
  · intro p
    exact congrArg₂ (fun a b : ℝ => a - b)
      (n06_nuColumn_even hT hS h01 z p)
      (n06_nuColumn_even hT hS h01 (C.referenceState, 0) p)
  · intro r hr θ
    exact (congrArg₂ (fun a b : ℝ => a - b)
      (n06_nuColumn_zero_off_tsupport hT hS h01 z (p := (r, θ)) hr)
      (n06_nuColumn_zero_off_tsupport hT hS h01
        (C.referenceState, 0) (p := (r, θ)) hr)).trans (sub_self 0)

def N06ReferenceChartNuDifferenceBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (V : VolumeModelData S K) (base : ℕ) (ε γ t : ℝ)
    (b : ℕ) (Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∃ F : V.level γ t b,
      (∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m
          (fun p => nuColumnField D S C z p -
            nuColumnField D S C (C.referenceState, 0) p)) ∧
      ‖F‖ ≤ Q * (stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2|)

set_option backward.isDefEq.respectTransparency true

theorem n06_source_family_norm_bound
    {X A Y : Type*} [Norm Y]
    (P₁ P₂ P₃ P₄ : A → Prop) (Jets : ℝ → A → Prop) (Source : A → Y → Prop)
    (field : X → A) (size : X → ℝ) (Ad₁ Ad₂ : X → Prop)
    (hsize : ∀ x, 0 ≤ size x)
    (hregular : ∀ x, Ad₁ x → Ad₂ x →
      P₁ (field x) ∧ P₂ (field x) ∧ P₃ (field x) ∧ P₄ (field x))
    (hjets : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, Ad₁ x → Ad₂ x → size x ≤ 1 →
      Jets (B * size x) (field x))
    (hsource : ∃ M : ℝ, 0 ≤ M ∧ ∀ a δ, 0 ≤ δ →
      P₁ a → P₂ a → P₃ a → P₄ a → Jets δ a →
      ∃ F : Y, Source a F ∧ ‖F‖ ≤ M * δ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ x, Ad₁ x → Ad₂ x → size x ≤ 1 →
      ∃ F : Y, Source (field x) F ∧ ‖F‖ ≤ Q * size x := by
  obtain ⟨M, hM, hconstruct⟩ := hsource
  obtain ⟨B, hB, hbound⟩ := hjets
  refine ⟨M * B, mul_nonneg hM hB, ?_⟩
  intro x hx₁ hx₂ hsmall
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hregular x hx₁ hx₂
  obtain ⟨F, hF, hFnorm⟩ := hconstruct (field x) (B * size x)
    (mul_nonneg hB (hsize x)) h₁ h₂ h₃ h₄ (hbound x hx₁ hx₂ hsmall)
  exact ⟨F, hF, hFnorm.trans_eq (mul_assoc M B (size x)).symm⟩

/-- An actual element of the same source scale, with the reference source
transform written explicitly in its representative identity. -/
theorem n06Volume_exists_referenceChart_nuDifference
    {R : ReturnEquationData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hV : IsVolumeModel T S K V)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (γ t : ℝ) (b : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      N06ReferenceChartNuDifferenceBound D S C K V base ε γ t b Q := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have hb : RadialTrueBorder D := h01.1.2.2.2.1
  have hsource := n06Volume_controlled_reference_source_norm
    (D := D) (T := T) (S := S) (C := C) (K := K) (V := V)
    hT hV h hcoordinates γ t b hb.2.1 (fun r hr => (hb.2.2.1 hr).1)
  have hjets := n06_nuColumn_finiteAngularDifference_bound
    (D := D) (T := T) (S := S) (C := C) hT hS h01 b
  exact n06_source_family_norm_bound
    (X := AnnularState S × ℝ) (A := PolarPoint → ℝ) (Y := V.level γ t b)
    (fun f => ContDiff ℝ ∞ f)
    (fun f => Function.Periodic f (0, Real.pi))
    (fun f => ∀ p : PolarPoint, f (p.1, -p.2) = f p)
    (fun f => ∀ r, r ∉ tsupport D.chi → ∀ θ, f (r, θ) = 0)
    (fun δ f => ∀ j, j ≤ b → ∀ p ∈ annularOpen D,
      |mixedDerivative 0 j f p| ≤ δ)
    (fun f F => ∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m f)
    (fun z p => nuColumnField D S C z p - nuColumnField D S C (C.referenceState, 0) p)
    (fun z => stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2|)
    (fun z => z ∈ stateNeighborhood S C base ε) (fun z => stateSector S z.1)
    (fun z => add_nonneg (apply_nonneg (stateGrading S (b + 4)) (z.1 - C.referenceState))
      (abs_nonneg z.2))
    (fun z hz hs => n06_nuDifference_source_regular
      (D := D) (T := T) (S := S) (C := C) hT hS h01 (z := z) hz hs)
    hjets hsource

end ContinuousFlexibility.Statements
