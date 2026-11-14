import ContinuousFlexibility.Analysis.N03CoefficientProbeSelection

/-!
# One ordinary state neighborhood for the corrected coefficient jets

Translation by the reference state identifies the linear sector with
the actual sector states. The sector grading is exactly the restricted
state grading. A single half-radius choice controls the sum of the state
and scalar seminorms and transports every component and derivative order
without altering the derivative loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

private theorem restricted_pairGrading_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (W : Submodule ℝ E) (n : ℕ) (v : W × ℝ) :
    pairGrading (fun k => (p k).comp W.subtype) realGrading n v =
      p n v.1.val + |v.2| := by
  simp only [pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply,
    realGrading, coe_normSeminorm, Real.norm_eq_abs]

private theorem affine_pairGrading_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (n : ℕ) (z : E × ℝ) (x₀ : E) :
    pairGrading p realGrading n (z - (x₀, 0)) =
      p n (z.1 - x₀) + |z.2| := by
  simp only [pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Prod.fst_sub, Prod.snd_sub,
    sub_zero, realGrading, coe_normSeminorm, Real.norm_eq_abs]

private theorem common_state_ball_of_sector_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (W : Submodule ℝ E) (x₀ : E)
    (base : ℕ) {ε : ℝ} (hε : 0 < ε) (hp : Monotone p) (hx₀ : x₀ ∈ W)
    (Ω : ℕ → Set PolarPoint) (value : ℕ → ℕ → ℕ → E × ℝ → PolarPoint → ℝ)
    (h : ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ m a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ v : W × ℝ, p base v.1.val < ε ∧ |v.2| < ε →
      pairGrading (fun k => (p k).comp W.subtype) realGrading low v < δ →
      ∀ q ∈ Ω m, value m a b (x₀ + v.1.val, v.2) q ≤
        B * (1 + pairGrading (fun k => (p k).comp W.subtype) realGrading (a + b + loss) v)) :
    ∃ loss base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ z : E × ℝ,
        p base' (z.1 - x₀) < ε' ∧ |z.2| < ε' → z.1 ∈ W →
        ∀ q ∈ Ω m, value m a b z q ≤
          B * (1 + pairGrading p realGrading (a + b + loss) (z - (x₀, 0))) := by
  obtain ⟨loss, low, δ, hδ, hbound⟩ := h
  let base' := max base low
  let ε' := min ε (δ / 2)
  have hε' : 0 < ε' := lt_min hε (half_pos hδ)
  have hεold : ε' ≤ ε := min_le_left _ _
  have hεδ : ε' ≤ δ / 2 := min_le_right _ _
  refine ⟨loss, base', ε', le_max_left _ _, hε', hεold, ?_⟩
  intro m a b
  obtain ⟨B, hB, hestimate⟩ := hbound m a b
  refine ⟨B, hB, ?_⟩
  intro z hz hs q hq
  let v : W × ℝ := (⟨z.1 - x₀, W.sub_mem hs hx₀⟩, z.2)
  have hsector : p base v.1.val < ε ∧ |v.2| < ε :=
    ⟨((hp (le_max_left base low) _).trans_lt hz.1).trans_le hεold,
      hz.2.trans_le hεold⟩
  have hv : pairGrading (fun k => (p k).comp W.subtype) realGrading low v < δ := by
    rw [restricted_pairGrading_apply]
    have hstate : p low (z.1 - x₀) < δ / 2 :=
      ((hp (le_max_right base low) _).trans_lt hz.1).trans_le hεδ
    have hscalar : |z.2| < δ / 2 := hz.2.trans_le hεδ
    change p low (z.1 - x₀) + |z.2| < δ
    linarith only [hstate, hscalar]
  have he : (x₀ + v.1.val, v.2) = z := by
    apply Prod.ext
    · change x₀ + (z.1 - x₀) = z.1
      abel
    · rfl
  have hweight : pairGrading (fun k => (p k).comp W.subtype) realGrading (a + b + loss) v =
      pairGrading p realGrading (a + b + loss) (z - (x₀, 0)) := by
    rw [restricted_pairGrading_apply, affine_pairGrading_apply]
  have hresult := hestimate v hsector hv q hq
  rw [he, hweight] at hresult
  exact hresult

def N03CorrectedCoefficientStateBoundAtOrder
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base loss : ℕ) (ε : ℝ)
    (m a b : ℕ) (B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      n03CoefficientCorrectionJet D S C L a b z q ≤
        B * (1 + pairGrading (stateGrading S) realGrading (a + b + loss)
          (z - (C.referenceState, 0)))

/-- Actual sector states in one ordinary neighborhood satisfy all
corrected coefficient bounds. The neighborhood precedes every component
and derivative order, and the sector-to-state transport adds no loss. -/
theorem n03_correctedCoefficient_commonNeighborhood_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∃ outLoss base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        N03CorrectedCoefficientStateBoundAtOrder D S C L base' outLoss ε' m a b B :=
  common_state_ball_of_sector_bound
    (p := stateGrading S) (W := stateSectorSubmodule S) (x₀ := C.referenceState)
    base hN01.2.1 (stateGrading_monotone S) hN01.2.2.1.stateSector
    (Ω := fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (value := fun _ a b z q => n03CoefficientCorrectionJet D S C L a b z q)
    (n03_correctedCoefficient_fixed_loss
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K)
      (base := base) (loss := loss) (ε := ε) hS hT hN01 hN02 hN03 hA hB)

end ContinuousFlexibility.Analysis
