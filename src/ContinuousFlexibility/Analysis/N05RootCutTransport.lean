import ContinuousFlexibility.Analysis.N05ReferenceNullTransport

/-!
# Root-to-cut identities for the actual reference chart

Both physical orientations have the same inward optical displacement.
At the root the two null coordinates coincide with the actual angular
chart.  At the cut their difference is the fixed Tricomi displacement.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

theorem n05_cut_physical_root_mem
    (h04 : N04Properties D T S C L K base loss ε) (m : ℕ) (right : Bool) :
    (if right then C.right m else C.left m) ∈
      Icc (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)) := by
  rcases h04 with ⟨_, _, _, hpieces, _, _, _, _, _, _, _, hcuts, _⟩
  obtain ⟨_, _, hleft, hright, _⟩ := hcuts m
  cases right with
  | false =>
    change C.left m ∈ Icc (K.physicalLeft (K.cutPair m).1) (K.physicalRight (K.cutPair m).1)
    rw [← hleft]
    exact ⟨le_rfl, (hpieces (K.cutPair m).1).1.le⟩
  | true =>
    change C.right m ∈ Icc (K.physicalLeft (K.cutPair m).2) (K.physicalRight (K.cutPair m).2)
    rw [← hright]
    exact ⟨(hpieces (K.cutPair m).2).1.le, le_rfl⟩

theorem n05_cut_physical_cut_mem
    (h04 : N04Properties D T S C L K base loss ε) (m : ℕ) (right : Bool) :
    K.physicalRight (K.cutPair m).1 ∈
      Icc (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)) := by
  rcases h04 with ⟨_, _, _, hpieces, _, _, _, _, _, _, _, hcuts, _⟩
  have hmeet := (hcuts m).2.2.2.2.1
  cases right with
  | false => exact ⟨(hpieces (K.cutPair m).1).1.le, le_rfl⟩
  | true =>
    change K.physicalRight (K.cutPair m).1 ∈
      Icc (K.physicalLeft (K.cutPair m).2) (K.physicalRight (K.cutPair m).2)
    rw [hmeet]
    exact ⟨le_rfl, (hpieces (K.cutPair m).2).1.le⟩

theorem n05_cut_reference_root_image
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) (θ : ℝ) :
    (K.chart (C.referenceState, 0)
      (if right then (K.cutPair m).2 else (K.cutPair m).1)
      (if right then C.right m else C.left m, θ)).1 = 0 := by
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, _, _, _, _, _, _, _, _, hcuts, _⟩
  have hneg : K.positive (if right then (K.cutPair m).2 else (K.cutPair m).1) = false := by
    cases right
    · exact (hcuts m).1
    · exact (hcuts m).2.1
  have hroots := h.1.1.1.2.2.2.1.2.1 m
  have hd : deriv D.w (if right then C.right m else C.left m) = 0 := by
    cases right
    · exact hroots.1
    · exact hroots.2.1
  exact n05_negative_reference_root_image hT hS h hneg
    (x := (if right then C.right m else C.left m, θ))
    (n05_cut_physical_root_mem h.2.2.2.2 m right) hd

/-- Optical transport from the cut to either actual physical root has the
same inward displacement for the two half orientations. -/
theorem n05_cut_reference_root_transport
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {σ : ℝ} (hσ : σ ^ 2 = 1) (θ : ℝ) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let root := if right then C.right m else C.left m
    let Ψ := K.chart (C.referenceState, 0) i
    n05NullCoordinate Ψ σ (K.physicalRight (K.cutPair m).1, θ) =
      (Ψ (root, θ + σ * opticalTravel D.w (K.physicalLeft i) (K.physicalRight i))).2 := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then C.right m else C.left m
  let Ψ := K.chart (C.referenceState, 0) i
  let orientation : ℝ := if right then -1 else 1
  let travel := opticalTravel D.w (K.physicalLeft i) (K.physicalRight i)
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, _, _, _, _, _, _, _, _, hcuts, _⟩
  obtain ⟨_, _, hleft, hright, hmeet, _⟩ := hcuts m
  have hshift : θ + (σ * orientation) *
        opticalTravel D.w (K.physicalLeft i) (K.physicalRight (K.cutPair m).1) -
      (σ * orientation) * opticalTravel D.w (K.physicalLeft i) root = θ + σ * travel := by
    cases right with
    | false =>
      change θ + (σ * 1) * opticalTravel D.w (K.physicalLeft (K.cutPair m).1)
          (K.physicalRight (K.cutPair m).1) -
        (σ * 1) * opticalTravel D.w (K.physicalLeft (K.cutPair m).1) (C.left m) =
          θ + σ * opticalTravel D.w (K.physicalLeft (K.cutPair m).1)
            (K.physicalRight (K.cutPair m).1)
      rw [← hleft]
      simp only [mul_one, opticalTravel, intervalIntegral.integral_same, mul_zero, sub_zero]
    | true =>
      change θ + (σ * (-1)) * opticalTravel D.w (K.physicalLeft (K.cutPair m).2)
          (K.physicalRight (K.cutPair m).1) -
        (σ * (-1)) * opticalTravel D.w (K.physicalLeft (K.cutPair m).2) (C.right m) =
          θ + σ * opticalTravel D.w (K.physicalLeft (K.cutPair m).2)
            (K.physicalRight (K.cutPair m).2)
      rw [hmeet, ← hright]
      simp only [opticalTravel, intervalIntegral.integral_same, mul_zero, add_zero]
      ring
  have ht := n05_cut_reference_null_transport hT hS h m right hσ
    (n05_cut_physical_cut_mem h.2.2.2.2 m right)
    (n05_cut_physical_root_mem h.2.2.2.2 m right) θ
  change n05NullCoordinate Ψ σ (K.physicalRight (K.cutPair m).1, θ) =
    n05NullCoordinate Ψ σ (root, θ + (σ * orientation) *
        opticalTravel D.w (K.physicalLeft i) (K.physicalRight (K.cutPair m).1) -
      (σ * orientation) * opticalTravel D.w (K.physicalLeft i) root) at ht
  rw [hshift] at ht
  have hroot := n05_cut_reference_root_image hT hS h m right (θ + σ * travel)
  change (Ψ (root, θ + σ * travel)).1 = 0 at hroot
  calc
    _ = n05NullCoordinate Ψ σ (root, θ + σ * travel) := ht
    _ = _ := by
      simp only [n05NullCoordinate, hroot, n05TricomiTime_zero, mul_zero, add_zero]

/-- The actual angular chart at either root satisfies the exact symmetric
finite-difference identity determined by the common canonical cut radius. -/
theorem n05_cut_reference_root_difference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) (θ : ℝ) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let root := if right then C.right m else C.left m
    let Ψ := K.chart (C.referenceState, 0) i
    let travel := opticalTravel D.w (K.physicalLeft i) (K.physicalRight i)
    (Ψ (root, θ + travel)).2 - (Ψ (root, θ - travel)).2 =
      2 * n05TricomiTime (K.cutRadius m) := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then C.right m else C.left m
  let Ψ := K.chart (C.referenceState, 0) i
  let travel := opticalTravel D.w (K.physicalLeft i) (K.physicalRight i)
  have hp : n05NullCoordinate Ψ 1 (K.physicalRight (K.cutPair m).1, θ) =
      (Ψ (root, θ + travel)).2 := by
    simpa only [one_mul] using n05_cut_reference_root_transport hT hS h m right
      (σ := 1) (by norm_num) θ
  have hn : n05NullCoordinate Ψ (-1) (K.physicalRight (K.cutPair m).1, θ) =
      (Ψ (root, θ - travel)).2 := by
    simpa only [neg_one_mul, sub_eq_add_neg] using n05_cut_reference_root_transport hT hS h m right
      (σ := -1) (by norm_num) θ
  have hi : i = (K.cutPair m).1 ∨ i = (K.cutPair m).2 := by
    cases right
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hc := n05_cut_reference_image hT hS h m hi θ
  change (Ψ (K.physicalRight (K.cutPair m).1, θ)).1 = K.cutRadius m at hc
  change (Ψ (root, θ + travel)).2 - (Ψ (root, θ - travel)).2 = _
  rw [← hp, ← hn]
  simp only [n05NullCoordinate, hc]
  ring

end ContinuousFlexibility.Statements
