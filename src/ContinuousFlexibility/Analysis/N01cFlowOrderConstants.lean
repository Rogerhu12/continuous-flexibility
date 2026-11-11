import ContinuousFlexibility.Analysis.N01cCosineSpeedPrefixBounds
import ContinuousFlexibility.Analysis.N01cActualFlowSmoothDirections

/-!
# Finite constants and the actual positive angular induction property

The state base never occurs in the finite choices below. Parameter
losses are uniformized before the spatial order, and spatial constants
are uniformized afterwards. The induction property is stated for the
canonical genuine angular state tower of the original flow.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

/-- Transport complete offset families while allowing the scalar
constant to change. This keeps concrete analytic indices opaque. -/
theorem n01c_transform_offset_constants
    (P Q : ℕ → ℕ → ℝ → Prop)
    (hP : ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ P d s B)
    (hstep : ∀ d s B, 0 < B → P d s B →
      ∃ C : ℝ, 0 < C ∧ Q d s C) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ Q d s C := by
  obtain ⟨d, hd⟩ := hP
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hd s
  exact hstep d s B hB hb

/-- Uniformizing finitely many parameter offsets preserves one common
base and places the selected offset before the spatial order. -/
theorem n01c_finite_offsets_uniform {I : Type*} [Fintype I]
    (P : I → ℕ → ℕ → ℝ → Prop) (loss : ℕ)
    (hmono : ∀ i s a b A B, a ≤ b → 0 < A → A ≤ B →
      P i s a A → P i s b B)
    (hP : ∀ i, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ P i s (s + loss + d) B) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i, P i s (s + d) B := by
  classical
  choose d hd using hP
  let offset : ℕ := loss + ∑ i, d i
  refine ⟨offset, fun s => ?_⟩
  choose c hc hcb using (fun i => hd i s)
  let B : ℝ := 1 + ∑ i, c i
  have hsum : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ => (hc i).le)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, fun i => ?_⟩
  have hdi : d i ≤ ∑ j, d j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hci : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
  exact hmono i s _ _ _ _ (by dsimp only [offset]; omega) (hc i) hci (hcb i)

/-- A convenient strict positive parameter prefix for induction. -/
theorem n01c_strict_positive_prefix
    (P : ℕ → ℕ → ℕ → ℝ → Prop) (N loss : ℕ)
    (hmono : ∀ k s a b A B, a ≤ b → 0 < A → A ≤ B →
      P k s a A → P k s b B)
    (hP : ∀ k, k < N → 0 < k →
      ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ P k s (s + loss + d) B) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k, k < N → 0 < k → P k s (s + d) B := by
  classical
  let I := {k : Fin N // 0 < (k : ℕ)}
  have hfinite := n01c_finite_offsets_uniform
    (fun i : I => P i.1.val) loss
    (fun i => hmono i.1.val)
    (fun i => hP i.1.val i.1.isLt i.2)
  obtain ⟨d, hd⟩ := hfinite
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hd s
  exact ⟨B, hB, fun k hk hkp => hb ⟨⟨k, hk⟩, hkp⟩⟩

/-- Spatial-order uniformization does not increase the additive loss. -/
theorem n01c_spatial_prefix
    (P : ℕ → ℕ → ℝ → Prop) (offset : ℕ)
    (hmono : ∀ b a a' B B', a ≤ a' → 0 < B → B ≤ B' →
      P b a B → P b a' B')
    (hP : ∀ b : ℕ, ∃ B : ℝ, 0 < B ∧ P b (b + offset) B) :
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ b, b ≤ s → P b (s + offset) B := by
  classical
  intro s
  choose c hc hcb using (fun b : Fin (s + 1) => hP b.val)
  let B : ℝ := 1 + ∑ b : Fin (s + 1), c b
  have hsum : 0 ≤ ∑ b : Fin (s + 1), c b :=
    Finset.sum_nonneg (fun b _ => (hc b).le)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, fun b hb => ?_⟩
  let i : Fin (s + 1) := ⟨b, Nat.lt_succ_of_le hb⟩
  have hci : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
  exact hmono b (b + offset) (s + offset) (c i) B
    (Nat.add_le_add_right hb _) (hc i) hci (hcb i)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- Bounds on one positive state order of the actual angular flow tower.
This is the strict-lower-order induction property, not an added input to
the nonlinear statement. -/
def OrdinaryFlowAngularOrderBound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (loss N : ℕ) : Prop :=
  ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ b : ℕ, b ≤ s → ∀ m,
    ∀ J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m),
    ∀ r : ℝ, ∀ hr : r ∈ Icc (C.left m) (C.right m), ∀ θ : ℝ,
    ∀ x ∈ stateNeighborhood S C base ε, ∀ v : Fin N → (AnnularState S × ℝ),
      |(ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J hr b θ).D N x v| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss + d) (x - (C.referenceState, 0)) v

end ContinuousFlexibility.Statements
