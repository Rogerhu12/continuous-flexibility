import ContinuousFlexibility.Analysis.N08CircleSingleState
import ContinuousFlexibility.Analysis.N08CircleNuLocality

/-!
# Uniform control-diagonal stability at zero parameter

The actual local return data permit replacement by a one-label state.
The material power in the genuine second-jet estimate is canceled by
raising the input circle grading. One neighborhood controls every label.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem n08_small_radius_product {K δ : ℝ} (hK : 0 ≤ K) :
    K * min δ (1 / (8 * (K + 1))) ≤ (1 / 8 : ℝ) := by
  calc
    K * min δ (1 / (8 * (K + 1))) ≤ K * (1 / (8 * (K + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hK
    _ = K / (8 * (K + 1)) := by ring
    _ ≤ 1 / 8 := (div_le_iff₀ (by positivity : 0 < 8 * (K + 1))).mpr (by linarith)

private theorem n08_weighted_decay_bound {K M a d : ℝ} {n : ℕ}
    (hK : 0 ≤ K) (hM : 0 < M) (hd : d ≤ (M ^ n)⁻¹ * a) :
    K * M ^ n * d ≤ K * a := by
  calc
    K * M ^ n * d ≤ K * M ^ n * ((M ^ n)⁻¹ * a) :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg hK (pow_nonneg hM.le _))
    _ = K * (M ^ n * (M ^ n)⁻¹) * a := by ring
    _ = K * a := by rw [mul_inv_cancel₀ (pow_pos hM _).ne', mul_one]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

private theorem n08_zero_diagonal_localized_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {b : ℕ} {δ K : ℝ} (hbase : base ≤ b) (hδ : 0 < δ)
    (hδε : δ ≤ ε) (hK : 0 ≤ K)
    (hcompare : ∀ x y : AnnularState S, ∀ q : ℝ,
      (x, q) ∈ stateNeighborhood S C b δ →
      (y, q) ∈ stateNeighborhood S C b δ →
      stateSector S x → stateSector S y → ∀ m,
      |n08CircleDiagonal hS hR (y, q) m - n08CircleDiagonal hS hR (x, q) m| ≤
        K * T.M (T.sample m) ^ b * stateGrading S b (y - x))
    (x : AnnularState S) (hxsmall : (x, 0) ∈ stateNeighborhood S C b δ)
    (hsx : stateSector S x) (m : ℕ) :
    |n08CircleDiagonal hS hR (x, 0) m - 1| ≤
      K * stateGrading S (b + b) (x - C.referenceState) := by
  let y : AnnularState S := n08CircleSingleState hS C m x
  have hsy : stateSector S y := n08CircleSingleState_sector hS hN.2.2.1 m hsx
  have hysmall : (y, 0) ∈ stateNeighborhood S C b δ := by
    constructor
    · change stateGrading S b (n08CircleSingleState hS C m x - C.referenceState) < δ
      exact (congrArg (stateGrading S b)
        (n08CircleSingleState_sub hS C m x)).trans_lt
        ((n08CircleSingleStateDirection_grading_le hS m b
          (x - C.referenceState)).trans_lt hxsmall.1)
    · exact (abs_zero : |(0 : ℝ)| = 0).trans_lt hδ
  have hrefsmall : (C.referenceState, 0) ∈ stateNeighborhood S C b δ := by
    constructor
    · change stateGrading S b (C.referenceState - C.referenceState) < δ
      exact n08_seminorm_center_lt (stateGrading S b) C.referenceState hδ
    · exact (abs_zero : |(0 : ℝ)| = 0).trans_lt hδ
  have hmono : stateNeighborhood S C b δ ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono hbase hδε
  have heq : n08CircleDiagonal hS hR (x, 0) m = n08CircleDiagonal hS hR (y, 0) m :=
    n08CircleDiagonal_zero_eq_of_kappa_chart hT hS hN hR
      (hmono hxsmall) (hmono hysmall) hsx hsy
      (n08CircleSingleState_kappa hS C m x).symm
      (n08CircleSingleState_chart hS C m x).symm
  have hdiff : |n08CircleDiagonal hS hR (y, 0) m -
      n08CircleDiagonal hS hR (C.referenceState, 0) m| ≤
      K * T.M (T.sample m) ^ b * stateGrading S b (y - C.referenceState) :=
    hcompare C.referenceState y 0 hrefsmall hysmall hN.2.2.1.stateSector hsy m
  have hM : 0 < T.M (T.sample m) := lt_of_lt_of_le zero_lt_one
    (n08_material_sample_bounds hN.1.1 hT m).2
  have hdecay : stateGrading S b (y - C.referenceState) ≤
      (T.M (T.sample m) ^ b)⁻¹ * stateGrading S (b + b) (x - C.referenceState) := by
    exact (congrArg (stateGrading S b)
      (n08CircleSingleState_sub hS C m x)).trans_le
      (n08CircleSingleStateDirection_grading_decay hS m b b
        (x - C.referenceState) hM)
  have hvalue : |n08CircleDiagonal hS hR (x, 0) m - 1| =
      |n08CircleDiagonal hS hR (y, 0) m -
        n08CircleDiagonal hS hR (C.referenceState, 0) m| :=
    congrArg₂ (fun a c : ℝ => |a - c|) heq
      (n08CircleDiagonal_reference hT hS hN hR m).symm
  exact hvalue.le.trans (hdiff.trans (n08_weighted_decay_bound hK hM hdecay))

theorem n08CircleDiagonal_zero_uniform
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) :
    ∃ b : ℕ, ∃ δ : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      ∀ x : AnnularState S, (x, 0) ∈ stateNeighborhood S C b δ →
        stateSector S x → ∀ m,
          |n08CircleDiagonal hS hR (x, 0) m - 1| ≤ (1 / 8 : ℝ) := by
  obtain ⟨b, δ, K, hbase, hδ, hδε, hK, hcompare⟩ :=
    n08CircleDiagonal_state_difference_bound hT hS hN hR
  let η : ℝ := min δ (1 / (8 * (K + 1)))
  have hη : 0 < η := lt_min hδ (by positivity)
  have hηδ : η ≤ δ := min_le_left _ _
  have hb : b ≤ b + b := Nat.le_add_right b b
  refine ⟨b + b, η, hbase.trans hb, hη, hηδ.trans hδε, ?_⟩
  intro x hx hsx m
  have hxsmall : (x, 0) ∈ stateNeighborhood S C b δ :=
    n08_stateNeighborhood_mono hb hηδ hx
  exact (n08_zero_diagonal_localized_bound hT hS hN hR hbase hδ hδε hK
    hcompare x hxsmall hsx m).trans
      ((mul_le_mul_of_nonneg_left hx.1.le hK).trans (n08_small_radius_product hK))

end ContinuousFlexibility.Statements
