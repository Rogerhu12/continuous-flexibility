module

public import ContinuousFlexibility.Radial.OuterPhysicalTailGreenBounds
public import ContinuousFlexibility.Radial.OuterTailKernelDecay

/-!
# Pointwise decay of the same natural state and Green pair

The actual Poisson interpolants turn the preserved node contraction into
pointwise estimates. The initial Dirichlet interval uses the same pair,
so its mixed products retain the full relative attenuation product.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem outer_tail_state_bound_nodes {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16)
    {f q : ℝ → ℝ}
    (hf : TailFirstOrderSystem T.p T.Λ f q (Ico T.entrance T.endpoint))
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    |f x| ≤ 2 * (|f (T.node n)| + |f (T.node (n + 1))|) := by
  rw [outer_tail_state_eq_interpolation hT hf n hx]
  unfold tailActualEdgeInterpolation
  calc
    _ ≤ |f (T.node n) * tailActualEdgePoissonPhysical T hT n false x| +
        |f (T.node (n + 1)) * tailActualEdgePoissonPhysical T hT n true x| :=
      abs_add_le _ _
    _ ≤ |f (T.node n)| * 2 + |f (T.node (n + 1))| * 2 := by
      simpa only [abs_mul] using add_le_add
        (mul_le_mul_of_nonneg_left (tailActualEdgePoissonPhysical_abs_le_two hT hη n false hx)
          (abs_nonneg (f (T.node n))))
        (mul_le_mul_of_nonneg_left (tailActualEdgePoissonPhysical_abs_le_two hT hη n true hx)
          (abs_nonneg (f (T.node (n + 1)))))
    _ = _ := by ring

theorem outer_tail_step_factor_le_one {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hK : 32 ≤ T.K) (n : ℕ) :
    8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) ≤ 1 := by
  apply (div_le_one (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (n + 1)))
    (tailResistance_pos hT n))).mpr
  exact (show (8 : ℝ) ≤ T.K by linarith only [hK]).trans
    (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.1

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K : ℝ}

theorem logP_node_step_le
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hK : 32 ≤ K) (n : ℕ) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    |F.logP (T.node (n + 1))| ≤ |F.logP (T.node n)| := by
  exact (F.P_node_step n).trans
    ((mul_le_mul_of_nonneg_right (outer_tail_step_factor_le_one hT hK n)
      (abs_nonneg _)).trans_eq (one_mul _))

theorem logP_node_product
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hK : 32 ≤ K) (n : ℕ) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    |F.logP (T.node n)| ≤
      (∏ k ∈ Finset.Ico 0 n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k)) *
        |F.logP T.entrance| := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  induction n with
  | zero => simpa using F.logP_initial_node_le_entry hT hK
  | succ n ih =>
      have hr : 0 ≤ 8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) :=
        div_nonneg (by norm_num)
          (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (n + 1)))
            (tailResistance_pos hT n)).le
      calc
        _ ≤ (8 / (T.Λ * tailMass T (n + 1) * tailResistance T n)) *
            |F.logP (T.node n)| := F.P_node_step n
        _ ≤ (8 / (T.Λ * tailMass T (n + 1) * tailResistance T n)) *
            ((∏ k ∈ Finset.Ico 0 n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k)) *
              |F.logP T.entrance|) := mul_le_mul_of_nonneg_left ih hr
        _ = _ := by rw [Finset.prod_Ico_succ_top (Nat.zero_le n)]; ring

theorem logP_edge_bound
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc
      ((morsePhysicalDeepTail M D right j start entrance η K).node n)
      ((morsePhysicalDeepTail M D right j start entrance η K).node (n + 1))) :
    |F.logP x| ≤ 4 *
      |F.logP ((morsePhysicalDeepTail M D right j start entrance η K).node n)| := by
  have hb := outer_tail_state_bound_nodes hT hη F.P_log_system n hx
  have hs := F.logP_node_step_le hT hK n
  nlinarith only [hb, hs]

theorem logP_edge_envelope
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) {C : ℝ} (hC : 0 ≤ C)
    (hden : ∀ k, exp (2 * ((start + k : ℕ) : ℝ) ^ 2 -
      C * (((start + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + k : ℕ))) ≤
        (morsePhysicalDeepTail M D right j start entrance η K).Λ *
          tailMass (morsePhysicalDeepTail M D right j start entrance η K) (k + 1) *
          tailResistance (morsePhysicalDeepTail M D right j start entrance η K) k)
    (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc
      ((morsePhysicalDeepTail M D right j start entrance η K).node n)
      ((morsePhysicalDeepTail M D right j start entrance η K).node (n + 1))) :
    |F.logP x| ≤ 4 * |F.logP (tailPhysicalLog right entrance)| *
      (radialE (start + n) ^ outerPhysicalDecayCost C *
        exp (-|radialS (start + n) - radialS start|)) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hp := F.logP_node_product hT hK n
  have hd := outer_physical_decay_product_envelope hC start hden (Nat.zero_le n)
  simp only [Nat.add_zero] at hd
  calc
    _ ≤ 4 * |F.logP (T.node n)| := F.logP_edge_bound hT hη hK n hx
    _ ≤ 4 * ((∏ k ∈ Finset.Ico 0 n,
        8 / (T.Λ * tailMass T (k + 1) * tailResistance T k)) * |F.logP T.entrance|) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ 4 * ((radialE (start + n) ^ outerPhysicalDecayCost C *
        exp (-|radialS (start + n) - radialS start|)) * |F.logP T.entrance|) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hd (abs_nonneg _)) (by norm_num)
    _ = _ := by change 4 * (_ * |F.logP T.entrance|) = 4 * |F.logP T.entrance| * _; ring

/-- A point in the initial interval and a point on any ordinary edge use
the same normalized Green pair and the same relative decay product. -/
theorem log_initial_edge_kernel_bound
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) (n : ℕ) {x y : ℝ}
    (hx : x ∈ Icc
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      ((morsePhysicalDeepTail M D right j start entrance η K).node 0))
    (hy : y ∈ Icc
      ((morsePhysicalDeepTail M D right j start entrance η K).node n)
      ((morsePhysicalDeepTail M D right j start entrance η K).node (n + 1))) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    |F.logQ (min x y) * F.logP (max x y)| ≤
      64 * tailFundamentalGreenBlockWeight T 0 *
        ∏ k ∈ Finset.Ico 0 n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hxy : x ≤ y := hx.2.trans
    (((deepTail_node_strictMono hT).monotone (Nat.zero_le n)).trans hy.1)
  rw [min_eq_left hxy, max_eq_right hxy]
  have hq := F.logQ_initial_bound hT hη hx
  have hp := F.logP_edge_bound hT hη hK n hy
  have hnode := F.log_node_green_bound hT hη hK 0 n (Nat.zero_le n)
  have hi : (T.Λ * tailMass T 0)⁻¹ ≤ tailFundamentalGreenBlockWeight T 0 := by
    have hI := (tailInnerResistance_pos hT 0).le
    have hR := (tailResistance_pos hT 0).le
    unfold tailFundamentalGreenBlockWeight
    linarith only [hI, hR]
  have hc : (8 / T.Λ) / tailMass T 0 ≤ 8 * tailFundamentalGreenBlockWeight T 0 := by
    calc
      _ = 8 * (T.Λ * tailMass T 0)⁻¹ := by
        field_simp [hT.2.2.1.ne', (tailMass_pos hT 0).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (by norm_num)
  have hprod : 0 ≤ ∏ k ∈ Finset.Ico 0 n,
      8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) :=
    Finset.prod_nonneg fun k _ => div_nonneg (by norm_num)
      (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (k + 1)))
        (tailResistance_pos hT k)).le
  calc
    _ = |F.logQ x| * |F.logP y| := abs_mul _ _
    _ ≤ (2 * |F.logQ (T.node 0)|) * (4 * |F.logP (T.node n)|) :=
      mul_le_mul hq hp (abs_nonneg _) (by positivity)
    _ = 8 * |F.logQ (T.node 0) * F.logP (T.node n)| := by rw [abs_mul]; ring
    _ ≤ 8 * (((8 / T.Λ) / tailMass T 0) *
        ∏ k ∈ Finset.Ico 0 n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k)) :=
      mul_le_mul_of_nonneg_left hnode (by norm_num)
    _ ≤ 8 * ((8 * tailFundamentalGreenBlockWeight T 0) *
        ∏ k ∈ Finset.Ico 0 n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hprod) (by norm_num)
    _ = _ := by ring

end MorsePhysicalTailBasis

end ContinuousFlexibility.Radial
