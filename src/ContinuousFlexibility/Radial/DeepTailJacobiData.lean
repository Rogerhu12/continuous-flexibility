module

public import ContinuousFlexibility.Radial.DeepTailJacobiBounds
public import ContinuousFlexibility.Radial.DeepTailInitialEdge

/-!
# The actual Jacobi data of a deep tail

The coefficients are the flux coefficients of the actual Poisson
functions.  Deep mass-resistance inequalities give uniform diagonal
dominance and the weighted square bound used by the continuous natural
node construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

def deepTailEdgeResistance (T : DeepTailData) (n : ℕ) : ℝ :=
  ∫ x in T.node n..T.node (n + 1), (T.p x)⁻¹

theorem deepTail_edge_continuous {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    ContinuousOn T.p (Icc (T.node n) (T.node (n + 1))) :=
  (deepTail_contDiffOn hT).continuousOn.mono
    (deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
      (deepTail_node_lt_endpoint hT (n + 1)))

theorem deepTail_edge_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    ∀ x ∈ Icc (T.node n) (T.node (n + 1)), 0 < T.p x :=
  fun x hx => deepTail_pos hT x
    (deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
      (deepTail_node_lt_endpoint hT (n + 1)) hx)

theorem deepTailEdgeResistance_eq {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    deepTailEdgeResistance T n = tailInnerResistance T n + tailResistance T n := by
  have hp := (deepTail_edge_continuous hT n).inv₀
    (fun x hx => (deepTail_edge_pos hT n x hx).ne')
  have h₁ := (hp.mono (Icc_subset_Icc le_rfl
    (deepTail_massEnd_lt_succ_node hT n).le)).intervalIntegrable_of_Icc
      (μ := volume) (deepTail_node_lt_massEnd hT n).le
  have h₂ := (hp.mono (Icc_subset_Icc (deepTail_node_lt_massEnd hT n).le
    le_rfl)).intervalIntegrable_of_Icc (μ := volume) (deepTail_massEnd_lt_succ_node hT n).le
  exact (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm

theorem deepTailEdgeResistance_eq_chart {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) :
    tailResistanceChart (tailClampedDensity T.p (T.node n) (T.node (n + 1))
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le) (T.node n) (T.node (n + 1)) =
      deepTailEdgeResistance T n :=
  tailClampedResistanceChart_eq _ ⟨(deepTail_node_strictMono hT (Nat.lt_succ_self n)).le, le_rfl⟩

theorem deepTailEdgeResistance_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    0 < deepTailEdgeResistance T n := by
  rw [deepTailEdgeResistance_eq hT n]
  exact add_pos (tailInnerResistance_pos hT n) (tailResistance_pos hT n)

theorem tailResistance_le_deepTailEdgeResistance {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailResistance T n ≤ deepTailEdgeResistance T n := by
  rw [deepTailEdgeResistance_eq hT n]
  exact le_add_of_nonneg_left (tailInnerResistance_pos hT n).le

theorem deepTailEdgeResistance_inv_le_left {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hK : 64 ≤ T.K) (n : ℕ) :
    (deepTailEdgeResistance T n)⁻¹ ≤ T.Λ * tailMass T n / 64 :=
  ((inv_anti₀ (tailResistance_pos hT n)
    (tailResistance_le_deepTailEdgeResistance hT n)).trans
      (deepTail_inverse_resistance_left hT n)).trans
    (div_le_div_of_nonneg_left (mul_pos hT.2.2.1 (tailMass_pos hT n)).le (by norm_num) hK)

theorem deepTailEdgeResistance_inv_le_right {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hK : 64 ≤ T.K) (n : ℕ) :
    (deepTailEdgeResistance T n)⁻¹ ≤ T.Λ * tailMass T (n + 1) / 64 :=
  ((inv_anti₀ (tailResistance_pos hT n)
    (tailResistance_le_deepTailEdgeResistance hT n)).trans
      (deepTail_inverse_resistance_right hT n)).trans
    (div_le_div_of_nonneg_left (mul_pos hT.2.2.1 (tailMass_pos hT (n + 1))).le
      (by norm_num) hK)

theorem deepTail_edge_mass {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    (∫ x in T.node n..T.node (n + 1), T.p x) = tailMass T n + tailGapMass T n := by
  have hp := deepTail_edge_continuous hT n
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((hp.mono (Icc_subset_Icc le_rfl (deepTail_massEnd_lt_succ_node hT n).le)).intervalIntegrable_of_Icc
      (deepTail_node_lt_massEnd hT n).le)
    ((hp.mono (Icc_subset_Icc (deepTail_node_lt_massEnd hT n).le le_rfl)).intervalIntegrable_of_Icc
      (deepTail_massEnd_lt_succ_node hT n).le)).symm

theorem deepTail_inner_resistance_short {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 16) (hK : 64 ≤ T.K) (n : ℕ) :
    4 * tailInnerResistance T n ≤ deepTailEdgeResistance T n := by
  apply le_trans _ (tailResistance_le_deepTailEdgeResistance hT n)
  apply (mul_le_mul_iff_right₀ (mul_pos hT.2.2.1 (tailMass_pos hT n))).mp
  have hs := deepTail_mass_resistance_small hT n
  have hd := (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.1
  nlinarith only [hs, hd, hη, hK]

section ActualEdges

variable {T : DeepTailData} (hT : DeepTailHypotheses T)
  (hη : T.η ≤ 1 / 16) (hK : 64 ≤ T.K)
  (B : ∀ n, TailPhysicalPoissonData T.p (T.node n) (T.node (n + 1)) T.Λ T.η
    (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le)

include hη hK in
theorem deepTail_Poisson_leftDiagonal_bound (n : ℕ) :
    (B n).leftDiagonal ≤ (deepTailEdgeResistance T n)⁻¹ - T.Λ * tailMass T n / 2 := by
  have hs : 4 * tailResistanceChart (tailClampedDensity T.p (T.node n) (T.node (n + 1))
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le) (T.node n) (T.massEnd n) ≤
      tailResistanceChart (tailClampedDensity T.p (T.node n) (T.node (n + 1))
        (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le) (T.node n) (T.node (n + 1)) := by
    rw [tailClampedResistanceChart_eq _
      ⟨(deepTail_node_lt_massEnd hT n).le, (deepTail_massEnd_lt_succ_node hT n).le⟩,
      deepTailEdgeResistance_eq_chart hT n]
    exact deepTail_inner_resistance_short hT hη hK n
  have h := (B n).leftDiagonal_le_inv_sub_half_mass
    (deepTail_node_strictMono hT (Nat.lt_succ_self n))
    ⟨(deepTail_node_lt_massEnd hT n).le, (deepTail_massEnd_lt_succ_node hT n).le⟩
    (deepTail_edge_continuous hT n) (deepTail_edge_pos hT n) hT.2.2.1.le hs
  simpa only [deepTailEdgeResistance_eq_chart hT n, tailMass] using h

theorem deepTail_Poisson_rightDiagonal_bound (n : ℕ) :
    (B n).rightDiagonal ≤ (deepTailEdgeResistance T n)⁻¹ := by
  simpa only [deepTailEdgeResistance_eq_chart hT n] using
    (B n).rightDiagonal_le_inv (deepTail_node_strictMono hT (Nat.lt_succ_self n))
      (deepTail_edge_continuous hT n) (deepTail_edge_pos hT n) hT.2.2.1.le

theorem deepTail_Poisson_offDiagonal_pos (n : ℕ) : 0 < (B n).offDiagonal :=
  (B n).offDiagonal_pos (deepTail_node_strictMono hT (Nat.lt_succ_self n))
    (deepTail_edge_continuous hT n) (deepTail_edge_pos hT n) hT.2.2.1.le

include hη in
theorem deepTail_Poisson_offDiagonal_bound (n : ℕ) :
    (B n).offDiagonal ≤ 2 / tailResistance T n := by
  have h := (B n).offDiagonal_le_two_div_length
    (deepTail_node_strictMono hT (Nat.lt_succ_self n)) (deepTail_edge_continuous hT n)
    (deepTail_edge_pos hT n) (show T.η ≤ 1 / 2 by linarith only [hη])
  rw [deepTailEdgeResistance_eq_chart hT n] at h
  exact h.trans (div_le_div_of_nonneg_left (by norm_num) (tailResistance_pos hT n)
    (tailResistance_le_deepTailEdgeResistance hT n))

include hη hK in
/-- When the first node is the entrance, this continuous flux coefficient
can serve as the otherwise unused zeroth Jacobi diagonal. -/
theorem deepTail_Poisson_firstDiagonal_bound :
    T.Λ * tailMass T 0 / 4 ≤ -(B 0).leftDiagonal := by
  have hl := deepTail_Poisson_leftDiagonal_bound hT hη hK B 0
  have hi := deepTailEdgeResistance_inv_le_left hT hK 0
  have hμ := mul_pos hT.2.2.1 (tailMass_pos hT 0)
  linarith only [hl, hi, hμ]

include hη hK in
theorem deepTail_Poisson_jacobiDiagonal_bound {b₀ : ℝ}
    (hb₀ : T.Λ * tailMass T 0 / 4 ≤ b₀) (n : ℕ) :
    T.Λ * tailMass T n / 4 ≤ tailPoissonJacobiDiagonal B b₀ n := by
  cases n with
  | zero => exact hb₀
  | succ n =>
    change T.Λ * tailMass T (n + 1) / 4 ≤ -(B n).rightDiagonal - (B (n + 1)).leftDiagonal
    have hr := deepTail_Poisson_rightDiagonal_bound hT B n
    have hl := deepTail_Poisson_leftDiagonal_bound hT hη hK B (n + 1)
    have hir := deepTailEdgeResistance_inv_le_right hT hK n
    have hil := deepTailEdgeResistance_inv_le_left hT hK (n + 1)
    have hμ := mul_pos hT.2.2.1 (tailMass_pos hT (n + 1))
    linarith only [hr, hl, hir, hil, hμ]

include hη hK in
theorem deepTail_Poisson_jacobi_smallness {b₀ : ℝ}
    (hb₀ : T.Λ * tailMass T 0 / 4 ≤ b₀) :
    (∀ n, (tailPoissonJacobiOffDiagonal B n) ^ 2 /
      (tailPoissonJacobiDiagonal B b₀ n * tailPoissonJacobiDiagonal B b₀ (n + 1)) ∈
        Icc 0 (1 / 8 : ℝ)) ∧
    (∀ n, Real.sqrt (tailMass T (n + 1)) *
      (tailPoissonJacobiOffDiagonal B n / tailPoissonJacobiDiagonal B b₀ (n + 1)) ≤
        (1 / 4 : ℝ) * Real.sqrt (tailMass T n)) := by
  exact tailJacobi_smallness hT.2.2.1 (tailMass_pos hT) (tailResistance_pos hT)
    (deepTail_Poisson_jacobiDiagonal_bound hT hη hK B hb₀)
    (fun n => (deepTail_Poisson_offDiagonal_pos hT B n).le)
    (deepTail_Poisson_offDiagonal_bound hT hη B)
    (fun n => (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.1)
    (fun n => (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.1) hK

include hη hK in
theorem deepTail_initialJacobiDiagonal_bound (hinitial : T.entrance < T.node 0)
    (BI : TailPhysicalPoissonData T.p T.entrance (T.node 0) T.Λ T.η hinitial.le) :
    T.Λ * tailMass T 0 / 4 ≤ -BI.rightDiagonal - (B 0).leftDiagonal := by
  have hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
  have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
  have hpos := fun x hx => deepTail_pos hT x (hsub hx)
  have hi := BI.rightDiagonal_le_inv hinitial hp hpos hT.2.2.1.le
  rw [tailClampedResistanceChart_eq hinitial.le ⟨hinitial.le, le_rfl⟩] at hi
  have hir : (tailInitialResistance T)⁻¹ ≤ T.Λ * tailMass T 0 / 64 :=
    (deepTail_initial_inverse_resistance hT hinitial).trans
      (div_le_div_of_nonneg_left (mul_pos hT.2.2.1 (tailMass_pos hT 0)).le (by norm_num) hK)
  have hl := deepTail_Poisson_leftDiagonal_bound hT hη hK B 0
  have hil := deepTailEdgeResistance_inv_le_left hT hK 0
  have hμ := mul_pos hT.2.2.1 (tailMass_pos hT 0)
  change BI.rightDiagonal ≤ (tailInitialResistance T)⁻¹ at hi
  linarith only [hi, hir, hl, hil, hμ]

include hη hK in
theorem deepTail_rightHeight_mass_bound (n : ℕ) :
    tailPhysicalHeight T.p (T.node n) (T.node (n + 1))
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le true (T.massEnd n) *
        tailMass T n ≤ tailMass T (n + 1) := by
  have hL := deepTailEdgeResistance_pos hT n
  have hR := tailResistance_le_deepTailEdgeResistance hT n
  have hs := deepTail_mass_resistance_small hT n
  have hd := (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.1
  have hm := mul_le_mul_of_nonneg_left hR
    (mul_pos hT.2.2.1 (tailMass_pos hT (n + 1))).le
  have hscaled : T.Λ * (tailInnerResistance T n * tailMass T n) ≤
      T.Λ * (tailMass T (n + 1) * deepTailEdgeResistance T n) := by
    nlinarith only [hs, hd, hm, hη, hK]
  have hprod := (mul_le_mul_iff_right₀ hT.2.2.1).mp hscaled
  simp only [tailPhysicalHeight, ite_true,
    tailClampedResistanceChart_eq _
      ⟨(deepTail_node_lt_massEnd hT n).le, (deepTail_massEnd_lt_succ_node hT n).le⟩,
    deepTailEdgeResistance_eq_chart hT n]
  change (tailInnerResistance T n / deepTailEdgeResistance T n) * tailMass T n ≤ _
  calc
    _ = (tailInnerResistance T n * tailMass T n) / deepTailEdgeResistance T n := by ring
    _ ≤ tailMass T (n + 1) := (div_le_iff₀ hL).mpr hprod

include hη in
theorem deepTail_Poisson_left_square_bound (n : ℕ) :
    (∫ x in T.node n..T.node (n + 1), T.p x * (B n).u false x ^ 2) ≤
      8 * tailMass T n := by
  have h := (B n).basis_square_le_four_mass
    (deepTail_node_strictMono hT (Nat.lt_succ_self n)) (deepTail_edge_continuous hT n)
    (deepTail_edge_pos hT n) (show T.η ≤ 1 / 2 by linarith only [hη]) false
  rw [deepTail_edge_mass hT n] at h
  have hg := deepTail_gap_mass_le_left hT n
  have hm := mul_le_mul_of_nonneg_right (show T.η ≤ 1 by linarith only [hη])
    (tailMass_pos hT n).le
  linarith only [h, hg, hm]

include hη hK in
theorem deepTail_Poisson_right_square_bound (n : ℕ) :
    (∫ x in T.node n..T.node (n + 1), T.p x * (B n).u true x ^ 2) ≤
      8 * tailMass T (n + 1) := by
  have h := (B n).right_basis_square_bound
    (deepTail_node_strictMono hT (Nat.lt_succ_self n))
    ⟨(deepTail_node_lt_massEnd hT n).le, (deepTail_massEnd_lt_succ_node hT n).le⟩
    (deepTail_edge_continuous hT n) (deepTail_edge_pos hT n)
    (show T.η ≤ 1 / 2 by linarith only [hη])
  have hw := deepTail_rightHeight_mass_bound hT hη hK n
  have hg := deepTail_gap_mass_le_right hT n
  have hm := mul_le_mul_of_nonneg_right (show T.η ≤ 1 by linarith only [hη])
    (tailMass_pos hT (n + 1)).le
  change (∫ x in T.node n..T.node (n + 1), T.p x * (B n).u true x ^ 2) ≤
    4 * (tailPhysicalHeight T.p (T.node n) (T.node (n + 1))
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le true (T.massEnd n) *
        tailMass T n + tailGapMass T n) at h
  linarith only [h, hw, hg, hm]

include hη hK in
/-- The actual Poisson interpolant has one universal weighted square
bound, with the two coefficients charged to their own neighboring masses. -/
theorem deepTail_Poisson_interpolate_square_bound (n : ℕ) (A Z : ℝ) :
    (∫ x in T.node n..T.node (n + 1), T.p x * (B n).interpolate A Z x ^ 2) ≤
      16 * (tailMass T n * A ^ 2 + tailMass T (n + 1) * Z ^ 2) := by
  have h := tailEdge_interpolant_square_bound
    (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le (deepTail_edge_continuous hT n)
    ((B n).differentiable false).continuous.continuousOn
    ((B n).differentiable true).continuous.continuousOn
    (fun x hx => (deepTail_edge_pos hT n x hx).le)
    (deepTail_Poisson_left_square_bound hT hη B n)
    (deepTail_Poisson_right_square_bound hT hη hK B n) A Z
  change (∫ x in T.node n..T.node (n + 1),
      T.p x * (A * (B n).u false x + Z * (B n).u true x) ^ 2) ≤ _
  convert h using 1 <;> ring

end ActualEdges

end ContinuousFlexibility.Radial
