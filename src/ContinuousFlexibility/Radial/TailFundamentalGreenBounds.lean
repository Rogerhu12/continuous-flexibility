module

public import ContinuousFlexibility.Radial.TailFundamentalGreenKernel
public import ContinuousFlexibility.Radial.TailActualSolutionNodes
public import ContinuousFlexibility.Radial.TailNodeProducts

/-!
# Localized bounds for the actual fundamental Green kernel

The four products of neighboring endpoint values control the product of
two physical Poisson interpolants. Shifting the left endpoint consumes one
decay factor. On the same edge, the conserved discrete Wronskian supplies
the single product whose node order is reversed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem tailGreen_prod_Ico_succ_le {r : ℕ → ℝ}
    (hr₀ : ∀ k, 0 ≤ r k) (hr₁ : ∀ k, r k ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    (∏ k ∈ Finset.Ico m (n + 1), r k) ≤ ∏ k ∈ Finset.Ico m n, r k := by
  rw [Finset.prod_Ico_succ_top hmn]
  exact (mul_le_mul_of_nonneg_left (hr₁ n)
    (Finset.prod_nonneg fun k _ => hr₀ k)).trans_eq (mul_one _)

theorem tailGreen_shifted_node_product_bound {w u g r H : ℕ → ℝ}
    (hr₀ : ∀ k, 0 ≤ r k)
    (hΓ : ∀ m n, m ≤ n → |w m * u n| ≤ g m * ∏ k ∈ Finset.Ico m n, r k)
    (hshift : ∀ m, g (m + 1) ≤ H m * r m) {m n : ℕ} (hmn : m < n) :
    |w (m + 1) * u n| ≤ H m * ∏ k ∈ Finset.Ico m n, r k := by
  calc
    |w (m + 1) * u n| ≤ g (m + 1) * ∏ k ∈ Finset.Ico (m + 1) n, r k :=
      hΓ (m + 1) n (Nat.succ_le_of_lt hmn)
    _ ≤ (H m * r m) * ∏ k ∈ Finset.Ico (m + 1) n, r k :=
      mul_le_mul_of_nonneg_right (hshift m) (Finset.prod_nonneg fun k _ => hr₀ k)
    _ = H m * ∏ k ∈ Finset.Ico m n, r k := by
      rw [Finset.prod_eq_prod_Ico_succ_bot hmn]
      ring

theorem tailGreen_reverse_node_product_bound {w₀ w₁ u₀ u₁ c L g r H : ℝ}
    (hc : 0 < c) (hcL : 1 / c ≤ L) (hg : 0 ≤ g) (hr : r ≤ 1)
    (hΓ : |w₀ * u₁| ≤ g * r) (hbudget : L + g ≤ H)
    (hcross : c * (u₀ * w₁ - u₁ * w₀) = 1) : |w₁ * u₀| ≤ H := by
  have heq : w₁ * u₀ = 1 / c + w₀ * u₁ := by
    apply (mul_left_cancel₀ hc.ne')
    field_simp [hc.ne']
    nlinarith only [hcross]
  calc
    |w₁ * u₀| = |1 / c + w₀ * u₁| := congrArg abs heq
    _ ≤ |1 / c| + |w₀ * u₁| := abs_add_le _ _
    _ = 1 / c + |w₀ * u₁| := by rw [abs_of_pos (one_div_pos.mpr hc)]
    _ ≤ L + g * r := add_le_add hcL hΓ
    _ ≤ L + g := add_le_add le_rfl
      ((mul_le_mul_of_nonneg_left hr hg).trans_eq (mul_one _))
    _ ≤ H := hbudget

/-- All four corner products have one common bound, including the
diagonal block where one corner reverses the node order. -/
theorem tailGreen_four_node_product_bounds {w u g r H : ℕ → ℝ}
    (hg : ∀ k, 0 ≤ g k) (hH : ∀ k, 0 ≤ H k)
    (hr₀ : ∀ k, 0 ≤ r k) (hr₁ : ∀ k, r k ≤ 1)
    (hΓ : ∀ m n, m ≤ n → |w m * u n| ≤ g m * ∏ k ∈ Finset.Ico m n, r k)
    (hbase : ∀ m, g m ≤ H m) (hshift : ∀ m, g (m + 1) ≤ H m * r m)
    (hreverse : ∀ m, |w (m + 1) * u m| ≤ H m)
    {m n : ℕ} (hmn : m ≤ n) :
    |w m * u n| ≤ H m * ∏ k ∈ Finset.Ico m n, r k ∧
    |w m * u (n + 1)| ≤ H m * ∏ k ∈ Finset.Ico m n, r k ∧
    |w (m + 1) * u n| ≤ H m * ∏ k ∈ Finset.Ico m n, r k ∧
    |w (m + 1) * u (n + 1)| ≤ H m * ∏ k ∈ Finset.Ico m n, r k := by
  have hp := tailGreen_prod_Ico_succ_le hr₀ hr₁ hmn
  refine ⟨(hΓ m n hmn).trans
    (mul_le_mul_of_nonneg_right (hbase m) (Finset.prod_nonneg fun k _ => hr₀ k)), ?_, ?_, ?_⟩
  · calc
      |w m * u (n + 1)| ≤ g m * ∏ k ∈ Finset.Ico m (n + 1), r k :=
        hΓ m (n + 1) (hmn.trans (Nat.le_succ n))
      _ ≤ g m * ∏ k ∈ Finset.Ico m n, r k := mul_le_mul_of_nonneg_left hp (hg m)
      _ ≤ H m * ∏ k ∈ Finset.Ico m n, r k :=
        mul_le_mul_of_nonneg_right (hbase m) (Finset.prod_nonneg fun k _ => hr₀ k)
  · rcases lt_or_eq_of_le hmn with hlt | rfl
    · exact tailGreen_shifted_node_product_bound hr₀ hΓ hshift hlt
    · simpa using hreverse m
  · exact (tailGreen_shifted_node_product_bound hr₀ hΓ hshift
      (hmn.trans_lt (Nat.lt_succ_self n))).trans
      (mul_le_mul_of_nonneg_left hp (hH m))

/-- Two Poisson interpolation coefficients bounded by two amplify a
common four-corner product bound by at most sixteen. -/
theorem tailGreen_two_interpolants_product_le
    {a₀ a₁ b₀ b₁ α₀ α₁ β₀ β₁ H : ℝ}
    (hα₀ : |α₀| ≤ 2) (hα₁ : |α₁| ≤ 2)
    (hβ₀ : |β₀| ≤ 2) (hβ₁ : |β₁| ≤ 2)
    (h₀₀ : |a₀ * b₀| ≤ H) (h₀₁ : |a₀ * b₁| ≤ H)
    (h₁₀ : |a₁ * b₀| ≤ H) (h₁₁ : |a₁ * b₁| ≤ H) :
    |(a₀ * α₀ + a₁ * α₁) * (b₀ * β₀ + b₁ * β₁)| ≤ 16 * H := by
  have ha : |a₀ * α₀ + a₁ * α₁| ≤ 2 * (|a₀| + |a₁|) := by
    calc
      _ ≤ |a₀ * α₀| + |a₁ * α₁| := abs_add_le _ _
      _ ≤ |a₀| * 2 + |a₁| * 2 := by
        simpa only [abs_mul] using add_le_add
          (mul_le_mul_of_nonneg_left hα₀ (abs_nonneg a₀))
          (mul_le_mul_of_nonneg_left hα₁ (abs_nonneg a₁))
      _ = _ := by ring
  have hb : |b₀ * β₀ + b₁ * β₁| ≤ 2 * (|b₀| + |b₁|) := by
    calc
      _ ≤ |b₀ * β₀| + |b₁ * β₁| := abs_add_le _ _
      _ ≤ |b₀| * 2 + |b₁| * 2 := by
        simpa only [abs_mul] using add_le_add
          (mul_le_mul_of_nonneg_left hβ₀ (abs_nonneg b₀))
          (mul_le_mul_of_nonneg_left hβ₁ (abs_nonneg b₁))
      _ = _ := by ring
  rw [abs_mul]
  apply (mul_le_mul ha hb (abs_nonneg _)
    (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _)))).trans
  rw [abs_mul] at h₀₀ h₀₁ h₁₀ h₁₁
  nlinarith only [h₀₀, h₀₁, h₁₀, h₁₁]

/-- The physical block weight absorbs both the inverse mass and the loss
of the first decay factor after shifting the left node. -/
theorem tailGreen_mass_resistance_budget {Λ B μ ν I R A : ℝ}
    (hΛ : 0 < Λ) (hB : 0 ≤ B) (hμ : 0 < μ) (hν : 0 < ν)
    (hI : 0 ≤ I) (hR : 0 < R)
    (hA : 1 + I + R + (Λ * μ)⁻¹ ≤ A) :
    I + R + B / μ ≤ (B * Λ + 1) * A ∧
      B / ν ≤ ((B * Λ + 1) * A) * (8 / (Λ * ν * R)) := by
  have hv : 0 ≤ (Λ * μ)⁻¹ := (inv_pos.mpr (mul_pos hΛ hμ)).le
  have hA₀ : 0 ≤ A := by linarith only [hA, hI, hR, hv]
  have hAI : I + R ≤ A := by linarith only [hA, hv]
  have hAv : (Λ * μ)⁻¹ ≤ A := by linarith only [hA, hI, hR]
  have hAR : R ≤ A := by linarith only [hA, hI, hv]
  have hBΛ : 0 ≤ B * Λ := mul_nonneg hB hΛ.le
  have hH₀ : 0 ≤ (B * Λ + 1) * A :=
    mul_nonneg (by linarith only [hBΛ]) hA₀
  have heq : B / μ = (B * Λ) * (Λ * μ)⁻¹ := by
    field_simp [hΛ.ne', hμ.ne'] <;> ring
  constructor
  · calc
      I + R + B / μ = I + R + (B * Λ) * (Λ * μ)⁻¹ := by rw [heq]
      _ ≤ A + (B * Λ) * A :=
        add_le_add hAI (mul_le_mul_of_nonneg_left hAv hBΛ)
      _ = (B * Λ + 1) * A := by ring
  · have hBR : B * Λ * R ≤ (B * Λ + 1) * A := by
      calc
        _ ≤ B * Λ * A := mul_le_mul_of_nonneg_left hAR hBΛ
        _ ≤ (B * Λ + 1) * A :=
          mul_le_mul_of_nonneg_right (by linarith) hA₀
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (mul_pos (mul_pos hΛ hν) hR)).mpr
    calc
      (B / ν) * (Λ * ν * R) = B * Λ * R := by
        field_simp [hν.ne'] <;> ring
      _ ≤ (B * Λ + 1) * A := hBR
      _ ≤ ((B * Λ + 1) * A) * 8 := by nlinarith only [hH₀]

def tailFundamentalGreenBlockWeight (T : DeepTailData) (n : ℕ) : ℝ :=
  1 + tailInnerResistance T n + tailResistance T n + (T.Λ * tailMass T n)⁻¹

theorem tailFundamentalGreenBlockWeight_one_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) : 1 ≤ tailFundamentalGreenBlockWeight T n := by
  have hI := (tailInnerResistance_pos hT n).le
  have hR := (tailResistance_pos hT n).le
  have hμ := (inv_pos.mpr (mul_pos hT.2.2.1 (tailMass_pos hT n))).le
  dsimp only [tailFundamentalGreenBlockWeight]
  linarith only [hI, hR, hμ]

/-- Node estimates from the inverse and the actual conserved Casoratian
control all four endpoint products of any ordered pair of physical edges. -/
theorem tailGreen_four_physical_node_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hK : 32 ≤ T.K) {B : ℝ} (hB : 0 < B)
    {w u : ℝ → ℝ}
    (hΓ : ∀ m n, m ≤ n →
      |w (T.node m) * u (T.node n)| ≤ (B / tailMass T m) *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k))
    (hcross : ∀ n, tailActualNodeCoupling T hT n *
      (u (T.node n) * w (T.node (n + 1)) - u (T.node (n + 1)) * w (T.node n)) = 1)
    {m n : ℕ} (hmn : m ≤ n) :
    let H := (B * T.Λ + 1) * tailFundamentalGreenBlockWeight T m *
      ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k)
    |w (T.node m) * u (T.node n)| ≤ H ∧
    |w (T.node m) * u (T.node (n + 1))| ≤ H ∧
    |w (T.node (m + 1)) * u (T.node n)| ≤ H ∧
    |w (T.node (m + 1)) * u (T.node (n + 1))| ≤ H := by
  let r : ℕ → ℝ := fun k => 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k)
  let g : ℕ → ℝ := fun k => B / tailMass T k
  let H : ℕ → ℝ := fun k => (B * T.Λ + 1) * tailFundamentalGreenBlockWeight T k
  have hr₀ (k : ℕ) : 0 ≤ r k :=
    (div_pos (by norm_num) (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (k + 1)))
      (tailResistance_pos hT k))).le
  have hr₁ (k : ℕ) : r k ≤ 1 := by
    apply (div_le_one (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (k + 1)))
      (tailResistance_pos hT k))).mpr
    exact (show (8 : ℝ) ≤ T.K by linarith only [hK]).trans
      (hT.2.2.2.2.2.2.2.2.2.2 k).2.2.2.2.1
  have hbudget (k : ℕ) := tailGreen_mass_resistance_budget hT.2.2.1 hB.le
    (tailMass_pos hT k) (tailMass_pos hT (k + 1)) (tailInnerResistance_pos hT k).le
    (tailResistance_pos hT k) (A := tailFundamentalGreenBlockWeight T k) le_rfl
  have hbase (k : ℕ) : g k ≤ H k := by
    have hL := add_nonneg (tailInnerResistance_pos hT k).le (tailResistance_pos hT k).le
    exact (le_add_of_nonneg_left hL).trans (hbudget k).1
  have hreverse (k : ℕ) : |w (T.node (k + 1)) * u (T.node k)| ≤ H k := by
    have hc := tailActualNodeCoupling_pos hT k
    have hcL : 1 / tailActualNodeCoupling T hT k ≤ tailActualEdgeLength T k := by
      apply (div_le_iff₀ hc).mpr
      simpa only [mul_comm] using
        (div_le_iff₀ (tailActualEdgeLength_pos hT k)).mp (tailActualNodeCoupling_lower hT k)
    have hstep : |w (T.node k) * u (T.node (k + 1))| ≤ g k * r k := by
      simpa only [Finset.prod_Ico_succ_top le_rfl, Finset.Ico_self,
        Finset.prod_empty, one_mul, g, r] using hΓ k (k + 1) (Nat.le_succ k)
    exact tailGreen_reverse_node_product_bound hc hcL
      (div_nonneg hB.le (tailMass_pos hT k).le) (hr₁ k) hstep (hbudget k).1 (hcross k)
  exact tailGreen_four_node_product_bounds
    (fun k => div_nonneg hB.le (tailMass_pos hT k).le)
    (fun k => mul_nonneg (add_nonneg (mul_nonneg hB.le hT.2.2.1.le) zero_le_one)
      ((tailFundamentalGreenBlockWeight_one_le hT k).trans' zero_le_one))
    hr₀ hr₁ hΓ hbase (fun k => (hbudget k).2) hreverse hmn

theorem tailActualEdgePoissonPhysical_abs_le_two {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (n : ℕ) (right : Bool)
    {x : ℝ} (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    |tailActualEdgePoissonPhysical T hT n right x| ≤ 2 := by
  have hs := tailActualEdgeChart_mem hT n hx
  rw [tailActualEdgePoissonPhysical_apply,
    abs_of_nonneg (tailActualEdgePoisson_nonneg hT n right hs)]
  exact (tailActualEdgePoisson_le_two_height hT hη n right hs).trans
    ((mul_le_mul_of_nonneg_left (tailActualEdgeAffineHeight_bounds hT n right hs).2
      (by norm_num)).trans_eq (mul_one 2))

theorem tailGreen_actual_interpolant_product_bound {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {B : ℝ} (hB : 0 < B) {w u : ℝ → ℝ}
    (hΓ : ∀ m n, m ≤ n →
      |w (T.node m) * u (T.node n)| ≤ (B / tailMass T m) *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k))
    (hcross : ∀ n, tailActualNodeCoupling T hT n *
      (u (T.node n) * w (T.node (n + 1)) - u (T.node (n + 1)) * w (T.node n)) = 1)
    {m n : ℕ} (hmn : m ≤ n) {x y : ℝ}
    (hx : x ∈ Icc (T.node m) (T.node (m + 1)))
    (hy : y ∈ Icc (T.node n) (T.node (n + 1))) :
    |tailActualEdgeInterpolation T hT m (w (T.node m)) (w (T.node (m + 1))) x *
      tailActualEdgeInterpolation T hT n (u (T.node n)) (u (T.node (n + 1))) y| ≤
      16 * (B * T.Λ + 1) * tailFundamentalGreenBlockWeight T m *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) := by
  obtain ⟨h₀₀, h₀₁, h₁₀, h₁₁⟩ := tailGreen_four_physical_node_bounds hT hK hB hΓ hcross hmn
  have h := tailGreen_two_interpolants_product_le
    (tailActualEdgePoissonPhysical_abs_le_two hT hη m false hx)
    (tailActualEdgePoissonPhysical_abs_le_two hT hη m true hx)
    (tailActualEdgePoissonPhysical_abs_le_two hT hη n false hy)
    (tailActualEdgePoissonPhysical_abs_le_two hT hη n true hy) h₀₀ h₀₁ h₁₀ h₁₁
  simpa only [tailActualEdgeInterpolation, mul_assoc] using h

theorem tailGreen_block_bound_mono {T : DeepTailData}
    (hT : DeepTailHypotheses T) {B C : ℝ} (hB : 0 ≤ B)
    (hC₈ : 8 ≤ C) (hC : 16 * (B * T.Λ + 1) ≤ C) (m n : ℕ) :
    16 * (B * T.Λ + 1) * tailFundamentalGreenBlockWeight T m *
        (∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k)) ≤
      C * tailFundamentalGreenBlockWeight T m * tailFundamentalGreenBlockWeight T n *
        ∏ k ∈ Finset.Ico m n, C / (T.Λ * tailMass T (k + 1) * tailResistance T k) := by
  have hAm := (tailFundamentalGreenBlockWeight_one_le hT m).trans' zero_le_one
  have hAn := (tailFundamentalGreenBlockWeight_one_le hT n).trans' zero_le_one
  have hC₀ : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 8).trans hC₈
  have hden (k : ℕ) : 0 < T.Λ * tailMass T (k + 1) * tailResistance T k :=
    mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (k + 1))) (tailResistance_pos hT k)
  have hp₀ : 0 ≤ ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) :=
    Finset.prod_nonneg fun k _ => div_nonneg (by norm_num) (hden k).le
  have hprod : (∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k)) ≤
      ∏ k ∈ Finset.Ico m n, C / (T.Λ * tailMass T (k + 1) * tailResistance T k) :=
    Finset.prod_le_prod₀ (fun k _ => div_nonneg (by norm_num) (hden k).le)
      (fun k _ => div_le_div_of_nonneg_right hC₈ (hden k).le)
  have hcoeff : 16 * (B * T.Λ + 1) * tailFundamentalGreenBlockWeight T m ≤
      C * tailFundamentalGreenBlockWeight T m * tailFundamentalGreenBlockWeight T n := by
    calc
      _ ≤ C * tailFundamentalGreenBlockWeight T m := mul_le_mul_of_nonneg_right hC hAm
      _ = (C * tailFundamentalGreenBlockWeight T m) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (tailFundamentalGreenBlockWeight_one_le hT n)
        (mul_nonneg hC₀ hAm)
  exact mul_le_mul hcoeff hprod hp₀ (mul_nonneg (mul_nonneg hC₀ hAm) hAn)

/-- The frozen physical block estimate follows from the actual two
fundamental states and their node Green estimate. -/
theorem tailFundamentalGreenKernel_bound {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v w z : ℝ → ℝ}
    (hu : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hw : TailFirstOrderSystem T.p T.Λ w z (Ico T.entrance T.endpoint))
    {B : ℝ} (hB : 0 < B)
    (hΓ : ∀ m n, m ≤ n →
      |w (T.node m) * u (T.node n)| ≤ (B / tailMass T m) *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k))
    (hcross : ∀ n, tailActualNodeCoupling T hT n *
      (u (T.node n) * w (T.node (n + 1)) - u (T.node (n + 1)) * w (T.node n)) = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, m ≤ n →
      ∀ x ∈ Ioo (T.node m) (T.node (m + 1)),
      ∀ y ∈ Ioo (T.node n) (T.node (n + 1)),
        |tailFundamentalGreenKernel T.entrance T.endpoint w u 1 x y| ≤
          C * (1 + tailInnerResistance T m + tailResistance T m + (T.Λ * tailMass T m)⁻¹) *
            (1 + tailInnerResistance T n + tailResistance T n + (T.Λ * tailMass T n)⁻¹) *
            ∏ k ∈ Finset.Ico m n, C / (T.Λ * tailMass T (k + 1) * tailResistance T k) := by
  let C : ℝ := 64 * (B * T.Λ + 1)
  have hD : 0 ≤ B * T.Λ := mul_nonneg hB.le hT.2.2.1.le
  have hC₀ : 0 < C := mul_pos (by norm_num) (by linarith only [hD])
  have hC₈ : 8 ≤ C := by dsimp only [C]; linarith only [hD]
  have hC : 16 * (B * T.Λ + 1) ≤ C := by dsimp only [C]; linarith only [hD]
  have hinterp {f q : ℝ → ℝ}
      (hs : TailFirstOrderSystem T.p T.Λ f q (Ico T.entrance T.endpoint))
      (k : ℕ) {t : ℝ} (ht : t ∈ Icc (T.node k) (T.node (k + 1))) :
      f t = tailActualEdgeInterpolation T hT k (f (T.node k)) (f (T.node (k + 1))) t := by
    have hc : ContinuousOn f (Icc (T.node k) (T.node (k + 1))) :=
      fun x hx => (hs x (tailActualEdge_interval_subset hT k hx)).1.continuousAt.continuousWithinAt
    have hq : ContinuousOn q (Icc (T.node k) (T.node (k + 1))) :=
      fun x hx => (hs x (tailActualEdge_interval_subset hT k hx)).2.continuousAt.continuousWithinAt
    exact (tailActualEdge_solution_eq_interpolation hT k hc hq
      (hs.mono (fun x hx => tailActualEdge_interval_subset hT k (Ioo_subset_Icc_self hx))) ht).1
  refine ⟨C, hC₀, ?_⟩
  intro m n hmn x hx y hy
  have hxT : x ∈ Ioo T.entrance T.endpoint :=
    ⟨(deepTail_entrance_le_node hT m).trans_lt hx.1,
      hx.2.trans (deepTail_node_lt_endpoint hT (m + 1))⟩
  have hyT : y ∈ Ioo T.entrance T.endpoint :=
    ⟨(deepTail_entrance_le_node hT n).trans_lt hy.1,
      hy.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩
  have hpoints : min x y ∈ Icc (T.node m) (T.node (m + 1)) ∧
      max x y ∈ Icc (T.node n) (T.node (n + 1)) := by
    rcases lt_or_eq_of_le hmn with hlt | rfl
    · have hxy : x ≤ y := hx.2.le.trans
        (((deepTail_node_strictMono hT).monotone (Nat.succ_le_of_lt hlt)).trans hy.1.le)
      simpa only [min_eq_left hxy, max_eq_right hxy] using
        And.intro (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)
    · exact ⟨⟨le_min hx.1.le hy.1.le, (min_le_left _ _).trans hx.2.le⟩,
        ⟨hx.1.le.trans (le_max_left _ _), max_le hx.2.le hy.2.le⟩⟩
  rw [tailFundamentalGreenKernel_eq hxT hyT, div_one,
    hinterp hw m hpoints.1, hinterp hu n hpoints.2]
  exact (tailGreen_actual_interpolant_product_bound hT hη hK hB hΓ hcross hmn
    hpoints.1 hpoints.2).trans
      (tailGreen_block_bound_mono hT hB.le hC₈ hC m n)

end ContinuousFlexibility.Radial
