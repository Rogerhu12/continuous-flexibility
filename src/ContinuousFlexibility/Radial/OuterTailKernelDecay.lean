module

public import ContinuousFlexibility.Radial.OuterDecayProducts
public import ContinuousFlexibility.Radial.TailFundamentalGreenBounds
public import ContinuousFlexibility.Radial.TailFundamentalStates

/-!
# The actual tail kernel with a uniform prefactor

The same two fundamental states are evaluated at the two physical points.
Their explicit normalized node estimate gives the numerical prefactor 144,
before the physical mass-resistance products are converted to cubic decay.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem outer_tail_state_eq_interpolation {T : DeepTailData}
    (hT : DeepTailHypotheses T) {f q : ℝ → ℝ}
    (hf : TailFirstOrderSystem T.p T.Λ f q (Ico T.entrance T.endpoint))
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    f x = tailActualEdgeInterpolation T hT n (f (T.node n)) (f (T.node (n + 1))) x := by
  have hi := tailActualEdge_interval_subset hT n
  exact (tailActualEdge_solution_eq_interpolation hT n
    (HasDerivAt.continuousOn (fun t ht => (hf t (hi ht)).1))
    (HasDerivAt.continuousOn (fun t ht => (hf t (hi ht)).2))
    (hf.mono (Ioo_subset_Icc_self.trans hi)) hx).1

theorem outer_tail_min_max_edges {T : DeepTailData}
    (hT : DeepTailHypotheses T) {m n : ℕ} (hmn : m ≤ n) {x y : ℝ}
    (hx : x ∈ Icc (T.node m) (T.node (m + 1)))
    (hy : y ∈ Icc (T.node n) (T.node (n + 1))) :
    min x y ∈ Icc (T.node m) (T.node (m + 1)) ∧
      max x y ∈ Icc (T.node n) (T.node (n + 1)) := by
  rcases lt_or_eq_of_le hmn with hlt | rfl
  · have hxy : x ≤ y := hx.2.trans
      (((deepTail_node_strictMono hT).monotone (Nat.succ_le_of_lt hlt)).trans hy.1)
    simpa only [min_eq_left hxy, max_eq_right hxy] using And.intro hx hy
  · exact ⟨⟨le_min hx.1 hy.1, (min_le_left _ _).trans hx.2⟩,
      ⟨hx.1.trans (le_max_left _ _), max_le hx.2 hy.2⟩⟩

/-- An explicit node bound on the actual pair yields a uniform physical kernel bound. -/
theorem outer_tail_kernel_product_bound {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {P ZP Q ZQ : ℝ → ℝ}
    (hP : TailFirstOrderSystem T.p T.Λ P ZP (Ico T.entrance T.endpoint))
    (hQ : TailFirstOrderSystem T.p T.Λ Q ZQ (Ico T.entrance T.endpoint))
    (hW : ∀ x ∈ Ico T.entrance T.endpoint, ZQ x * P x - Q x * ZP x = 1)
    (hΓ : ∀ m n, m ≤ n →
      |Q (T.node m) * P (T.node n)| ≤ ((8 / T.Λ) / tailMass T m) *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k))
    {m n : ℕ} (hmn : m ≤ n) {x y : ℝ}
    (hx : x ∈ Icc (T.node m) (T.node (m + 1)))
    (hy : y ∈ Icc (T.node n) (T.node (n + 1))) :
    |Q (min x y) * P (max x y)| ≤
      144 * tailFundamentalGreenBlockWeight T m *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) := by
  have hpoints := outer_tail_min_max_edges hT hmn hx hy
  rw [outer_tail_state_eq_interpolation hT hQ m hpoints.1,
    outer_tail_state_eq_interpolation hT hP n hpoints.2]
  have h := tailGreen_actual_interpolant_product_bound hT hη hK
    (div_pos (by norm_num : (0 : ℝ) < 8) hT.2.2.1) hΓ
    (tailActualState_discrete_wronskian hT hP hQ hW) hmn hpoints.1 hpoints.2
  have hc : 16 * ((8 / T.Λ) * T.Λ + 1) = (144 : ℝ) := by
    rw [div_mul_cancel₀ _ hT.2.2.1.ne']
    norm_num
  simpa only [hc] using h

/-- The actual two-point kernel retains the full cubic attenuation exponent. -/
theorem outer_tail_kernel_envelope {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {P ZP Q ZQ : ℝ → ℝ}
    (hP : TailFirstOrderSystem T.p T.Λ P ZP (Ico T.entrance T.endpoint))
    (hQ : TailFirstOrderSystem T.p T.Λ Q ZQ (Ico T.entrance T.endpoint))
    (hW : ∀ x ∈ Ico T.entrance T.endpoint, ZQ x * P x - Q x * ZP x = 1)
    (hΓ : ∀ m n, m ≤ n →
      |Q (T.node m) * P (T.node n)| ≤ ((8 / T.Λ) / tailMass T m) *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k))
    {C : ℝ} (hC : 0 ≤ C) (start : ℕ)
    (hden : ∀ k, exp (2 * ((start + k : ℕ) : ℝ) ^ 2 -
      C * (((start + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + k : ℕ))) ≤
        T.Λ * tailMass T (k + 1) * tailResistance T k)
    {m n : ℕ} (hmn : m ≤ n) {x y : ℝ}
    (hx : x ∈ Icc (T.node m) (T.node (m + 1)))
    (hy : y ∈ Icc (T.node n) (T.node (n + 1))) :
    |Q (min x y) * P (max x y)| ≤
      144 * tailFundamentalGreenBlockWeight T m *
        radialE (start + n) ^ outerPhysicalDecayCost C *
          exp (-|radialS (start + n) - radialS (start + m)|) := by
  calc
    _ ≤ 144 * tailFundamentalGreenBlockWeight T m *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) :=
      outer_tail_kernel_product_bound hT hη hK hP hQ hW hΓ hmn hx hy
    _ ≤ (144 * tailFundamentalGreenBlockWeight T m) *
        (radialE (start + n) ^ outerPhysicalDecayCost C *
          exp (-|radialS (start + n) - radialS (start + m)|)) :=
      mul_le_mul_of_nonneg_left (outer_physical_decay_product_envelope hC start hden hmn)
        (mul_nonneg (by norm_num)
          (zero_le_one.trans (tailFundamentalGreenBlockWeight_one_le hT m)))
    _ = _ := by ring

end ContinuousFlexibility.Radial
