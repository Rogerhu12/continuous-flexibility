import ContinuousFlexibility.Analysis.JointJetInterpolationBudget
import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Fixed-loss composition of weighted joint jets

The joint derivative order includes parameter and spatial directions.
Only the parameter component enters the grading of the base point.
Finite-partition interpolation leaves one high factor, and component
powers stay explicit. The low order and loss precede both the low-ball
radius and every derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E P F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def UniformWeightedJointGrowth
    (p : ℕ → Seminorm ℝ E) (W : I → ℝ)
    {U : Set E} {V : I → Set P} {f : I → E × P → F}
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)) (base loss : ℕ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ n : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
    ∀ i x, x ∈ U → p base x ≤ R → ∀ y ∈ V i, ∀ v : Fin n → E × P,
      (∀ j, p base (v j).1 + ‖(v j).2‖ ≤ 1) →
      ‖(J i).D n (x, y) v‖ ≤ C * W i ^ Q *
        (1 + p (n + loss) x + ∑ j : Fin n, p (n + loss) (v j).1)

theorem UniformWeightedJointGrowth.congr
    {p : ℕ → Seminorm ℝ E} {W : I → ℝ}
    {U : Set E} {V : I → Set P} {f g : I → E × P → F}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (g i))
    (heq : ∀ i z, z ∈ U ×ˢ V i → f i z = g i z) :
    UniformWeightedJointGrowth p W K base loss := by
  intro R hR n
  obtain ⟨C, Q, hC, hQ, hb⟩ := hJ R hR n
  refine ⟨C, Q, hC, hQ, fun i x hx hlow y hy v hv => ?_⟩
  rw [(K i).unique ((J i).congrOn (heq i)) n (x, y) ⟨hx, hy⟩]
  exact hb i x hx hlow y hy v hv

/-- Ordinary smooth postcomposition preserves a fixed joint loss when
the outer Taylor jets have uniform component-power bounds. -/
theorem UniformWeightedJointGrowth.comp_contDiff
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hIp : HasInterpolation p)
    {W : I → ℝ} (hW : ∀ i, 1 ≤ W i)
    {U : Set E} {V : I → Set P} {f : I → E × P → F}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {base loss : ℕ} (hJ : UniformWeightedJointGrowth p W J base loss)
    {Z : Set F} {g : F → G} (hZ : IsOpen Z) (hg : ContDiffOn ℝ ∞ g Z)
    (hmap : ∀ i, MapsTo (f i) (U ×ˢ V i) Z) (outerBase : ℕ)
    (houter : ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p outerBase x ≤ R → ∀ y ∈ V i,
        ‖contDiffOnJetFamily g Z k (f i (x, y))‖ ≤ C * W i ^ Q) :
    ∃ B L : ℕ, base ≤ B ∧ outerBase ≤ B ∧
      UniformWeightedJointGrowth p W
        (fun i => (J i).comp_contDiff hZ hg (hmap i)) B L := by
  classical
  obtain ⟨B, L, hB, hbudget⟩ :=
    hasInterpolation_partition_affine_growth p hp hIp (max base outerBase) loss
  have hb : base ≤ B := (le_max_left _ _).trans hB
  have ho : outerBase ≤ B := (le_max_right _ _).trans hB
  refine ⟨B, L, hb, ho, ?_⟩
  intro R hR N
  have hterm (c : OrderedFinpartition N) : ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ y ∈ V i, ∀ v : Fin N → E × P,
      (∀ j, p B (v j).1 + ‖(v j).2‖ ≤ 1) →
      ‖contDiffOnJetFamily g Z c.length (f i (x, y))
        (fun j => (J i).D (c.partSize j) (x, y) (v ∘ c.emb j))‖ ≤
        A * W i ^ Q * (1 + p (N + L) x + ∑ j : Fin N, p (N + L) (v j).1) := by
    obtain ⟨A, Q, hA, hQ, hAb⟩ := houter R hR c.length
    choose C P₀ hC hP hCb using fun j : Fin c.length => hJ R hR (c.partSize j)
    obtain ⟨K, hK, hKb⟩ := hbudget R hR N c
    refine ⟨A * (∏ j, C j) * K, Q + ∑ j, P₀ j,
      mul_nonneg (mul_nonneg hA (Finset.prod_nonneg (fun j _ => hC j))) hK,
      add_nonneg hQ (Finset.sum_nonneg (fun j _ => hP j)), ?_⟩
    intro i x hx hlow y hy v hv
    have hWpos : 0 < W i := zero_lt_one.trans_le (hW i)
    let a : Fin c.length → ℝ := fun j => 1 + p (c.partSize j + loss) x +
      ∑ k : Fin (c.partSize j), p (c.partSize j + loss) (v (c.emb j k)).1
    have ha (j : Fin c.length) : 0 ≤ a j := by dsimp only [a]; positivity
    have hinner (j : Fin c.length) :
        ‖(J i).D (c.partSize j) (x, y) (v ∘ c.emb j)‖ ≤ C j * W i ^ P₀ j * a j := by
      apply hCb j i x hx ((hp hb x).trans hlow) y hy (v ∘ c.emb j)
      intro k
      exact (add_le_add (hp hb (v (c.emb j k)).1) le_rfl).trans (hv (c.emb j k))
    have hprod : (∏ j : Fin c.length, C j * W i ^ P₀ j * a j) =
        (∏ j, C j) * W i ^ (∑ j, P₀ j) * ∏ j, a j := by
      rw [Real.rpow_sum_of_pos hWpos]
      simp only [Finset.prod_mul_distrib]
    have hprod0 : 0 ≤ ∏ j : Fin c.length, C j := Finset.prod_nonneg (fun j _ => hC j)
    have hscale0 : 0 ≤ A * (∏ j, C j) * W i ^ (Q + ∑ j, P₀ j) :=
      mul_nonneg (mul_nonneg hA hprod0) (Real.rpow_nonneg hWpos.le _)
    have hinterp : (∏ j : Fin c.length, a j) ≤
        K * (1 + p (N + L) x + ∑ j : Fin N, p (N + L) (v j).1) := by
      exact hKb x (fun j => (v j).1) hlow (fun j =>
        (le_add_of_nonneg_right (norm_nonneg (v j).2)).trans (hv j))
    calc
      _ ≤ (A * W i ^ Q) * ∏ j : Fin c.length, C j * W i ^ P₀ j * a j :=
        ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
          (hAb i x hx ((hp ho x).trans hlow) y hy) hinner
      _ = (A * (∏ j, C j) * W i ^ (Q + ∑ j, P₀ j)) * ∏ j, a j := by
        rw [hprod, Real.rpow_add hWpos]
        ring
      _ ≤ (A * (∏ j, C j) * W i ^ (Q + ∑ j, P₀ j)) *
          (K * (1 + p (N + L) x + ∑ j : Fin N, p (N + L) (v j).1)) :=
        mul_le_mul_of_nonneg_left hinterp hscale0
      _ = _ := by ring
  choose C Q hC hQ hCb using hterm
  let A : ℝ := ∑ c : OrderedFinpartition N, C c
  let P₀ : ℝ := ∑ c : OrderedFinpartition N, Q c
  have hA : 0 ≤ A := Finset.sum_nonneg (fun c _ => hC c)
  have hP : 0 ≤ P₀ := Finset.sum_nonneg (fun c _ => hQ c)
  refine ⟨A, P₀, hA, hP, ?_⟩
  intro i x hx hlow y hy v hv
  rw [(J i).comp_contDiff_apply]
  have hweight : 0 ≤ 1 + p (N + L) x + ∑ j : Fin N, p (N + L) (v j).1 := by
    positivity
  calc
    _ ≤ ∑ c : OrderedFinpartition N,
        ‖contDiffOnJetFamily g Z c.length (f i (x, y))
          (fun j => (J i).D (c.partSize j) (x, y) (v ∘ c.emb j))‖ := norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition N, C c * W i ^ P₀ *
        (1 + p (N + L) x + ∑ j : Fin N, p (N + L) (v j).1) := by
      apply Finset.sum_le_sum
      intro c _
      have hc : Q c ≤ P₀ := Finset.single_le_sum (fun d _ => hQ d) (Finset.mem_univ c)
      exact (hCb c i x hx hlow y hy v hv).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hW i) hc) (hC c)) hweight)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

end ContinuousFlexibility.Analysis
