module

public import ContinuousFlexibility.Radial.TailNaturalIntegrability
public import ContinuousFlexibility.Radial.TailNaturalEquationState
public import ContinuousFlexibility.Radial.TailNaturalNodeBounds
public import ContinuousFlexibility.Radial.TailNodeMassRecovery

/-!
# Quantitative weighted norms of the actual natural tail

The physical mass--resistance decay controls the sum of squared node
masses. Integrating the already constructed Poisson interpolation on the
actual disjoint edges turns this into a bound for the whole outward tail.
These estimates retain the first physical mass, as required in Lemma 6.4.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Both mass--resistance inequalities are used: one contracts the node
value and the other contracts its mass-weighted absolute value. Their
product contracts the squared node mass by a factor of sixteen. -/
theorem tailNaturalNode_square_step {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hK : 32 ≤ T.K) {a : ℕ → ℝ}
    (hstep : ∀ n, |a (n + 1)| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |a n|) (n : ℕ) :
    tailMass T (n + 1) * a (n + 1) ^ 2 ≤
      (1 / 16) * (tailMass T n * a n ^ 2) := by
  have hKpos : 0 < T.K := by linarith
  have hden : 0 < T.Λ * tailMass T (n + 1) * tailResistance T n :=
    mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (n + 1))) (tailResistance_pos hT n)
  have hleft := (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.1
  have hright := (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.1
  have hq : 8 / T.K ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hKpos).mpr
    linarith
  have hf : 8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hvalue : |a (n + 1)| ≤ (1 / 4 : ℝ) * |a n| :=
    (hstep n).trans (mul_le_mul_of_nonneg_right hf (abs_nonneg _))
  have hmassfactor : tailMass T (n + 1) *
      (8 / (T.Λ * tailMass T (n + 1) * tailResistance T n)) ≤
      (1 / 4 : ℝ) * tailMass T n := by
    exact (tailNode_decay_mass_factor hT.2.2.1 hKpos
      (tailMass_pos hT (n + 1)) (tailResistance_pos hT n) hleft).trans
      (mul_le_mul_of_nonneg_right hq (tailMass_pos hT n).le)
  have hmass : tailMass T (n + 1) * |a (n + 1)| ≤
      (1 / 4 : ℝ) * (tailMass T n * |a n|) := by
    calc
      _ ≤ tailMass T (n + 1) *
          ((8 / (T.Λ * tailMass T (n + 1) * tailResistance T n)) * |a n|) :=
        mul_le_mul_of_nonneg_left (hstep n) (tailMass_pos hT (n + 1)).le
      _ = (tailMass T (n + 1) *
          (8 / (T.Λ * tailMass T (n + 1) * tailResistance T n))) * |a n| := by ring
      _ ≤ ((1 / 4 : ℝ) * tailMass T n) * |a n| :=
        mul_le_mul_of_nonneg_right hmassfactor (abs_nonneg _)
      _ = _ := by ring
  rw [← sq_abs (a (n + 1)), ← sq_abs (a n)]
  calc
    _ = (tailMass T (n + 1) * |a (n + 1)|) * |a (n + 1)| := by ring
    _ ≤ ((1 / 4 : ℝ) * (tailMass T n * |a n|)) * ((1 / 4 : ℝ) * |a n|) :=
      mul_le_mul hmass hvalue (abs_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg (tailMass_pos hT n).le (abs_nonneg _)))
    _ = _ := by ring

/-- The total squared node mass is controlled by twice the first squared
node mass. This conclusion is derived from the physical decay inequality. -/
theorem tailNaturalNode_square_sum_bound {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hK : 32 ≤ T.K) {a : ℕ → ℝ}
    (hstep : ∀ n, |a (n + 1)| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |a n|) :
    Summable (fun n => tailMass T n * a n ^ 2) ∧
      (∑' n, tailMass T n * a n ^ 2) ≤ 2 * (tailMass T 0 * a 0 ^ 2) := by
  let v : ℕ → ℝ := fun n => tailMass T n * a n ^ 2
  have hv (n : ℕ) : 0 ≤ v n := mul_nonneg (tailMass_pos hT n).le (sq_nonneg _)
  have hs (n : ℕ) : v (n + 1) ≤ (0 : ℝ) * 0 + (1 / 16 : ℝ) * v n := by
    simpa only [zero_mul, zero_add] using tailNaturalNode_square_step hT hK hstep n
  have hz : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hsum := tailNode_mass_summable_of_step hv (fun _ => (le_rfl : (0 : ℝ) ≤ 0))
    (le_rfl : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    (by norm_num : (1 / 16 : ℝ) < 1) hs hz
  have hbound := tailNode_mass_tsum_le hv (fun _ => (le_rfl : (0 : ℝ) ≤ 0))
    (le_rfl : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    (by norm_num : (1 / 16 : ℝ) < 1) hs hz
  refine ⟨hsum, ?_⟩
  change (∑' n, v n) ≤ 2 * v 0
  norm_num at hbound
  nlinarith only [hbound, hv 0]

theorem deepTail_halfOpen_edges_pairwiseDisjoint {T : DeepTailData}
    (hT : DeepTailHypotheses T) :
    Pairwise (fun m n : ℕ =>
      Disjoint (Ico (T.node m) (T.node (m + 1))) (Ico (T.node n) (T.node (n + 1)))) := by
  have hdis (m n : ℕ) (hmn : m < n) :
      Disjoint (Ico (T.node m) (T.node (m + 1))) (Ico (T.node n) (T.node (n + 1))) := by
    apply Set.disjoint_left.mpr
    intro x hxm hxn
    have hnodes := (deepTail_node_strictMono hT).monotone (Nat.succ_le_of_lt hmn)
    exact (not_lt_of_ge (hnodes.trans hxn.1)) hxm.2
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hdis m n h
  · exact (hdis n m h).symm

theorem deepTail_iUnion_halfOpen_edges {T : DeepTailData} (hT : DeepTailHypotheses T) :
    (⋃ n : ℕ, Ico (T.node n) (T.node (n + 1))) = Ico (T.node 0) T.endpoint := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact ⟨((deepTail_node_strictMono hT).monotone (Nat.zero_le n)).trans hn.1,
      hn.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩
  · intro hx
    obtain ⟨n, hn⟩ := morse_outward_block_exists hT.2.2.2.2.2.2.2.2.2.1 hx.1 hx.2
    exact mem_iUnion.mpr ⟨n, hn⟩

/-- Summing the actual Poisson edge estimates bounds the full outward
integral by sixteen times the sum of physical squared node masses. -/
theorem tailPoissonInterpolation_sq_integral_le_node_sum {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {a : ℕ → ℝ} (ha : Summable (fun n => tailMass T n * a n ^ 2)) :
    (∫ x in Ico (T.node 0) T.endpoint, T.p x * tailPoissonInterpolation T hT a x ^ 2) ≤
      16 * (∑' n, tailMass T n * a n ^ 2) := by
  let v : ℕ → ℝ := fun n => tailMass T n * a n ^ 2
  let f : ℝ → ℝ := fun x => T.p x * tailPoissonInterpolation T hT a x ^ 2
  have hshift : Summable (fun n => v (n + 1)) := (summable_nat_add_iff 1).mpr ha
  have hsum : Summable (fun n => 8 * (v n + v (n + 1))) := (ha.add hshift).mul_left 8
  have hf : IntegrableOn f (⋃ n : ℕ, Ico (T.node n) (T.node (n + 1))) := by
    rw [deepTail_iUnion_halfOpen_edges hT]
    exact tailPoissonInterpolation_weighted_sq_integrableOn hT hη hK ha
  have hedge := hasSum_integral_iUnion (fun _ : ℕ => measurableSet_Ico)
    (deepTail_halfOpen_edges_pairwiseDisjoint hT) hf
  have hlocal (n : ℕ) :
      (∫ x in Ico (T.node n) (T.node (n + 1)), f x) ≤ 8 * (v n + v (n + 1)) := by
    rw [integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (tailActualEdge_order hT n).le]
    calc
      _ = ∫ x in T.node n..T.node (n + 1),
          T.p x * tailActualEdgeInterpolation T hT n (a n) (a (n + 1)) x ^ 2 := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (tailActualEdge_order hT n).le]
        intro x hx
        dsimp only [f]
        rw [tailPoissonInterpolation_apply_closed hT a hx]
      _ ≤ _ := tailActualEdgeInterpolation_sq_integral_le hT hη hK n (a n) (a (n + 1))
  have hshiftle : (∑' n, v (n + 1)) ≤ ∑' n, v n := by
    have hsplit := ha.tsum_eq_zero_add
    change (∑' n, v n) = v 0 + ∑' n, v (n + 1) at hsplit
    linarith only [hsplit, mul_nonneg (tailMass_pos hT 0).le (sq_nonneg (a 0))]
  calc
    (∫ x in Ico (T.node 0) T.endpoint, f x) =
        ∑' n, ∫ x in Ico (T.node n) (T.node (n + 1)), f x := by
      rw [← deepTail_iUnion_halfOpen_edges hT]
      exact hedge.tsum_eq.symm
    _ ≤ ∑' n, 8 * (v n + v (n + 1)) := Summable.tsum_le_tsum hlocal hedge.summable hsum
    _ = 8 * ((∑' n, v n) + ∑' n, v (n + 1)) := by
      rw [tsum_mul_left, ha.tsum_add hshift]
    _ ≤ 16 * (∑' n, v n) := by linarith only [hshiftle]

theorem tailPoissonInterpolation_sq_integral_le_first_mass {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) {a : ℕ → ℝ}
    (hstep : ∀ n, |a (n + 1)| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |a n|) :
    (∫ x in Ico (T.node 0) T.endpoint, T.p x * tailPoissonInterpolation T hT a x ^ 2) ≤
      32 * tailMass T 0 * a 0 ^ 2 := by
  obtain ⟨hasum, habound⟩ := tailNaturalNode_square_sum_bound hT hK hstep
  have hout := tailPoissonInterpolation_sq_integral_le_node_sum hT hη hK hasum
  nlinarith only [hout, habound]

/-- This bound is for the actual classical natural solution itself. Its
identification with the Poisson interpolation follows from the equation,
not from an extra interpolation hypothesis. -/
theorem tailNaturalEquation_outward_sq_integral_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u : ℝ → ℝ} (hu : TailNaturalEquation T u)
    (hstep : ∀ n, |u (T.node (n + 1))| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |u (T.node n)|) :
    (∫ x in Ico (T.node 0) T.endpoint, T.p x * u x ^ 2) ≤
      32 * tailMass T 0 * u (T.node 0) ^ 2 := by
  let a : ℕ → ℝ := fun n => u (T.node n)
  have hco : Ico (T.node 0) T.endpoint ⊆ Ico T.entrance T.endpoint :=
    fun _ hx => ⟨(deepTail_entrance_le_node hT 0).trans hx.1, hx.2⟩
  have hoo : Ioo (T.node 0) T.endpoint ⊆ Ioo T.entrance T.endpoint :=
    fun _ hx => ⟨(deepTail_entrance_le_node hT 0).trans_lt hx.1, hx.2⟩
  have hucont := (tailNaturalEquation_continuousOn hu).mono hco
  have hvcont := (tailNaturalEquation_flux_continuousOn hT hu).mono hco
  have hsys := (tailNaturalEquation_system hT hu).mono hoo
  have heq : EqOn u (tailPoissonInterpolation T hT a) (Ico (T.node 0) T.endpoint) := by
    intro x hx
    obtain ⟨n, hn⟩ := morse_outward_block_exists hT.2.2.2.2.2.2.2.2.2.1 hx.1 hx.2
    have hncc : x ∈ Icc (T.node n) (T.node (n + 1)) := ⟨hn.1, hn.2.le⟩
    rw [tailPoissonInterpolation_apply_closed hT a hncc]
    exact (tailActualEdge_solution_eq_interpolation hT n
      (hucont.mono (tailActualEdge_subset_outward hT n))
      (hvcont.mono (tailActualEdge_subset_outward hT n))
      (hsys.mono (tailActualEdge_interior_subset_outward hT n)) hncc).1
  calc
    _ = ∫ x in Ico (T.node 0) T.endpoint,
        T.p x * tailPoissonInterpolation T hT a x ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      change T.p x * u x ^ 2 = T.p x * tailPoissonInterpolation T hT a x ^ 2
      rw [heq hx]
    _ ≤ _ := tailPoissonInterpolation_sq_integral_le_first_mass hT hη hK hstep

/-- At a mass entrance the actual weighted norm has the first-mass scale. -/
theorem tailNaturalEquation_massEntrance_sq_integral_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    (hentry : T.node 0 = T.entrance) {u : ℝ → ℝ} (hu : TailNaturalEquation T u)
    (hstep : ∀ n, |u (T.node (n + 1))| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |u (T.node n)|) :
    (∫ x, u x ^ 2 ∂deepTailMeasure T) ≤ 32 * tailMass T 0 * u T.entrance ^ 2 := by
  rw [tail_integral_density ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
    (fun x hx => deepTail_pos hT x ⟨hx.1.le, hx.2⟩), ← hentry,
    ← integral_Ico_eq_integral_Ioo]
  exact tailNaturalEquation_outward_sq_integral_le hT hη hK hu hstep

end ContinuousFlexibility.Radial
