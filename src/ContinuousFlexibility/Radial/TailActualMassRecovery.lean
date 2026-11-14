module

public import ContinuousFlexibility.Radial.TailNaturalEquationState
public import ContinuousFlexibility.Radial.TailNodeMassRecovery

/-!
# Recovering actual node masses from a square-integrable solution

The recurrence eliminates the next node from the Poisson interpolation on
the current mass interval. The coefficient of the current node remains
at least one half, while the previous-node error is controlled by both
large mass--resistance products. Summing the resulting one-sided estimate
proves node square summability without assuming it in advance.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

private theorem tail_mass_value_square_bound {a z w φ ψ B : ℝ}
    (hφ : (1 / 2 : ℝ) ≤ φ) (hψ₀ : 0 ≤ ψ) (hψ : ψ ≤ B)
    (hz : z = φ * a - ψ * w) : a ^ 2 ≤ 8 * z ^ 2 + 8 * B ^ 2 * w ^ 2 := by
  have hφsq : (1 / 4 : ℝ) ≤ φ ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hφ 2
    norm_num at h ⊢
    exact h
  have hψsq := pow_le_pow_left₀ hψ₀ hψ 2
  have ha := mul_le_mul_of_nonneg_right hφsq (sq_nonneg a)
  have hw := mul_le_mul_of_nonneg_right hψsq (sq_nonneg w)
  have hmain : (φ * a) ^ 2 ≤ 2 * z ^ 2 + 2 * (ψ * w) ^ 2 := by
    rw [show φ * a = z + ψ * w by linarith only [hz]]
    nlinarith only [sq_nonneg (z - ψ * w)]
  nlinarith only [ha, hw, hmain]

theorem tailActualEdgeChart_mass_mem {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (T.node n) (T.massEnd n)) :
    tailActualEdgeChart T hT n x ∈ Icc 0 (tailInnerResistance T n) := by
  constructor
  · calc
      0 = tailActualEdgeChart T hT n (T.node n) := (tailActualEdgeChart_left hT n).symm
      _ ≤ tailActualEdgeChart T hT n x := (tailActualEdgeChart_strictMono hT n).monotone hx.1
  · calc
      tailActualEdgeChart T hT n x ≤ tailActualEdgeChart T hT n (T.massEnd n) :=
        (tailActualEdgeChart_strictMono hT n).monotone hx.2
      _ = tailInnerResistance T n := tailActualEdgeChart_massEnd hT n

/-- Both physical Poisson columns obey their mass-side affine bounds. -/
theorem tailActualEdgePoissonPhysical_mass_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (n : ℕ) (right : Bool) {x : ℝ}
    (hx : x ∈ Icc (T.node n) (T.massEnd n)) :
    (if right then 0 else 1 - T.η / T.K) ≤ tailActualEdgePoissonPhysical T hT n right x ∧
      tailActualEdgePoissonPhysical T hT n right x ≤
        2 * (if right then tailInnerResistance T n / tailActualEdgeLength T n else 1) := by
  have hs := tailActualEdgeChart_mass_mem hT n hx
  have hs' := tailActualEdge_mass_subset hT n hs
  have hb := tailActualEdgeAffineHeight_mass_bounds hT n right hs
  rw [tailActualEdgePoissonPhysical_apply]
  exact ⟨hb.1.trans (tailActualEdgePoisson_bounds_eta hT n right hs').1,
    (tailActualEdgePoisson_le_two_height hT hη n right hs').trans
      (mul_le_mul_of_nonneg_left hb.2 (by norm_num))⟩

/-- Elimination of the forward neighbor leaves a coercive coefficient on the current mass cell. -/
theorem tailActualEdgeInterpolation_recovery_pointwise {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    (n : ℕ) {a b e : ℝ}
    (hrec : -tailActualInteriorDiagonal T hT n * b =
      tailActualNodeCoupling T hT n * a + tailActualNodeCoupling T hT (n + 1) * e)
    {x : ℝ} (hx : x ∈ Icc (T.node (n + 1)) (T.massEnd (n + 1))) :
    b ^ 2 ≤ 8 * tailActualEdgeInterpolation T hT (n + 1) b e x ^ 2 +
      32 * (tailInnerResistance T (n + 1) * tailActualNodeCoupling T hT n) ^ 2 * a ^ 2 := by
  let r : ℝ := tailInnerResistance T (n + 1)
  let c : ℝ := tailActualNodeCoupling T hT (n + 1)
  let c₀ : ℝ := tailActualNodeCoupling T hT n
  let d : ℝ := tailActualInteriorDiagonal T hT n
  let v₀ : ℝ := tailActualEdgePoissonPhysical T hT (n + 1) false x
  let v₁ : ℝ := tailActualEdgePoissonPhysical T hT (n + 1) true x
  let t : ℝ := v₁ / c
  have hr : 0 < r := tailInnerResistance_pos hT (n + 1)
  have hc : 0 < c := tailActualNodeCoupling_pos hT (n + 1)
  have hc₀ : 0 < c₀ := tailActualNodeCoupling_pos hT n
  have hd : 0 ≤ d := (tailActualInteriorDiagonal_pos hT hη hK n).le
  have hd_upper : d ≤ 2 * (T.Λ * tailMass T (n + 1)) :=
    (tailActualInteriorDiagonal_bounds hT hη hK n).2
  have hv₀ : 1 - T.η / T.K ≤ v₀ :=
    (tailActualEdgePoissonPhysical_mass_bounds hT hη (n + 1) false hx).1
  have hv₁ : 0 ≤ v₁ ∧ v₁ ≤ 2 * (r / tailActualEdgeLength T (n + 1)) :=
    tailActualEdgePoissonPhysical_mass_bounds hT hη (n + 1) true hx
  have ht₀ : 0 ≤ t := div_nonneg hv₁.1 hc.le
  have ht : t ≤ 2 * r := by
    apply (div_le_iff₀ hc).mpr
    calc
      v₁ ≤ 2 * (r / tailActualEdgeLength T (n + 1)) := hv₁.2
      _ = (2 * r) * (1 / tailActualEdgeLength T (n + 1)) := by ring
      _ ≤ (2 * r) * c := mul_le_mul_of_nonneg_left
        (tailActualNodeCoupling_lower hT (n + 1)) (mul_nonneg (by norm_num) hr.le)
  have hdt : d * t ≤ 4 * T.η := by
    calc
      d * t ≤ d * (2 * r) := mul_le_mul_of_nonneg_left ht hd
      _ = 2 * (d * r) := by ring
      _ ≤ 2 * ((2 * (T.Λ * tailMass T (n + 1))) * r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd_upper hr.le) (by norm_num)
      _ = 4 * (T.Λ * tailMass T (n + 1) * r) := by ring
      _ ≤ 4 * T.η := mul_le_mul_of_nonneg_left
        (deepTail_mass_resistance_small hT (n + 1)) (by norm_num)
  have hratio : T.η / T.K ≤ 1 / 16 :=
    (div_le_self hT.2.2.2.2.1.le hT.2.2.2.2.2.2.1.le).trans hη
  have hφ : (1 / 2 : ℝ) ≤ v₀ - d * t := by
    linarith only [hv₀, hdt, hratio, hη]
  have hψ₀ : 0 ≤ c₀ * t := mul_nonneg hc₀.le ht₀
  have hψ : c₀ * t ≤ 2 * r * c₀ := by
    calc
      c₀ * t ≤ c₀ * (2 * r) := mul_le_mul_of_nonneg_left ht hc₀.le
      _ = 2 * r * c₀ := by ring
  have hct : c * t = v₁ := by
    dsimp only [t]
    field_simp [hc.ne']
  have hrec' : -d * b = c₀ * a + c * e := hrec
  have hrect : -d * b * t = c₀ * a * t + e * v₁ := by
    calc
      _ = (c₀ * a + c * e) * t := congrArg (fun z : ℝ => z * t) hrec'
      _ = c₀ * a * t + e * (c * t) := by ring
      _ = c₀ * a * t + e * v₁ := by rw [hct]
  have hz : b * v₀ + e * v₁ = (v₀ - d * t) * b - (c₀ * t) * a := by
    nlinarith only [hrect]
  have hpoint := tail_mass_value_square_bound hφ hψ₀ hψ hz
  calc
    b ^ 2 ≤ 8 * (b * v₀ + e * v₁) ^ 2 + 8 * (2 * r * c₀) ^ 2 * a ^ 2 := hpoint
    _ = 8 * tailActualEdgeInterpolation T hT (n + 1) b e x ^ 2 +
        32 * (tailInnerResistance T (n + 1) * tailActualNodeCoupling T hT n) ^ 2 * a ^ 2 := by
      dsimp only [tailActualEdgeInterpolation, v₀, v₁, r, c₀]
      ring

/-- The error coefficient belongs to the preceding node's actual mass. -/
theorem tailActualNodeCoupling_previous_mass_error {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (n : ℕ) :
    tailMass T (n + 1) *
        (tailInnerResistance T (n + 1) * tailActualNodeCoupling T hT n) ^ 2 ≤
      4 * (T.η / T.K) ^ 2 * tailMass T n := by
  have hr := (tailInnerResistance_pos hT (n + 1)).le
  calc
    _ ≤ tailMass T (n + 1) *
        (tailInnerResistance T (n + 1) * (2 / tailResistance T n)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hr (tailActualNodeCoupling_pos hT n).le)
          (mul_le_mul_of_nonneg_left (tailActualNodeCoupling_upper hT hη n) hr) 2)
        (tailMass_pos hT (n + 1)).le
    _ = 4 * (tailMass T (n + 1) *
        (tailInnerResistance T (n + 1) / tailResistance T n) ^ 2) := by ring
    _ ≤ 4 * ((T.η / T.K) ^ 2 * tailMass T n) :=
      mul_le_mul_of_nonneg_left (deepTail_previous_gap_mass_error hT n) (by norm_num)
    _ = _ := by ring

/-- A mass-cell integral and a strict fraction of the preceding node mass control the current node. -/
theorem tailActualEdgeInterpolation_mass_recovery {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    (n : ℕ) {a b e : ℝ}
    (hrec : -tailActualInteriorDiagonal T hT n * b =
      tailActualNodeCoupling T hT n * a + tailActualNodeCoupling T hT (n + 1) * e) :
    tailMass T (n + 1) * b ^ 2 ≤
      8 * (∫ x in T.node (n + 1)..T.massEnd (n + 1),
        T.p x * tailActualEdgeInterpolation T hT (n + 1) b e x ^ 2) +
        (1 / 2 : ℝ) * (tailMass T n * a ^ 2) := by
  let E : ℝ :=
    32 * (tailInnerResistance T (n + 1) * tailActualNodeCoupling T hT n) ^ 2 * a ^ 2
  have hab := (deepTail_node_lt_massEnd hT (n + 1)).le
  have hsub := deepTail_Icc_subset hT (deepTail_entrance_le_node hT (n + 1))
    (deepTail_massEnd_lt_endpoint hT (n + 1))
  have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
  have hpi := hp.intervalIntegrable_of_Icc (μ := volume) hab
  have hui : IntervalIntegrable
      (fun x => T.p x * tailActualEdgeInterpolation T hT (n + 1) b e x ^ 2)
      volume (T.node (n + 1)) (T.massEnd (n + 1)) :=
    (hp.mul
      ((tailActualEdgeInterpolation_differentiable hT (n + 1) b e).continuous.pow 2).continuousOn).intervalIntegrable_of_Icc
        (μ := volume) hab
  have hi := intervalIntegral.integral_mono_on hab (hpi.mul_const (b ^ 2))
    ((hui.const_mul 8).add (hpi.const_mul E)) (fun x hx => calc
      T.p x * b ^ 2 ≤ T.p x *
          (8 * tailActualEdgeInterpolation T hT (n + 1) b e x ^ 2 + E) :=
        mul_le_mul_of_nonneg_left
          (tailActualEdgeInterpolation_recovery_pointwise hT hη hK n hrec hx)
          (deepTail_pos hT x (hsub hx)).le
      _ = 8 * (T.p x * tailActualEdgeInterpolation T hT (n + 1) b e x ^ 2) + E * T.p x := by ring)
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (hui.const_mul 8) (hpi.const_mul E),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  change tailMass T (n + 1) * b ^ 2 ≤
    8 * (∫ x in T.node (n + 1)..T.massEnd (n + 1),
      T.p x * tailActualEdgeInterpolation T hT (n + 1) b e x ^ 2) + E * tailMass T (n + 1) at hi
  have hK₀ : 0 < T.K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hK
  have hratio : T.η / T.K ≤ 1 / 32 := by
    calc
      T.η / T.K ≤ T.η / 2 := div_le_div_of_nonneg_left hT.2.2.2.2.1.le
        (by norm_num) (by linarith only [hK])
      _ ≤ 1 / 32 := by linarith only [hη]
  have hfactor : 128 * (T.η / T.K) ^ 2 ≤ (1 / 2 : ℝ) := by
    have hs := pow_le_pow_left₀ (div_nonneg hT.2.2.2.2.1.le hK₀.le) hratio 2
    nlinarith only [hs]
  have herr : E * tailMass T (n + 1) ≤ (1 / 2 : ℝ) * (tailMass T n * a ^ 2) := by
    calc
      E * tailMass T (n + 1) = (32 * a ^ 2) *
          (tailMass T (n + 1) *
            (tailInnerResistance T (n + 1) * tailActualNodeCoupling T hT n) ^ 2) := by
        dsimp only [E]
        ring
      _ ≤ (32 * a ^ 2) * (4 * (T.η / T.K) ^ 2 * tailMass T n) :=
        mul_le_mul_of_nonneg_left (tailActualNodeCoupling_previous_mass_error hT hη n)
          (mul_nonneg (by norm_num) (sq_nonneg a))
      _ = (128 * (T.η / T.K) ^ 2) * (tailMass T n * a ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * (tailMass T n * a ^ 2) :=
        mul_le_mul_of_nonneg_right hfactor (mul_nonneg (tailMass_pos hT n).le (sq_nonneg a))
  exact hi.trans (add_le_add le_rfl herr)

theorem tailActualSolution_mass_recovery {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hu : ContinuousOn u (Ico (T.node 0) T.endpoint))
    (hv : ContinuousOn v (Ico (T.node 0) T.endpoint))
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ioo (T.node 0) T.endpoint)) (n : ℕ) :
    tailMass T (n + 1) * u (T.node (n + 1)) ^ 2 ≤
      8 * (∫ x in T.node (n + 1)..T.massEnd (n + 1), T.p x * u x ^ 2) +
        (1 / 2 : ℝ) * (tailMass T n * u (T.node n) ^ 2) := by
  have h := tailActualEdgeInterpolation_mass_recovery hT hη hK n
    (tailActualSolution_node_recurrence hT hu hv hsys n)
  have heq : (∫ x in T.node (n + 1)..T.massEnd (n + 1),
      T.p x * tailActualEdgeInterpolation T hT (n + 1)
        (u (T.node (n + 1))) (u (T.node (n + 2))) x ^ 2) =
      ∫ x in T.node (n + 1)..T.massEnd (n + 1), T.p x * u x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (T.node (n + 1)) (T.node ((n + 1) + 1)) :=
      uIcc_subset_Icc ⟨le_rfl, (tailActualEdge_order hT (n + 1)).le⟩
        ⟨(deepTail_node_lt_massEnd hT (n + 1)).le,
          (deepTail_massEnd_lt_succ_node hT (n + 1)).le⟩ hx
    have hval := (tailActualEdge_solution_eq_interpolation hT (n + 1)
      (hu.mono (tailActualEdge_subset_outward hT (n + 1)))
      (hv.mono (tailActualEdge_subset_outward hT (n + 1)))
      (hsys.mono (tailActualEdge_interior_subset_outward hT (n + 1))) hx').1
    dsimp only
    rw [← hval]
  rwa [heq] at h

/-- Every square-integrable actual state has a square-summable physical node sequence. -/
theorem tailActualSolution_node_sq_summable {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hu : ContinuousOn u (Ico (T.node 0) T.endpoint))
    (hv : ContinuousOn v (Ico (T.node 0) T.endpoint))
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ioo (T.node 0) T.endpoint))
    (huL2 : MemLp u 2 (deepTailMeasure T)) :
    Summable (fun n => tailMass T n * u (T.node n) ^ 2) := by
  apply tailNode_weighted_sq_summable_of_interval_recovery
    (μ := tailMass T) (a := fun n => u (T.node n)) (left := T.node) (right := T.massEnd)
    (p := T.p) (u := u) (M := 8) (ρ := 1 / 2)
    (fun n => (tailMass_pos hT n).le) (fun n => (deepTail_node_lt_massEnd hT n).le)
    (fun n x hx => (deepTail_pos hT x
      (deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
        (deepTail_massEnd_lt_endpoint hT n) hx)).le)
    (by norm_num) (by norm_num) (by norm_num)
    (tailActualSolution_mass_recovery hT hη hK hu hv hsys)
    (tailMassCell_sq_integral_summable hT huL2)

/-- The frozen natural equation implies weighted node square summability. -/
theorem tailNaturalEquation_node_sq_summable {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u : ℝ → ℝ} (hu : TailNaturalEquation T u) :
    Summable (fun n => tailMass T n * u (T.node n) ^ 2) := by
  have hco : Ico (T.node 0) T.endpoint ⊆ Ico T.entrance T.endpoint :=
    fun _ hx => ⟨(deepTail_entrance_le_node hT 0).trans hx.1, hx.2⟩
  have hoo : Ioo (T.node 0) T.endpoint ⊆ Ioo T.entrance T.endpoint :=
    fun _ hx => ⟨(deepTail_entrance_le_node hT 0).trans_lt hx.1, hx.2⟩
  exact tailActualSolution_node_sq_summable hT hη hK
    ((tailNaturalEquation_continuousOn hu).mono hco)
    ((tailNaturalEquation_flux_continuousOn hT hu).mono hco)
    ((tailNaturalEquation_system hT hu).mono hoo) hu.2.2.1

end ContinuousFlexibility.Radial
