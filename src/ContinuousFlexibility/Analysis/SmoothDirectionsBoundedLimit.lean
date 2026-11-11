import ContinuousFlexibility.Analysis.SmoothDirectionsUniformBounds

/-!
# Smooth limits under uniform seminorm bounds

At each fixed jet order a single continuous seminorm bounds the entire
family. These estimates imply both joint equicontinuity and the local
second-line bounds required by the endpoint assembly theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {ι : Type*} {U : Set E} {f : ι → E → ℝ}

def UniformScalarJetSeminormBounds (J : ∀ i, SmoothDirections U (f i)) : Prop :=
  ∀ n, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
    ∀ i x, x ∈ U → ∀ v : Fin n → E,
      |(J i).D n x v| ≤ B * (1 + p x) * ∏ j, p (v j)

theorem equicontinuous_jets_of_uniform_seminorm_bounds
    (J : ∀ i, SmoothDirections U (f i)) (hU : IsOpen U) (hc : Convex ℝ U)
    (hbound : UniformScalarJetSeminormBounds J) (n : ℕ) :
    EquicontinuousOn (fun i (z : E × (Fin n → E)) => (J i).D n z.1 z.2) (U ×ˢ univ) := by
  obtain ⟨p, B, hp, hB, hb⟩ := hbound (n + 1)
  obtain ⟨q, A, hq, hA, ha⟩ := hbound n
  rintro ⟨x, v⟩ hx
  apply EquicontinuousAt.equicontinuousWithinAt
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  let err : E × (Fin n → E) → ℝ := fun z =>
    B * (1 + p x + p (z.1 - x)) * (p (z.1 - x) * ∏ j, p (z.2 j)) +
      A * (1 + q x) * seminormMultilinearDifference q v z.2
  have hpbase : Continuous (fun z : E × (Fin n → E) => p (z.1 - x)) :=
    hp.comp (continuous_fst.sub continuous_const)
  have hpdirs : Continuous (fun z : E × (Fin n → E) => ∏ j, p (z.2 j)) :=
    continuous_finsetProd _ (fun j _ => hp.comp ((continuous_apply j).comp continuous_snd))
  have herr : Continuous err :=
    ((continuous_const.mul (continuous_const.add hpbase)).mul (hpbase.mul hpdirs)).add
      (continuous_const.mul ((continuous_seminormMultilinearDifference q hq v).comp continuous_snd))
  have herr0 : err (x, v) = 0 := by
    simp only [err, sub_self, map_zero, mul_zero, zero_mul,
      seminormMultilinearDifference_self, add_zero]
  have hsmall : ∀ᶠ z in 𝓝 (x, v), err z < ε :=
    (herr.tendsto (x, v)).eventually (Iio_mem_nhds (by simpa only [herr0] using hε))
  have hmem : ∀ᶠ z : E × (Fin n → E) in 𝓝 (x, v), z.1 ∈ U :=
    continuous_fst.continuousAt.eventually (hU.mem_nhds hx.1)
  filter_upwards [hsmall, hmem] with z hz hzu
  intro i
  have hbase := (J i).base_variation_le hc p hB (hb i) hx.1 hzu z.2
  have hdirs := abs_multilinear_sub_le_of_seminorm_bound ((J i).D n x) q
    (A * (1 + q x)) (ha i x hx.1) v z.2
  have htotal : |(J i).D n z.1 z.2 - (J i).D n x v| ≤ err z :=
    (abs_sub_le ((J i).D n z.1 z.2) ((J i).D n x z.2) ((J i).D n x v)).trans
      (add_le_add hbase hdirs)
  rw [Real.dist_eq, abs_sub_comm]
  exact htotal.trans_lt hz

theorem local_second_line_bounds_of_uniform_seminorm_bounds
    (J : ∀ i, SmoothDirections U (f i)) (hU : IsOpen U)
    (hbound : UniformScalarJetSeminormBounds J)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (w : E) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧
      (∀ t : ℝ, |t| < δ → x + t • w ∈ U) ∧
      ∀ i t, |t| < δ →
        |(J i).D (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v))| ≤ B := by
  obtain ⟨p, B, hp, hB, hb⟩ := hbound (n + 2)
  have hline : {t : ℝ | x + t • w ∈ U} ∈ 𝓝 (0 : ℝ) := by
    have hc : Continuous (fun t : ℝ => x + t • w) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact hc.continuousAt.eventually (hU.mem_nhds
      (by simpa only [zero_smul, add_zero] using hx))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hline
  let K : ℝ := B * (1 + p x + p w) * (p w * (p w * ∏ j, p (v j)))
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hB (add_nonneg (add_nonneg zero_le_one (apply_nonneg p x))
      (apply_nonneg p w)))
      (mul_nonneg (apply_nonneg p w) (mul_nonneg (apply_nonneg p w)
        (Finset.prod_nonneg (fun j _ => apply_nonneg p (v j)))))
  refine ⟨min δ 1, K, lt_min hδ zero_lt_one, hK, ?_, ?_⟩
  · intro t ht
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      ht.trans_le (min_le_left δ 1)
  · intro i t ht
    have htδ : |t| < δ := ht.trans_le (min_le_left δ 1)
    have ht1 : |t| ≤ 1 := (ht.trans_le (min_le_right δ 1)).le
    have htu : x + t • w ∈ U := hball
      (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using htδ)
    have hpaffine : p (x + t • w) ≤ p x + p w := by
      calc
        p (x + t • w) ≤ p x + p (t • w) := map_add_le_add _ _ _
        _ = p x + |t| * p w := by rw [map_smul_eq_mul, Real.norm_eq_abs]
        _ ≤ p x + p w := add_le_add_left (mul_le_of_le_one_left (apply_nonneg p w) ht1) _
    have hb' := hb i _ htu (Fin.cons w (Fin.cons w v))
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at hb'
    exact hb'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hB)
      (mul_nonneg (apply_nonneg _ _) (mul_nonneg (apply_nonneg _ _)
        (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)))))

/-- The endpoint tower is obtained without a separate derivative-limit
or equicontinuity hypothesis: both follow from the stated seminorm bounds. -/
theorem exists_smoothDirections_of_uniform_seminorm_bounds
    {l : Filter ι} [NeBot l] {g : E → ℝ}
    (J : ∀ i, SmoothDirections U (f i)) (hU : IsOpen U) (hc : Convex ℝ U)
    (hzero : ∀ x ∈ U, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hbound : UniformScalarJetSeminormBounds J) :
    ∃ K : SmoothDirections U g, ∀ n x, x ∈ U → ∀ v : Fin n → E,
      Tendsto (fun i => (J i).D n x v) l (𝓝 (K.D n x v)) :=
  exists_smoothDirections_of_equicontinuous_limits hU J hzero
    (local_second_line_bounds_of_uniform_seminorm_bounds J hU hbound)
    (equicontinuous_jets_of_uniform_seminorm_bounds J hU hc hbound)

end ContinuousFlexibility.Analysis
