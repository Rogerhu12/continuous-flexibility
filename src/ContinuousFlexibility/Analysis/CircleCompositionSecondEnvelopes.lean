import ContinuousFlexibility.Analysis.CircleCompositionLineEnvelope
import ContinuousFlexibility.Analysis.CircleJetAssembly

/-!
# Actual second-variation envelopes for joint chart composition

The moving outer field splits into its base value and its affine
increment. Together with the finitely many direction fields this gives
a single summable envelope for every angular and material-weight jet.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem linear_product_affine
    {E F G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    (L : E →ₗ[ℝ] F) (P : F → G)
    (hadd : ∀ a b, P (a + b) = P a + P b)
    (hsmul : ∀ (t : ℝ) a, P (t • a) = t • P a)
    (x w : E) (t : ℝ) :
    P (L (x + t • w)) = P (L x) + t • P (L w) := by
  rw [map_add, map_smul, hadd, hsmul]

private theorem weighted_affine_fin_sum_le
    {n : ℕ} {weight R t a b : ℝ} {c : Fin n → ℝ}
    (hw : 0 ≤ weight) (ht : |t| ≤ 1)
    (ha : weight * |a| ≤ R) (hb : weight * |b| ≤ R)
    (hc : ∀ i, weight * |c i| ≤ R) :
    weight * |a + t * b + ∑ i : Fin n, c i| ≤ ((n : ℝ) + 2) * R := by
  calc
    _ ≤ weight * (|a + t * b| + |∑ i : Fin n, c i|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ ≤ weight * ((|a| + |t * b|) + ∑ i : Fin n, |c i|) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (abs_add_le _ _) (Finset.abs_sum_le_sum_abs _ _)) hw
    _ = weight * |a| + |t| * (weight * |b|) + ∑ i : Fin n, weight * |c i| := by
      rw [abs_mul, Finset.mul_sum]
      ring
    _ ≤ R + 1 * R + ∑ _i : Fin n, R :=
      add_le_add (add_le_add ha
        (mul_le_mul ht hb (mul_nonneg hw (abs_nonneg b)) zero_le_one))
        (Finset.sum_le_sum (fun i _ => hc i))
    _ = ((n : ℝ) + 2) * R := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circleChartCompositionJets_line_envelope
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (n : ℕ) (x w : S.Space × S.Space)
    (v : Fin n → S.Space × S.Space) (s : ℕ) :
    ∃ energy : ℕ → ℝ≥0∞, ∃ B : ℝ,
      (∑' m, energy m) < ⊤ ∧ 0 ≤ B ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ m b k, b + k ≤ s → ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
          |iteratedDeriv b (circleChartCompositionJets hS travel n (x + t • w) v m) θ| ≤
          B * Real.sqrt (energy m).toReal := by
  classical
  let ι := Option (Option (Fin n))
  let order : ι → ℕ
    | none => n
    | some none => n
    | some (some _) => n - 1
  let outer : ι → S.Space
    | none => x.2
    | some none => w.2
    | some (some i) => (v i).2
  let mask : ι → Finset (Fin n)
    | none => Finset.univ
    | some none => Finset.univ
    | some (some i) => Finset.univ.erase i
  let P : ι → ℝ → S.Space := fun i t =>
    circleFiniteProductWith hS hT hD hγ
      (circleOuterJetComposeContinuousLinear hS hT hD hγ travel (order i)
        (x.1 + t • w.1) (outer i)) (fun j => (v j).1) (mask i)
  have hfamily (i : ι) :
      ∃ E : ℕ → ℝ≥0∞, ∃ C : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ C ∧
        ∀ t : ℝ, |t| ≤ 1 → ∀ m b k, b + k ≤ s → ∀ θ,
          (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
            |iteratedDeriv b (S.decode (P i t) m) θ| ≤ C * Real.sqrt (E m).toReal :=
    circleFiniteProductWith_comp_line_envelope hS hT hD hγ travel (order i)
      x.1 w.1 (outer i) (fun j => (v j).1) (mask i) s
  choose E C hE hC hb using hfamily
  let total : ℕ → ℝ≥0∞ := fun m => ∑ i : ι, ENNReal.ofReal (C i ^ 2) * E i m
  have htotal : (∑' m, total m) < ⊤ := finiteEnergyEnvelope_tsum_lt_top C E hE
  have heq (t : ℝ) :
      circleChartCompositionJetValue hS hT hD hγ travel n (x + t • w) v =
        P none t + t • P (some none) t + ∑ i : Fin n, P (some (some i)) t := by
    change circleFiniteProductWith hS hT hD hγ
        (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n
          (x.1 + t • w.1) (x.2 + t • w.2)) (fun i => (v i).1) Finset.univ +
      (∑ i : Fin n, circleFiniteProductWith hS hT hD hγ
        (circleOuterJetComposeContinuousLinear hS hT hD hγ travel (n - 1)
          (x.1 + t • w.1) (v i).2) (fun j => (v j).1) (Finset.univ.erase i)) = _
    let L : S.Space →ₗ[ℝ] S.Space :=
      (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n
        (x.1 + t • w.1)).toLinearMap
    have hmain :
        circleFiniteProductWith hS hT hD hγ (L (x.2 + t • w.2))
          (fun i => (v i).1) Finset.univ =
        circleFiniteProductWith hS hT hD hγ (L x.2) (fun i => (v i).1) Finset.univ +
          t • circleFiniteProductWith hS hT hD hγ (L w.2) (fun i => (v i).1) Finset.univ :=
      linear_product_affine L
        (fun u => circleFiniteProductWith hS hT hD hγ u (fun i => (v i).1) Finset.univ)
        (fun a b => circleFiniteProductWith_add hS hT hD hγ a b
          (fun i => (v i).1) Finset.univ)
        (fun a b => circleFiniteProductWith_smul hS hT hD hγ a b
          (fun i => (v i).1) Finset.univ) x.2 w.2 t
    exact congrArg
      (fun u : S.Space => u + ∑ i : Fin n, P (some (some i)) t) hmain
  refine ⟨total, (n : ℝ) + 2, htotal, by positivity, ?_⟩
  intro t ht m b k horder θ
  let ev := circleAngularJetEvaluationLinear hS b m θ
  let weight : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  have hw : 0 ≤ weight := mul_nonneg
    (pow_nonneg ((material_circle_sample_weights_pos hT hD).1 m).le _)
    (Real.rpow_nonneg ((material_circle_sample_weights_pos hT hD).2 m).le _)
  let R : ℝ := Real.sqrt (total m).toReal
  have hpoint (i : ι) : weight * |ev (P i t)| ≤ R := by
    rw [show ev (P i t) = iteratedDeriv b (S.decode (P i t) m) θ from
      circleAngularJetEvaluationLinear_apply hS b m θ (P i t)]
    exact (hb i t ht m b k horder θ).trans
      (finiteEnergyEnvelope_term_le C (fun j => E j m) hC
        (fun j => (ENNReal.le_tsum (f := E j) m).trans_lt (hE j)) i)
  have hjet : iteratedDeriv b
      (circleChartCompositionJets hS travel n (x + t • w) v m) θ =
        ev (P none t) + t * ev (P (some none) t) +
          ∑ i : Fin n, ev (P (some (some i)) t) := by
    rw [← circleChartCompositionJetValue_decode hS hT hD hγ travel n (x + t • w) v]
    rw [← circleAngularJetEvaluationLinear_apply, heq]
    simp only [map_add, map_smul, map_sum, RingHom.id_apply, smul_eq_mul, ev]
  rw [hjet]
  exact weighted_affine_fin_sum_le hw ht (hpoint none) (hpoint (some none))
    (fun i => hpoint (some (some i)))

private theorem circleJetSecondEnvelopes_of_unit_line
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} (hU : IsOpen U)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hlineEnvelope : ∀ (n : ℕ) (x w : E) (v : Fin n → E) (s : ℕ),
      ∃ energy : ℕ → ℝ≥0∞, ∃ B : ℝ,
        (∑' m, energy m) < ⊤ ∧ 0 ≤ B ∧
        ∀ t : ℝ, |t| ≤ 1 → ∀ m b k, b + k ≤ s → ∀ θ,
          (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
            |iteratedDeriv b (A n (x + t • w) v m) θ| ≤
            B * Real.sqrt (energy m).toReal) :
    CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U) A := by
  intro n x hx v w
  have hline : Continuous (fun t : ℝ => x + t • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : {t : ℝ | x + t • w ∈ U} ∈ 𝓝 (0 : ℝ) :=
    hline.continuousAt.preimage_mem_nhds (by
      simpa only [zero_smul, add_zero] using hU.mem_nhds hx)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_, ?_⟩
  · intro t ht
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      ht.trans_le (min_le_left δ 1)
  · intro s
    let data := hlineEnvelope (n + 2) x w (Fin.cons w (Fin.cons w v)) s
    let energy : ℕ → ℝ≥0∞ := data.choose
    let bounds := data.choose_spec
    exact ⟨energy, bounds.choose, bounds.choose_spec.1, bounds.choose_spec.2.1,
      fun t ht => bounds.choose_spec.2.2 t (ht.trans_le (min_le_right δ 1)).le⟩

theorem circleChartCompositionJets_secondEnvelopes
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) {U : Set (S.Space × S.Space)} (hU : IsOpen U) :
    CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U)
      (circleChartCompositionJets hS travel) :=
  circleJetSecondEnvelopes_of_unit_line hU (circleChartCompositionJets hS travel)
    (circleChartCompositionJets_line_envelope hS hT hD hγ travel)

end ContinuousFlexibility.Statements
