module

public import ContinuousFlexibility.Analysis.CircleCompositionLineEnvelope
public import ContinuousFlexibility.Analysis.CircleJetAssembly

/-!
# Actual second-variation envelopes for joint chart composition

The moving outer field splits into its base value and its affine
increment. Together with the finitely many direction fields this gives
a single summable envelope for every angular and material-weight jet.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

local instance circleCompositionSecondEnvelopesPairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

private theorem linear_product_affine_add
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] E) (P : E → E)
    (hadd : ∀ u v, P (u + v) = P u + P v)
    (hsmul : ∀ (t : ℝ) (u : E), P (t • u) = t • P u)
    (x w rest : E) (t : ℝ) :
    P (L (x + t • w)) + rest = P (L x) + t • P (L w) + rest := by
  simp only [map_add, map_smul, RingHom.id_apply, hadd, hsmul]

private theorem linear_eval_affine_sum
    {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (L : E →ₗ[ℝ] ℝ) (eval : E → ℝ) (heval : ∀ u, L u = eval u)
    (x w : E) (v : Fin n → E) (t : ℝ) :
    L (x + t • w + ∑ i, v i) = eval x + t * eval w + ∑ i, eval (v i) := by
  calc
    L (x + t • w + ∑ i, v i) = L x + t * L w + ∑ i, L (v i) := by
      simp only [map_add, map_smul, map_sum, RingHom.id_apply, smul_eq_mul]
    _ = _ := by simp only [heval]

private theorem scalar_finite_line_envelope
    (n s : ℕ)
    (P : Option (Option (Fin n)) → ℝ → ℕ → ℕ → ℝ → ℝ)
    (F : ℝ → ℕ → ℕ → ℝ → ℝ)
    (hweight : ∀ m k : ℕ, 0 ≤ T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ))
    (hjet : ∀ t m b θ, F t m b θ =
      P none t m b θ + t * P (some none) t m b θ +
        ∑ i : Fin n, P (some (some i)) t m b θ)
    (hfamily : ∀ i, ∃ E : ℕ → ℝ≥0∞, ∃ C : ℝ,
      (∑' m, E m) < ⊤ ∧ 0 ≤ C ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ m b k, b + k ≤ s → ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) * |P i t m b θ| ≤
          C * Real.sqrt (E m).toReal) :
    ∃ energy : ℕ → ℝ≥0∞, ∃ B : ℝ,
      (∑' m, energy m) < ⊤ ∧ 0 ≤ B ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ m b k, b + k ≤ s → ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) * |F t m b θ| ≤
          B * Real.sqrt (energy m).toReal := by
  classical
  choose E C hE hC hb using hfamily
  let total : ℕ → ℝ≥0∞ := fun m =>
    ∑ i : Option (Option (Fin n)), ENNReal.ofReal (C i ^ 2) * E i m
  have htotal : (∑' m, total m) < ⊤ := finiteEnergyEnvelope_tsum_lt_top C E hE
  refine ⟨total, (n : ℝ) + 2, htotal, by positivity, ?_⟩
  intro t ht m b k horder θ
  let weight : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  have hw : 0 ≤ weight := hweight m k
  let R : ℝ := Real.sqrt (total m).toReal
  have hpoint (i : Option (Option (Fin n))) : weight * |P i t m b θ| ≤ R :=
    (hb i t ht m b k horder θ).trans
      (finiteEnergyEnvelope_term_le C (fun j => E j m) hC
        (fun j => (ENNReal.le_tsum (f := E j) m).trans_lt (hE j)) i)
  rw [hjet t m b θ]
  calc
    weight * |P none t m b θ + t * P (some none) t m b θ +
        ∑ i : Fin n, P (some (some i)) t m b θ| ≤
      weight * (|P none t m b θ + t * P (some none) t m b θ| +
        |∑ i : Fin n, P (some (some i)) t m b θ|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ ≤ weight * ((|P none t m b θ| + |t * P (some none) t m b θ|) +
        ∑ i : Fin n, |P (some (some i)) t m b θ|) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (abs_add_le _ _) (Finset.abs_sum_le_sum_abs _ _)) hw
    _ = weight * |P none t m b θ| + |t| * (weight * |P (some none) t m b θ|) +
        ∑ i : Fin n, weight * |P (some (some i)) t m b θ| := by
      rw [abs_mul, mul_add, Finset.mul_sum]
      ring
    _ ≤ R + 1 * R + ∑ _i : Fin n, R :=
      add_le_add
        (add_le_add (hpoint none) (mul_le_mul ht (hpoint (some none))
          (mul_nonneg hw (abs_nonneg _)) zero_le_one))
        (Finset.sum_le_sum (fun i _ => hpoint (some (some i))))
    _ = ((n : ℝ) + 2) * R := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private theorem circleJetSecondEnvelopes_of_line_envelopes
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    {U : Set E} (hU : IsOpen U)
    (hline : ∀ n x w v s, ∃ energy : ℕ → ℝ≥0∞, ∃ B : ℝ,
      (∑' m, energy m) < ⊤ ∧ 0 ≤ B ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ m b k, b + k ≤ s → ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
          |iteratedDeriv b (A n (x + t • w) v m) θ| ≤ B * Real.sqrt (energy m).toReal) :
    CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U) A := by
  intro n x hx v w
  have hcurve : Continuous (fun t : ℝ => x + t • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : {t : ℝ | x + t • w ∈ U} ∈ 𝓝 (0 : ℝ) :=
    hcurve.continuousAt.preimage_mem_nhds (by
      simpa only [zero_smul, add_zero] using hU.mem_nhds hx)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_, ?_⟩
  · intro t ht
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      ht.trans_le (min_le_left δ 1)
  · intro s
    obtain ⟨energy, B, hE, hB, hb⟩ :=
      hline (n + 2) x w (Fin.cons w (Fin.cons w v)) s
    exact ⟨energy, B, hE, hB, fun t ht =>
      hb t (ht.trans_le (min_le_right δ 1)).le⟩

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
  have heq (t : ℝ) :
      circleChartCompositionJetValue hS hT hD hγ travel n (x + t • w) v =
        P none t + t • P (some none) t + ∑ i : Fin n, P (some (some i)) t := by
    change circleFiniteProductWith hS hT hD hγ
        (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n
          (x.1 + t • w.1) (x.2 + t • w.2)) (fun i => (v i).1) Finset.univ +
      (∑ i : Fin n, circleFiniteProductWith hS hT hD hγ
        (circleOuterJetComposeContinuousLinear hS hT hD hγ travel (n - 1)
          (x.1 + t • w.1) (v i).2) (fun j => (v j).1) (Finset.univ.erase i)) = _
    exact linear_product_affine_add
      (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n (x.1 + t • w.1)).toLinearMap
      (fun u => circleFiniteProductWith hS hT hD hγ u (fun i => (v i).1) Finset.univ)
      (fun u z => circleFiniteProductWith_add hS hT hD hγ u z (fun i => (v i).1) Finset.univ)
      (fun c u => circleFiniteProductWith_smul hS hT hD hγ c u (fun i => (v i).1) Finset.univ)
      x.2 w.2 (∑ i : Fin n, P (some (some i)) t) t
  have hjet (t : ℝ) (m b : ℕ) (θ : ℝ) :
      iteratedDeriv b (circleChartCompositionJets hS travel n (x + t • w) v m) θ =
        iteratedDeriv b (S.decode (P none t) m) θ +
          t * iteratedDeriv b (S.decode (P (some none) t) m) θ +
          ∑ i : Fin n, iteratedDeriv b (S.decode (P (some (some i)) t) m) θ := by
    let ev : S.Space →ₗ[ℝ] ℝ := circleAngularJetEvaluationLinear hS b m θ
    have hd := congrFun (circleChartCompositionJetValue_decode
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel n (x + t • w) v) m
    have heval := circleAngularJetEvaluationLinear_apply hS b m θ
      (circleChartCompositionJetValue hS hT hD hγ travel n (x + t • w) v)
    exact (congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ) hd).symm.trans
      (heval.symm.trans ((congrArg ev (heq t)).trans
        (linear_eval_affine_sum ev (fun u => iteratedDeriv b (S.decode u m) θ)
          (fun u => circleAngularJetEvaluationLinear_apply hS b m θ u)
          (P none t) (P (some none) t) (fun i => P (some (some i)) t) t)))
  exact scalar_finite_line_envelope n s
    (fun i t m b θ => iteratedDeriv b (S.decode (P i t) m) θ)
    (fun t m b θ => iteratedDeriv b
      (circleChartCompositionJets hS travel n (x + t • w) v m) θ)
    (fun m k => mul_nonneg
      (pow_nonneg ((material_circle_sample_weights_pos hT hD).1 m).le k)
      (Real.rpow_nonneg ((material_circle_sample_weights_pos hT hD).2 m).le _))
    hjet
    (fun i => circleFiniteProductWith_comp_line_envelope
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel (order i)
      x.1 w.1 (outer i) (fun j => (v j).1) (mask i) s)

theorem circleChartCompositionJets_secondEnvelopes
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) {U : Set (S.Space × S.Space)} (hU : IsOpen U) :
    CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U)
      (circleChartCompositionJets hS travel) := by
  exact circleJetSecondEnvelopes_of_line_envelopes (circleChartCompositionJets hS travel) hU
    (fun n x w v s => circleChartCompositionJets_line_envelope
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel n x w v s)

end ContinuousFlexibility.Statements
