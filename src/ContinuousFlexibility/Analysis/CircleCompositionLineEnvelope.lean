import ContinuousFlexibility.Analysis.CircleCompositionJetModels
import ContinuousFlexibility.Analysis.CircleFiniteEnergyEnvelopes

/-!
# Summable envelopes along actual affine chart lines

Only finitely many fixed outer circle fields carry the energy. The chart
moves along a genuine affine line, whose angular jets are uniformly
bounded on the unit parameter interval. The remaining factors are
uniformly smooth multipliers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circleModel_uniform_jets_affineLine
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (e w : S.Space) (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ m i θ, i ≤ s →
      |iteratedDeriv i (S.decode (e + t • w) m) θ| ≤ B := by
  obtain ⟨Be, he, hbe⟩ := circleModel_uniform_jets_of_material hS hT hD hγ e s
  obtain ⟨Bw, hw, hbw⟩ := circleModel_uniform_jets_of_material hS hT hD hγ w s
  refine ⟨Be + Bw, add_nonneg he hw, ?_⟩
  intro t ht m i θ hi
  rw [circleAngularJetEvaluation_line]
  calc
    _ ≤ |iteratedDeriv i (S.decode e m) θ| +
        |t| * |iteratedDeriv i (S.decode w m) θ| := by
      simpa only [abs_mul] using abs_add_le
        (iteratedDeriv i (S.decode e m) θ) (t * iteratedDeriv i (S.decode w m) θ)
    _ ≤ Be + 1 * Bw :=
      add_le_add (hbe m i θ hi) (mul_le_mul ht (hbw m i θ hi)
        (abs_nonneg _) zero_le_one)
    _ = Be + Bw := by rw [one_mul]

theorem circleShiftedChart_uniform_jets_affineLine
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e w : S.Space) (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ m i θ,
      1 ≤ i → i ≤ s →
      |iteratedDeriv i (circleAffineLift travel (S.decode (e + t • w)) 1 m) θ| ≤ B ^ i := by
  obtain ⟨B, hB, hb⟩ := circleModel_uniform_jets_affineLine hS hT hD hγ e w s
  refine ⟨1 + B, by positivity, ?_⟩
  intro t ht
  exact circleAffineLift_uniform_jets
    (fun m => ((hS.2.2.2.1 (e + t • w)).1 m).1)
    travel hB (hb t ht) (by norm_num : (1 : ℝ) ∈ Icc 0 1)

theorem circleFiniteProductWith_add
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (u z : S.Space) (v : ι → S.Space) (I : Finset ι) :
    circleFiniteProductWith hS hT hD hγ (u + z) v I =
      circleFiniteProductWith hS hT hD hγ u v I +
        circleFiniteProductWith hS hT hD hγ z v I := by
  apply hS.2.2.2.2.2.1
  simp only [map_add, circleFiniteProductWith_decode]
  funext m θ
  simp only [Pi.add_apply, add_mul]

theorem circleFiniteProductWith_smul
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (c : ℝ) (u : S.Space) (v : ι → S.Space) (I : Finset ι) :
    circleFiniteProductWith hS hT hD hγ (c • u) v I =
      c • circleFiniteProductWith hS hT hD hγ u v I := by
  apply hS.2.2.2.2.2.1
  simp only [map_smul, circleFiniteProductWith_decode]
  funext m θ
  simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_assoc]

/-- The finite product is used only as a multiplier. In the empty case
it is the scalar constant one; in every other case it is an actual
decoded circle vector. -/
theorem circleFiniteProduct_multiplier_uniform_jets
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (v : ι → S.Space) (I : Finset ι) (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m i θ, i ≤ s →
      |iteratedDeriv i (fun y => ∏ j ∈ I, S.decode (v j) m y) θ| ≤ B := by
  classical
  by_cases hI : I = ∅
  · subst I
    refine ⟨1, zero_le_one, ?_⟩
    intro m i θ hi
    simp only [Finset.prod_empty, iteratedDeriv_const]
    split_ifs <;> norm_num
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hI
    let u := circleFiniteProductWith hS hT hD hγ (v j) v (I.erase j)
    have heq : S.decode u = fun m θ => ∏ k ∈ I, S.decode (v k) m θ := by
      rw [show S.decode u =
        (fun m θ => S.decode (v j) m θ * ∏ k ∈ I.erase j, S.decode (v k) m θ) from
          circleFiniteProductWith_decode hS hT hD hγ (v j) v (I.erase j)]
      funext m θ
      exact Finset.mul_prod_erase I (fun k => S.decode (v k) m θ) hj
    obtain ⟨B, hB, hb⟩ := circleModel_uniform_jets_of_material hS hT hD hγ u s
    refine ⟨B, hB, ?_⟩
    simpa only [heq] using hb

/-- One product term of a parameter jet has a fixed summable envelope
as the chart moves on an affine parameter interval. -/
theorem circleFiniteProductWith_comp_line_envelope
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (n : ℕ) (e w u : S.Space)
    (v : ι → S.Space) (I : Finset ι) (s : ℕ) :
    ∃ energy : ℕ → ℝ≥0∞, ∃ B : ℝ,
      (∑' m, energy m) < ⊤ ∧ 0 ≤ B ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ m b k, b + k ≤ s → ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
          |iteratedDeriv b
            (S.decode (circleFiniteProductWith hS hT hD hγ
              (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n (e + t • w) u)
              v I) m) θ| ≤ B * Real.sqrt (energy m).toReal := by
  classical
  let U := circleAngularDerivativeIterate hS n u
  let energy : ℕ → ℝ≥0∞ := circleComponentEnergy T γ (s + 2) (S.decode U)
  obtain ⟨L, hL, hLjets⟩ := circleFiniteProduct_multiplier_uniform_jets hS hT hD hγ v I s
  obtain ⟨V, hV, hVjets⟩ :=
    circleShiftedChart_uniform_jets_affineLine hS hT hD hγ travel e w (s + 1)
  let Q : ℝ := (Fintype.card (CircleJetIndex (s + 1)) : ℝ) *
    (Real.pi * circleCompositionJetConstant (s + 1) V ^ 2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let B : ℝ := circleProductJetConstant s L * Real.sqrt Q
  have hB : 0 ≤ B := mul_nonneg (circleProductJetConstant_nonneg s hL) (Real.sqrt_nonneg _)
  refine ⟨energy, B, (hS.2.2.2.1 U).2.2 (s + 2), hB, ?_⟩
  intro t ht m b k horder θ
  let φ := circleAffineLift travel (S.decode (e + t • w)) 1
  let z := circleOuterJetComposeContinuousLinear hS hT hD hγ travel n (e + t • w) u
  have hz : S.decode z = circleComposeField (S.decode U) φ := by
    rw [show S.decode z =
      (fun m θ => iteratedDeriv n (S.decode u m)
        (circleCompositionPhase travel (e + t • w, u) m θ)) from
          circleOuterJetComposeContinuousLinear_decode hS hT hD hγ travel n (e + t • w) u]
    rw [show S.decode U = (fun m => iteratedDeriv n (S.decode u m)) from
      circleAngularDerivativeIterate_decode hS n u]
    simp only [circleComposeField, φ, circleAffineLift, circleCompositionPhase,
      Function.comp_def, one_mul]
  have hφ (j : ℕ) : ContDiff ℝ ∞ (φ j) :=
    circleAffineLift_contDiff (fun l => ((hS.2.2.2.1 (e + t • w)).1 l).1) travel 1 j
  have hcomponent := circleComponentEnergy_comp_le (hS.2.2.2.1 U)
    (material_circle_sample_weights_pos hT hD).1
    (material_circle_sample_weights_pos hT hD).2 hφ (s + 1) hV (hVjets t ht) m
  have hfinite : ENNReal.ofReal Q * energy m < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (circleComponentEnergy_lt_top (hS.2.2.2.1 U) (s + 2) m)
  have hsqrt :
      Real.sqrt (circleComponentEnergy T γ (s + 1) (S.decode z) m).toReal ≤
        Real.sqrt Q * Real.sqrt (energy m).toReal := by
    rw [hz]
    have h := Real.sqrt_le_sqrt (ENNReal.toReal_mono hfinite.ne hcomponent)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hQ,
      Real.sqrt_mul hQ] using h
  have hmult (j : ℕ) :
      ContDiff ℝ ∞ (fun y => ∏ i ∈ I, S.decode (v i) j y) :=
    contDiff_prod (fun i hi => ((hS.2.2.2.1 (v i)).1 j).1)
  have hb := circleWeighted_product_iteratedDeriv_abs_le (hS.2.2.2.1 z) hmult
    ((material_circle_sample_weights_pos hT hD).1 m).le
    ((material_circle_sample_weights_pos hT hD).2 m).le horder hL
    (fun i y hi => hLjets m i y hi) θ
  have heq :
      S.decode (circleFiniteProductWith hS hT hD hγ z v I) m =
      (fun y => (∏ i ∈ I, S.decode (v i) m y) * S.decode z m y) := by
    rw [circleFiniteProductWith_decode]
    funext y
    exact mul_comm _ _
  rw [heq]
  exact hb.trans ((mul_le_mul_of_nonneg_left hsqrt
    (circleProductJetConstant_nonneg s hL)).trans_eq (by dsimp [B]; ring))

end ContinuousFlexibility.Statements
