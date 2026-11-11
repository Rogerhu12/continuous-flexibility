import ContinuousFlexibility.Analysis.CoupledLogProfileCoefficientJets
import ContinuousFlexibility.Analysis.CoupledPositiveWeightBounds
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Scalar.WeightedReferenceCoefficients

/-!
# Positive-weight bounds for the actual logarithmic profile

The first N01 coefficient jet controls every logarithmic state direction,
with one fixed loss in the original state grading. Moving the sample weight
to its actual cell and dividing by the reference profile retains a positive
height power. No Banach control model or stronger decay hypothesis is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem coupled_weightedLogProfile_point_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (fun t => D.w t * coupled_stateLogProfile D S C v t) r| ≤
        K * T.H r ^ (3 / 64 : ℝ) * stateGrading S (s + (base + loss)) v := by
  obtain ⟨B, hB, hBb⟩ := coupled_logProfile_reference_jet_bound hT hS hN s
  obtain ⟨K, hK, hKb⟩ := coupled_materialSample_point_weight_bound hN.1.1 hT
    (γ := (3 / 4 : ℝ)) (by norm_num) B
  refine ⟨2 * B * K, by positivity, fun v r hr => ?_⟩
  obtain ⟨A, hA⟩ := hN.1.1
  obtain ⟨m, hrm⟩ := hA.2.1.exists_cell hr
  have hs : stateGrading S base v + stateGrading S (s + loss) v ≤
      2 * stateGrading S (s + (base + loss)) v := by
    have h₁ := solve_stateGrading_monotone S
      (by omega : base ≤ s + (base + loss)) v
    have h₂ := solve_stateGrading_monotone S
      (by omega : s + loss ≤ s + (base + loss)) v
    linarith only [h₁, h₂]
  have hsample := hT.2.1 (T.sample m) (materialSample_mem_radialCore hT hA.2.1 m)
  have hpos : 0 ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg hsample.2.1.le _))
      (Real.rpow_nonneg hsample.2.2.1.le _)
  calc
    _ ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
        (stateGrading S base v + stateGrading S (s + loss) v) := hBb m r hrm v
    _ ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
        (2 * stateGrading S (s + (base + loss)) v) :=
      mul_le_mul_of_nonneg_left hs hpos
    _ = (2 * B) * (T.H (T.sample m) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample m) ^ B) * stateGrading S (s + (base + loss)) v := by ring
    _ ≤ (2 * B) * (K * T.H r ^ ((3 / 4 : ℝ) / 16)) *
        stateGrading S (s + (base + loss)) v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hKb m r hrm) (by positivity)) (apply_nonneg _ _)
    _ = _ := by norm_num; ring

private theorem coupled_logProfile_radialJet_eq_iteratedDeriv (s : ℕ) (f : ℝ → ℝ) :
    radialJet s f = iteratedDeriv s f := by
  induction s with
  | zero => rfl
  | succ s ih => rw [radialJet, ih, iteratedDeriv_succ]

theorem coupled_logProfile_point_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (coupled_stateLogProfile D S C v) r| ≤
        K * T.M r * T.H r ^ (3 / 64 : ℝ) * stateGrading S (s + (base + loss)) v := by
  obtain ⟨A, hA⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hA.1.2.2.1.1
  have hwp : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hA.1.2.2.2.2.1
  have hbF (j : ℕ) (_ : j ≤ s) : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv j (fun t => (D.w t)⁻¹) r| ≤ K * T.M r := by
    obtain ⟨K, hK, hKb⟩ := referenceInverseJet_le_materialM ⟨A, hA⟩ hT j
    exact ⟨K, hK.le, fun r hr => by
      simpa only [coupled_logProfile_radialJet_eq_iteratedDeriv] using hKb r hr⟩
  have hbG (j : ℕ) (hj : j ≤ s) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ v r, r ∈ Ioo D.a D.b →
      |iteratedDeriv j (fun t => D.w t * coupled_stateLogProfile D S C v t) r| ≤
        K * T.H r ^ (3 / 64 : ℝ) * stateGrading S (s + (base + loss)) v := by
    obtain ⟨K, hK, hKb⟩ := coupled_weightedLogProfile_point_jet_bound hT hS hN j
    refine ⟨K, hK, fun v r hr => (hKb v r hr).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (solve_stateGrading_monotone S (Nat.add_le_add_right hj _) v)
      (mul_nonneg hK (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _))
  obtain ⟨K, hK, hKb⟩ := coupled_product_jet_majorant
    (f := fun r => (D.w r)⁻¹)
    (g := fun v r => D.w r * coupled_stateLogProfile D S C v r)
    (W := T.M) (V := fun r => T.H r ^ (3 / 64 : ℝ))
    (P := fun v => stateGrading S (s + (base + loss)) v)
    isOpen_Ioo (hw.contDiffOn.inv (fun r hr => (hwp r hr).ne'))
    (fun v => (hw.mul (coupled_contDiff_stateLogProfile hT hS hN v)).contDiffOn)
    (fun r hr => zero_le_one.trans (hT.2.1 r hr).2.2.2)
    (fun r hr => Real.rpow_nonneg (hT.2.1 r hr).2.1.le _)
    (apply_nonneg _) s hbF hbG
  refine ⟨K, hK, fun v r hr => ?_⟩
  have heq : (fun t => (D.w t)⁻¹ * (D.w t * coupled_stateLogProfile D S C v t)) =ᶠ[𝓝 r]
      coupled_stateLogProfile D S C v := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact inv_mul_cancel_left₀ (hwp t ht).ne' _
  rw [← heq.iteratedDeriv_eq s]
  exact hKb v r hr

/-- The same fixed loss works at every ordinary derivative order. -/
theorem coupled_logProfile_decay_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : AnnularState S, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (coupled_stateLogProfile D S C v) r| ≤
        K * stateGrading S (s + (base + loss)) v * T.H r ^ (3 / 128 : ℝ) * T.M r := by
  obtain ⟨K, hK, hKb⟩ := coupled_logProfile_point_jet_bound hT hS hN s
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, henv, _⟩ := hdata
  obtain ⟨A, hA, hAb, _, _⟩ := henv 0 (3 / 128) (by norm_num)
  refine ⟨K * A, mul_nonneg hK hA.le, fun v r hr => ?_⟩
  have hH := (hT.2.1 r hr).2.1
  have hM : 0 ≤ T.M r := zero_le_one.trans (hT.2.1 r hr).2.2.2
  have hb : T.H r ^ (3 / 128 : ℝ) ≤ A := by
    simpa only [Real.rpow_zero, mul_one] using hAb r hr
  have hs : T.H r ^ (3 / 64 : ℝ) =
      T.H r ^ (3 / 128 : ℝ) * T.H r ^ (3 / 128 : ℝ) := by
    rw [← Real.rpow_add hH]
    norm_num
  calc
    _ ≤ K * T.M r * T.H r ^ (3 / 64 : ℝ) *
        stateGrading S (s + (base + loss)) v := hKb v r hr
    _ = (K * stateGrading S (s + (base + loss)) v * T.H r ^ (3 / 128 : ℝ) * T.M r) *
        T.H r ^ (3 / 128 : ℝ) := by rw [hs]; ring
    _ ≤ (K * stateGrading S (s + (base + loss)) v * T.H r ^ (3 / 128 : ℝ) * T.M r) * A :=
      mul_le_mul_of_nonneg_left hb
        (mul_nonneg (mul_nonneg (mul_nonneg hK (apply_nonneg _ _))
          (Real.rpow_nonneg hH.le _)) hM)
    _ = _ := by ring

theorem coupled_stateLogProfile_zero_off_core
    (hN : N01Properties D T S C base loss ε) (v : AnnularState S)
    {r : ℝ} (hr : r ∉ Ioo D.a D.b) : coupled_stateLogProfile D S C v r = 0 := by
  have hborder : RadialTrueBorder D := hN.1.2.2.2.1
  have hchi : D.chi r = 0 := by
    by_contra hc
    exact hr (hborder.support_subset hc).1
  simp only [coupled_stateLogProfile, hchi, mul_zero,
    stateControlSum_zero_off_core hN.2.2.2.1 v hr, add_zero]

end ContinuousFlexibility.Statements
