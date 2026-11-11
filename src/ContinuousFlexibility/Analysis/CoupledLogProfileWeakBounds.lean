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

private theorem coupled_logProfile_sample_majorant
    {x B K W E H u v P : ℝ}
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hE : 0 ≤ E) (hP : 0 ≤ P)
    (hs : u + v ≤ 2 * P) (hx : x ≤ B * W * E * (u + v))
    (hweight : W * E ≤ K * H ^ ((3 / 4 : ℝ) / 16)) :
    x ≤ (2 * B * K) * H ^ (3 / 64 : ℝ) * P := by
  calc
    x ≤ B * W * E * (2 * P) :=
      hx.trans (mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg hB hW) hE))
    _ = (2 * B) * (W * E) * P := by ring
    _ ≤ (2 * B) * (K * H ^ ((3 / 4 : ℝ) / 16)) * P :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hweight (mul_nonneg (by norm_num) hB)) hP
    _ = _ := by
      rw [show ((3 / 4 : ℝ) / 16) = 3 / 64 by norm_num]
      ring

theorem coupled_weightedLogProfile_point_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (fun t => D.w t * coupled_stateLogProfile D S C v t) r| ≤
        K * T.H r ^ (3 / 64 : ℝ) * stateGrading S (s + (base + loss)) v := by
  let hreference := coupled_logProfile_reference_jet_bound hT hS hN s
  let B : ℝ := hreference.choose
  have hB : 0 < B := hreference.choose_spec.1
  let hBb := hreference.choose_spec.2
  let hweight := coupled_materialSample_point_weight_bound hN.1.1 hT
    (γ := (3 / 4 : ℝ)) (by norm_num) B
  let K : ℝ := hweight.choose
  have hK : 0 < K := hweight.choose_spec.1
  let hKb := hweight.choose_spec.2
  refine ⟨2 * B * K, mul_nonneg (mul_nonneg (by norm_num) hB.le) hK.le,
    fun v r hr => ?_⟩
  let hA := hN.1.1.choose_spec
  let hcell := hA.2.1.exists_cell hr
  let m : ℕ := hcell.choose
  have hrm : r ∈ D.cells m := hcell.choose_spec
  have hs : stateGrading S base v + stateGrading S (s + loss) v ≤
      2 * stateGrading S (s + (base + loss)) v := by
    have h₁ := solve_stateGrading_monotone S
      (by omega : base ≤ s + (base + loss)) v
    have h₂ := solve_stateGrading_monotone S
      (by omega : s + loss ≤ s + (base + loss)) v
    exact (add_le_add h₁ h₂).trans_eq (two_mul _).symm
  have hsample := hT.2.1 (T.sample m) (materialSample_mem_radialCore hT hA.2.1 m)
  exact coupled_logProfile_sample_majorant hB.le
    (Real.rpow_nonneg hsample.2.1.le _) (Real.rpow_nonneg hsample.2.2.1.le _)
    (apply_nonneg (stateGrading S (s + (base + loss))) v) hs (hBb m r hrm v) (hKb m r hrm)

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
  let hA := hN.1.1.choose_spec
  have hw : ContDiff ℝ ∞ D.w := hA.1.2.2.1.1
  have hwp : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hA.1.2.2.2.2.1
  have hbF (j : ℕ) (_ : j ≤ s) : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv j (fun t => (D.w t)⁻¹) r| ≤ K * T.M r := by
    let hinverse := referenceInverseJet_le_materialM hN.1.1 hT j
    let K : ℝ := hinverse.choose
    have hK : 0 < K := hinverse.choose_spec.1
    let hKb := hinverse.choose_spec.2
    refine ⟨K, hK.le, fun r hr => ?_⟩
    calc
      |iteratedDeriv j (fun t => (D.w t)⁻¹) r| =
          |radialJet j (fun t => (D.w t)⁻¹) r| :=
        congrArg (fun f : ℝ → ℝ => |f r|)
          (coupled_logProfile_radialJet_eq_iteratedDeriv j (fun t => (D.w t)⁻¹)).symm
      _ ≤ K * T.M r := hKb r hr
  have hbG (j : ℕ) (hj : j ≤ s) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ v r, r ∈ Ioo D.a D.b →
      |iteratedDeriv j (fun t => D.w t * coupled_stateLogProfile D S C v t) r| ≤
        K * T.H r ^ (3 / 64 : ℝ) * stateGrading S (s + (base + loss)) v := by
    let hweighted := coupled_weightedLogProfile_point_jet_bound hT hS hN j
    let K : ℝ := hweighted.choose
    have hK : 0 ≤ K := hweighted.choose_spec.1
    let hKb := hweighted.choose_spec.2
    refine ⟨K, hK, fun v r hr => (hKb v r hr).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (solve_stateGrading_monotone S (Nat.add_le_add_right hj _) v)
      (mul_nonneg hK (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _))
  let hproduct := coupled_product_jet_majorant
    (f := fun r => (D.w r)⁻¹)
    (g := fun v r => D.w r * coupled_stateLogProfile D S C v r)
    (W := T.M) (V := fun r => T.H r ^ (3 / 64 : ℝ))
    (P := fun v => stateGrading S (s + (base + loss)) v)
    isOpen_Ioo (hw.contDiffOn.inv (fun r hr => (hwp r hr).ne'))
    (fun v => (hw.mul (coupled_contDiff_stateLogProfile hT hS hN v)).contDiffOn)
    (fun r hr => zero_le_one.trans (hT.2.1 r hr).2.2.2)
    (fun r hr => Real.rpow_nonneg (hT.2.1 r hr).2.1.le _)
    (apply_nonneg (stateGrading S (s + (base + loss)))) s hbF hbG
  let K : ℝ := hproduct.choose
  have hK : 0 ≤ K := hproduct.choose_spec.1
  let hKb := hproduct.choose_spec.2
  refine ⟨K, hK, fun v r hr => ?_⟩
  have heq : (fun t => (D.w t)⁻¹ * (D.w t * coupled_stateLogProfile D S C v t)) =ᶠ[𝓝 r]
      coupled_stateLogProfile D S C v := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact inv_mul_cancel_left₀ (hwp t ht).ne' _
  calc
    |iteratedDeriv s (coupled_stateLogProfile D S C v) r| =
        |iteratedDeriv s (fun t => (D.w t)⁻¹ *
          (D.w t * coupled_stateLogProfile D S C v t)) r| :=
      congrArg abs (heq.iteratedDeriv_eq s).symm
    _ ≤ _ := hKb v r hr

private theorem coupled_logProfile_decay_majorant
    {x K A M P H : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hP : 0 ≤ P) (hH : 0 < H)
    (hx : x ≤ K * M * H ^ (3 / 64 : ℝ) * P)
    (hb : H ^ (3 / 128 : ℝ) ≤ A) :
    x ≤ (K * A) * P * H ^ (3 / 128 : ℝ) * M := by
  have hs : H ^ (3 / 64 : ℝ) = H ^ (3 / 128 : ℝ) * H ^ (3 / 128 : ℝ) := by
    rw [← Real.rpow_add hH]
    norm_num
  calc
    x ≤ K * M * H ^ (3 / 64 : ℝ) * P := hx
    _ = (K * P * H ^ (3 / 128 : ℝ) * M) * H ^ (3 / 128 : ℝ) := by rw [hs]; ring
    _ ≤ (K * P * H ^ (3 / 128 : ℝ) * M) * A :=
      mul_le_mul_of_nonneg_left hb
        (mul_nonneg (mul_nonneg (mul_nonneg hK hP) (Real.rpow_nonneg hH.le _)) hM)
    _ = _ := by ring

/-- The same fixed loss works at every ordinary derivative order. -/
theorem coupled_logProfile_decay_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : AnnularState S, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (coupled_stateLogProfile D S C v) r| ≤
        K * stateGrading S (s + (base + loss)) v * T.H r ^ (3 / 128 : ℝ) * T.M r := by
  let hpoint := coupled_logProfile_point_jet_bound hT hS hN s
  let K : ℝ := hpoint.choose
  have hK : 0 ≤ K := hpoint.choose_spec.1
  let hKb := hpoint.choose_spec.2
  let henvelope := hT.2.2.2.2.2.2.2.2.2.2.2.2.1 0 (3 / 128) (by norm_num)
  let A : ℝ := henvelope.choose
  have hA : 0 < A := henvelope.choose_spec.1
  let hAb := henvelope.choose_spec.2.1
  refine ⟨K * A, mul_nonneg hK hA.le, fun v r hr => ?_⟩
  have hH := (hT.2.1 r hr).2.1
  have hM : 0 ≤ T.M r := zero_le_one.trans (hT.2.1 r hr).2.2.2
  have hb : T.H r ^ (3 / 128 : ℝ) ≤ A := by
    calc
      T.H r ^ (3 / 128 : ℝ) = T.H r ^ (3 / 128 : ℝ) * T.M r ^ (0 : ℝ) := by
        rw [Real.rpow_zero, mul_one]
      _ ≤ A := hAb r hr
  exact coupled_logProfile_decay_majorant hK hM
    (apply_nonneg (stateGrading S (s + (base + loss))) v) hH (hKb v r hr) hb

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
