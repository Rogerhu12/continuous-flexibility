module

public import ContinuousFlexibility.Analysis.N08ControlLabelDecay
public import ContinuousFlexibility.Analysis.N08SamplePointWeights
public import ContinuousFlexibility.Scalar.WeightedReferenceCoefficients

/-!
# Actual spatial bounds for normalized control profiles

The genuine N01 coefficient derivative first bounds `w` times a control
profile. The actual reciprocal reference jets recover that same profile by
Leibniz's formula, at the evaluation point and independently of its label.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n08_product_jet_majorant {I : Type*} {U : Set ℝ}
    {f : ℝ → ℝ} {g : I → ℝ → ℝ} {W V : ℝ → ℝ} {P : I → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) U)
    (hW : ∀ r ∈ U, 0 ≤ W r) (hV : ∀ r ∈ U, 0 ≤ V r) (hP : ∀ i, 0 ≤ P i)
    (s : ℕ)
    (hbF : ∀ j ≤ s, ∃ A : ℝ, 0 ≤ A ∧ ∀ r ∈ U, |iteratedDeriv j f r| ≤ A * W r)
    (hbG : ∀ j ≤ s, ∃ A : ℝ, 0 ≤ A ∧ ∀ i r, r ∈ U →
      |iteratedDeriv j (g i) r| ≤ A * V r * P i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ U →
      |iteratedDeriv s (fun t => f t * g i t) r| ≤ K * W r * V r * P i := by
  have hA (j : Fin (s + 1)) := hbF j.val (by omega)
  have hB (j : Fin (s + 1)) := hbG (s - j.val) (Nat.sub_le _ _)
  choose A hA hAb using hA
  choose B hB hBb using hB
  let K (j : Fin (s + 1)) : ℝ := (s.choose j.val : ℝ) * A j * B j
  have hK (j : Fin (s + 1)) : 0 ≤ K j :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA j)) (hB j)
  refine ⟨∑ j, K j, Finset.sum_nonneg (fun j _ => hK j), ?_⟩
  intro i r hr
  let term (j : ℕ) : ℝ :=
    (s.choose j : ℝ) * iteratedDeriv j f r * iteratedDeriv (s - j) (g i) r
  have hformula : iteratedDeriv s (fun t => f t * g i t) r =
      ∑ j : Fin (s + 1), term j.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_mul ((hf.contDiffAt (hU.mem_nhds hr)).of_le (by simp))
      (((hg i).contDiffAt (hU.mem_nhds hr)).of_le (by simp))
  rw [hformula, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  dsimp only [term]
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (s.choose j.val))]
  calc
    _ ≤ (s.choose j.val : ℝ) * (A j * W r) * (B j * V r * P i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hAb j r hr) (Nat.cast_nonneg _))
        (hBb j i r hr) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA j) (hW r hr)))
    _ = K j * W r * V r * P i := by dsimp only [K]; ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_controlProfile_point_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (fun t => D.w t * n08WeightedControlProfile T C i t) r| ≤
        K * T.H r ^ (3 / 64 : ℝ) * T.M (T.sample i) ^ (base + (s + loss)) := by
  obtain ⟨B, K, _, hK, hb⟩ := n08_controlProfile_reference_jet_bound hT hS hN s
  obtain ⟨L, hL, hLb⟩ := n08_materialSample_point_weight_bound hN.1.1 hT
    (γ := (3 / 4 : ℝ)) (by norm_num) B
  refine ⟨K * L, mul_nonneg hK hL.le, fun i r hr => ?_⟩
  obtain ⟨A, hA⟩ := hN.1.1
  obtain ⟨m, hrm⟩ := hA.2.1.exists_cell hr
  have hi := n08_material_sample_bounds hN.1.1 hT i
  calc
    _ ≤ K * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
        T.M (T.sample i) ^ (base + (s + loss)) := hb i m r hrm
    _ = K * (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B) *
        T.M (T.sample i) ^ (base + (s + loss)) := by ring
    _ ≤ K * (L * T.H r ^ ((3 / 4 : ℝ) / 16)) *
        T.M (T.sample i) ^ (base + (s + loss)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hLb m r hrm) hK)
        (pow_nonneg (zero_le_one.trans hi.2) _)
    _ = _ := by
      rw [show ((3 / 4 : ℝ) / 16) = 3 / 64 by norm_num]
      ring

private theorem n08_radialJet_eq_iteratedDeriv (s : ℕ) (f : ℝ → ℝ) :
    radialJet s f = iteratedDeriv s f := by
  induction s with
  | zero => rfl
  | succ s ih => rw [radialJet, ih, iteratedDeriv_succ]

/-- Dividing by the reference profile costs one material envelope, with
the same label power for every term of the finite Leibniz expansion. -/
theorem n08_weightedControlProfile_point_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (n08WeightedControlProfile T C i) r| ≤
        K * T.M r * T.H r ^ (3 / 64 : ℝ) *
          T.M (T.sample i) ^ (base + (s + loss)) := by
  obtain ⟨A, hA⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hA.1.2.2.1.1
  have hwp : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hA.1.2.2.2.2.1
  have hcontrol := hN.2.2.2.1.2.2.2.2.2.1
  have hbF (j : ℕ) (_ : j ≤ s) : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv j (fun t => (D.w t)⁻¹) r| ≤ K * T.M r := by
    obtain ⟨K, hK, hKb⟩ := referenceInverseJet_le_materialM ⟨A, hA⟩ hT j
    exact ⟨K, hK.le, fun r hr => by
      simpa only [n08_radialJet_eq_iteratedDeriv] using hKb r hr⟩
  have hbG (j : ℕ) (hj : j ≤ s) : ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv j (fun t => D.w t * n08WeightedControlProfile T C i t) r| ≤
        K * T.H r ^ (3 / 64 : ℝ) * T.M (T.sample i) ^ (base + (s + loss)) := by
    obtain ⟨K, hK, hKb⟩ := n08_controlProfile_point_jet_bound hT hS hN j
    refine ⟨K, hK, fun i r hr => (hKb i r hr).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (n08_material_sample_bounds ⟨A, hA⟩ hT i).2 (by omega))
      (mul_nonneg hK (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _))
  obtain ⟨K, hK, hKb⟩ := n08_product_jet_majorant
    (f := fun r => (D.w r)⁻¹)
    (g := fun i r => D.w r * n08WeightedControlProfile T C i r)
    (W := T.M) (V := fun r => T.H r ^ (3 / 64 : ℝ))
    (P := fun i => T.M (T.sample i) ^ (base + (s + loss)))
    isOpen_Ioo (hw.contDiffOn.inv (fun r hr => (hwp r hr).ne'))
    (fun i => (hw.mul (contDiff_const.mul (hcontrol i).1)).contDiffOn)
    (fun r hr => zero_le_one.trans (hT.2.1 r hr).2.2.2)
    (fun r hr => Real.rpow_nonneg (hT.2.1 r hr).2.1.le _)
    (fun i => pow_nonneg (zero_le_one.trans (n08_material_sample_bounds ⟨A, hA⟩ hT i).2) _)
    s hbF hbG
  refine ⟨K, hK, fun i r hr => ?_⟩
  have heq : (fun t => (D.w t)⁻¹ * (D.w t * n08WeightedControlProfile T C i t)) =ᶠ[𝓝 r]
      n08WeightedControlProfile T C i := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact inv_mul_cancel_left₀ (hwp t ht).ne' _
  rw [← heq.iteratedDeriv_eq s]
  exact hKb i r hr

end ContinuousFlexibility.Statements
