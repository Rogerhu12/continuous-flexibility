module

public import ContinuousFlexibility.Analysis.N01aReferenceHeightMajorants
public import ContinuousFlexibility.Analysis.N01aOpticalProfile
public import ContinuousFlexibility.Analysis.AffineMaterialSampling
public import ContinuousFlexibility.Analysis.N01aJacobiTransfer

/-!
# Reference-kernel jets from the actual Jacobi equation

The optical radicand supplies both coefficients of the scalar equation.
The cell bounds become powers of the actual material envelope, so the
pointwise Cauchy-data factor is preserved at every ordinary derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n01a_cell_coefficient_le_material_M {D : ReferenceData} {sample : ℕ → ℝ}
    (hD : IsAccumulatingProfile D) {f : ℝ → ℝ}
    (hb : ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ D.cells m →
      |f r| ≤ B * radialE (D.cellIndex m) ^ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D,
      |f r| ≤ C * (affineMaterialData D sample).M r := by
  have hdata := hD
  obtain ⟨C₀, hprofile⟩ := hdata
  have hgeom := hprofile.1
  have hpart := hprofile.2.1
  obtain ⟨B, hB, hb⟩ := hb
  obtain ⟨A, J, hA, hJ, hlog⟩ := affineMaterialData_cell_log_bounds (sample := sample) hD
  obtain ⟨K, hK, henv⟩ := affineMaterialData_E0_rpow_le_M
    (D := D) (sample := sample) (A * B)
  refine ⟨B * K, mul_nonneg hB.le hK.le, fun r hr => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.localizer m r ≠ 0 := by
    by_contra hn
    have hz : ∀ m, D.localizer m r = 0 :=
      fun m => not_ne_iff.mp (fun hm => hn ⟨m, hm⟩)
    have hs := (hpart.2.2.2.2.1 r hr).2
    simp only [hz, tsum_zero] at hs
    exact zero_ne_one hs
  have hcell : r ∈ D.cells m := hpart.2.2.1 m hm
  have hE : 0 < (affineMaterialData D sample).E0 r :=
    (affineMaterialData_positive (sample := sample) hgeom.2.1 hr).2.2.1
  have hpow : radialE (D.cellIndex m) ^ B ≤
      (affineMaterialData D sample).E0 r ^ (A * B) := by
    rw [radialE, ← Real.exp_mul, Real.rpow_def_of_pos hE]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (hlog m r hcell).2.1 hB.le
    nlinarith only [h]
  calc
    _ ≤ B * ((affineMaterialData D sample).E0 r ^ (A * B)) :=
      (hb m r hcell).trans (mul_le_mul_of_nonneg_left hpow hB.le)
    _ ≤ B * (K * (affineMaterialData D sample).M r) :=
      mul_le_mul_of_nonneg_left (henv r hr) hB.le
    _ = _ := by ring

theorem n01a_reference_phi_physical_jets {D : ReferenceData} {sample : ℕ → ℝ}
    (hD : IsRadialReference D) (k : ℕ) :
    N01aPointwiseBound (radialCore D) (affineMaterialData D sample).M
      (fun r => |D.phi r| + |deriv D.phi r|) (iteratedDeriv k D.phi) := by
  obtain ⟨C₀, hprofile⟩ := hD.1
  have hgeom := hprofile.1
  let T := affineMaterialData D sample
  let q := n01aOpticalRadicand D.w
  have hM (r : ℝ) (hr : r ∈ radialCore D) : 1 ≤ T.M r :=
    (affineMaterialData_positive (sample := sample) hgeom.2.1 hr).2.2.2
  have hq : ContDiffOn ℝ ∞ q (radialCore D) := fun r hr =>
    (contDiffAt_n01aOpticalRadicand hgeom.2.2.1.1
      (hgeom.1.trans hr.1).ne' (hgeom.2.2.2.2.1 r hr).ne').contDiffWithinAt
  have hqB (j : ℕ) : N01aPointwiseBound (radialCore D) T.M (fun _ => 1)
      (iteratedDeriv j q) := by
    obtain ⟨C, hC, hb⟩ := n01a_cell_coefficient_le_material_M
      (sample := sample) hD.1 (n01aOpticalRadicand_cell_jets hD.1 j)
    exact ⟨1, C, hC, fun r hr => by simpa only [pow_one, mul_one] using hb r hr⟩
  have hidB (j : ℕ) : N01aPointwiseBound (radialCore D) T.M (fun _ => 1)
      (iteratedDeriv j (fun r : ℝ => r)) := by
    apply n01aPointwiseBound_uniform
      (show 0 ≤ |D.a| + |D.b| + 1 by positivity)
    intro r hr
    rw [iteratedDeriv_fun_id]
    split_ifs
    · exact abs_le.mpr ⟨by linarith [hr.1, neg_abs_le D.a, abs_nonneg D.b],
        by linarith [hr.2, le_abs_self D.b, abs_nonneg D.a]⟩
    · simpa only [abs_one] using
        (show (1 : ℝ) ≤ |D.a| + |D.b| + 1 by
          linarith only [abs_nonneg D.a, abs_nonneg D.b])
    · simp only [abs_zero]
      positivity
  have haB (j : ℕ) : N01aPointwiseBound (radialCore D) T.M (fun _ => 1)
      (iteratedDeriv j (fun r => (-4 : ℝ) * q r)) := by
    apply ((hqB j).const_mul (fun r hr => zero_le_one.trans (hM r hr)) (-4)).congr
    intro r hr
    exact (iteratedDeriv_const_mul_field (-4 : ℝ) q).symm
  have hbB (j : ℕ) : N01aPointwiseBound (radialCore D) T.M (fun _ => 1)
      (iteratedDeriv j (fun r => r * q r)) :=
    n01aPointwiseBound_iteratedDeriv_mul j hM (fun _ _ => zero_le_one)
      (fun _ _ => contDiffAt_id)
      (fun r hr => (hq r hr).contDiffAt (isOpen_Ioo.mem_nhds hr))
      (fun i _ => hidB i) (fun i _ => hqB i)
  apply n01aPointwiseJets_of_secondOrder isOpen_Ioo hM
    hgeom.2.2.2.1.1.contDiffOn (contDiffOn_const.mul hq) (contDiffOn_id.mul hq) haB hbB _ k
  intro r hr
  rw [n01a_second_deriv_of_jacobi hgeom.2.2.1.1 hgeom.2.2.2.1.1
    (hgeom.1.trans hr.1).ne' (hgeom.2.2.2.2.1 r hr).ne' (hD.2.1.1 r hr)]
  dsimp only [q, n01aOpticalRadicand, id]
  field_simp [(hgeom.1.trans hr.1).ne', (hgeom.2.2.2.2.1 r hr).ne']
  <;> ring

end ContinuousFlexibility.Statements
