import ContinuousFlexibility.Analysis.N01ControlWeightConstraint
import ContinuousFlexibility.Analysis.MaterialSampleDiscreteEnvelope

/-!
# Optical normalization controls the actual containing-cell index

The coefficient tower and the flow tower force a positive lower bound on
a product of weights.  Material absorption converts that constraint into
a cubic exponential inequality in the two actual reference-cell indices.
It follows that every cell containing the control component has index
bounded by a fixed multiple of the control sample index plus one.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance n01ControlIndexBoundStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set

theorem indices_le_of_cubic_exp_constraint
    {K L : ℝ} (hK : 0 < K) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 < A ∧ ∀ n m : ℕ,
      1 ≤ K * Real.exp (-(n : ℝ) ^ 3 / 64 + L * ((m : ℝ) + 1) ^ 3) →
      (n : ℝ) ≤ A * ((m : ℝ) + 1) := by
  let A := 64 * (|Real.log K| + L + 1) + 1
  have hA1 : 1 ≤ A := by
    dsimp only [A]
    linarith only [abs_nonneg (Real.log K), hL]
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hAcube : A ≤ A ^ 3 := by
    nlinarith only [mul_nonneg hA.le (sub_nonneg.mpr hA1),
      mul_nonneg (sub_nonneg.mpr hA1) (sq_nonneg A)]
  refine ⟨A, hA, fun n m he => ?_⟩
  let y : ℝ := (m : ℝ) + 1
  have hy : 1 ≤ y := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    dsimp only [y]
    linarith only [hm0]
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hy3 : 1 ≤ y ^ 3 := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hy 3
  have hlog : 0 ≤ Real.log K - (n : ℝ) ^ 3 / 64 + L * y ^ 3 := by
    have he' : Real.exp 0 ≤
        Real.exp (Real.log K + (-(n : ℝ) ^ 3 / 64 + L * y ^ 3)) := by
      simpa only [Real.exp_zero, Real.exp_add, Real.exp_log hK] using he
    have hh := Real.exp_le_exp.mp he'
    linarith only [hh]
  have hcube : (n : ℝ) ^ 3 ≤ A ^ 3 * y ^ 3 := by
    have habs := le_abs_self (Real.log K)
    have hlogBound := mul_le_mul_of_nonneg_left hy3 (abs_nonneg (Real.log K))
    have hAA := mul_le_mul_of_nonneg_right hAcube (pow_nonneg hy0.le 3)
    have hfirst : (n : ℝ) ^ 3 ≤ A * y ^ 3 := by
      dsimp only [A]
      nlinarith only [hlog, habs, hlogBound, pow_nonneg hy0.le 3]
    exact hfirst.trans hAA
  by_contra hn
  have hn' : A * y < (n : ℝ) := lt_of_not_ge hn
  have hstrict : (A * y) ^ 3 < (n : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hn' (mul_pos hA hy0).le (by decide)
  nlinarith only [hstrict, hcube]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.control_actual_cell_cubic_exp_constraint
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      1 ≤ K * Real.exp (-(D.cellIndex j : ℝ) ^ 3 / 64 +
        L * ((D.cellIndex m : ℝ) + 1) ^ 3) := by
  obtain ⟨d₂, K, B, A, F, hK, _, _, _, hconstraint⟩ :=
    hN.control_actual_cell_weight_constraint hS hT
  obtain ⟨CE, hCE, he⟩ :=
    materialSample_H_E0_envelope hT hN.1.1 (γ := (3 / 8 : ℝ)) (by norm_num) B
  obtain ⟨CR, hCR, hr⟩ :=
    materialSample_H_radialE_envelope hT hN.1.1 (γ := (3 / 8 : ℝ)) (by norm_num) A
  obtain ⟨CC, hCC, hc⟩ :=
    materialSample_H_E0_envelope hT hN.1.1 (γ := (3 / 4 : ℝ)) (by norm_num) F
  let d : ℕ := max base (1 + loss) + max base (loss + d₂) * 2
  obtain ⟨CM, hCM, hm⟩ :=
    materialSample_H_M_envelope hT hN.1.1 (γ := (3 / 4 : ℝ)) (by norm_num) (d : ℝ)
  obtain ⟨CH, L, hCH, hL, hh⟩ :=
    materialSample_H_neg_envelope hT hN.1.1 (γ := (3 : ℝ)) (by norm_num)
  let K0 := K * CE * CR * CC * CM * CH
  have hK0 : 0 < K0 := by dsimp only [K0]; positivity
  obtain ⟨_, hgeom⟩ := hN.1.1
  refine ⟨K0, L, hK0, hL, fun m j hcell => ?_⟩
  have hpos (i : ℕ) := hT.2.1 (T.sample i)
    (materialSample_mem_radialCore hT hgeom.2.1 i)
  let Hj := T.H (T.sample j)
  let Hm := T.H (T.sample m)
  let Mm := T.M (T.sample m)
  have hHj : 0 < Hj := (hpos j).2.1
  have hHm : 0 < Hm := (hpos m).2.1
  have hMm : 0 < Mm := zero_lt_one.trans_le (hpos m).2.2.2
  have hsplit : Hj ^ (3 / 4 : ℝ) =
      Hj ^ (3 / 8 : ℝ) * Hj ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add hHj]
    norm_num
  have hnegative : Hm ^ (-(3 / 4 : ℝ)) * (Hm ^ (-(3 / 4 : ℝ))) ^ 2 =
      Hm ^ (3 / 4 : ℝ) * Hm ^ (-3 : ℝ) := by
    simp only [Real.rpow_def_of_pos hHm, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hMd : Mm ^ d = Mm ^ max base (1 + loss) * (Mm ^ max base (loss + d₂)) ^ 2 := by
    simp only [d, pow_add, pow_mul]
  have hm' : Hm ^ (3 / 4 : ℝ) * Mm ^ d ≤ CM := by
    simpa only [Real.rpow_natCast] using hm m
  have he' := he j
  have hr' := hr j
  have hc' := hc (C.cell m)
  have hh' := hh m
  have hraw := hconstraint m j hcell
  have hrearrange :
      K * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B *
        radialE (D.cellIndex j) ^ A *
        T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ F *
        ((Mm ^ max base (1 + loss) * Hm ^ (-(3 / 4 : ℝ))) *
          (Mm ^ max base (loss + d₂) * Hm ^ (-(3 / 4 : ℝ))) ^ 2) =
      K * (Hj ^ (3 / 8 : ℝ) * T.E0 (T.sample j) ^ B) *
        (Hj ^ (3 / 8 : ℝ) * radialE (D.cellIndex j) ^ A) *
        (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ F) *
        (Hm ^ (3 / 4 : ℝ) * Mm ^ d) * Hm ^ (-3 : ℝ) := by
    change K * Hj ^ (3 / 4 : ℝ) * _ * _ * _ * _ * _ = _
    calc
      _ = K * (Hj ^ (3 / 8 : ℝ) * T.E0 (T.sample j) ^ B) *
          (Hj ^ (3 / 8 : ℝ) * radialE (D.cellIndex j) ^ A) *
          (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ F) *
          Mm ^ d * (Hm ^ (-(3 / 4 : ℝ)) * (Hm ^ (-(3 / 4 : ℝ))) ^ 2) := by
        rw [hsplit, hMd]
        ring
      _ = _ := by rw [hnegative]; ring
  rw [hrearrange] at hraw
  have hbound :
      K * (Hj ^ (3 / 8 : ℝ) * T.E0 (T.sample j) ^ B) *
        (Hj ^ (3 / 8 : ℝ) * radialE (D.cellIndex j) ^ A) *
        (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ F) *
        (Hm ^ (3 / 4 : ℝ) * Mm ^ d) * Hm ^ (-3 : ℝ) ≤
      K * CE * (CR * radialH (D.cellIndex j) ^ ((3 / 8 : ℝ) / 16)) *
        CC * CM * (CH * Real.exp (L * ((D.cellIndex m : ℝ) + 1) ^ 3)) := by
    have hE : 0 < T.E0 (T.sample j) := (hpos j).2.2.1
    have hHC : 0 < T.H (T.sample (C.cell m)) := (hpos (C.cell m)).2.1
    have hEC : 0 < T.E0 (T.sample (C.cell m)) := (hpos (C.cell m)).2.2.1
    have hR : 0 < radialE (D.cellIndex j) := Real.exp_pos _
    have hRH : 0 < radialH (D.cellIndex j) := Real.exp_pos _
    apply mul_le_mul _ (hh m) (by positivity) (by positivity)
    apply mul_le_mul _ hm' (by positivity) (by positivity)
    apply mul_le_mul _ (hc (C.cell m)) (by positivity) (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (he j) hK.le) (hr j)
      (by positivity) (by positivity)
  have hcombined := hraw.trans hbound
  have hradial : radialH (D.cellIndex j) ^ ((3 / 8 : ℝ) / 16) =
      Real.exp (-(D.cellIndex j : ℝ) ^ 3 / 64) := by
    rw [radialH, ← Real.exp_mul, radialS]
    congr 1
    ring
  rw [hradial] at hcombined
  exact hcombined.trans_eq (by
    dsimp only [K0]
    rw [Real.exp_add]
    ring)

theorem N01Properties.control_actual_cell_index_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ A : ℝ, 0 < A ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (D.cellIndex j : ℝ) ≤ A * ((D.cellIndex m : ℝ) + 1) := by
  obtain ⟨K, L, hK, hL, hb⟩ := hN.control_actual_cell_cubic_exp_constraint hS hT
  obtain ⟨A, hA, hindex⟩ := indices_le_of_cubic_exp_constraint hK hL.le
  exact ⟨A, hA, fun m j hij => hindex _ _ (hb m j hij)⟩

end ContinuousFlexibility.Statements
