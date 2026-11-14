module

public import ContinuousFlexibility.Analysis.N08ControlRestriction
public import ContinuousFlexibility.Analysis.SolveCircleProjection

/-!
# Actual constant control basis in the physical circle space

Each basis element is the genuine angular-constant field supported at one
circle, with amplitude `H_m ^ (3/4)`. Exact realization gives the physical
element. Its control restriction is the unit vector, and its projective
grading costs only the corresponding power of `M_m`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators ENNReal ContDiff

set_option backward.isDefEq.respectTransparency false

def n08ConstantCircleField (m : ℕ) (a : ℝ) : ℕ → ℝ → ℝ :=
  fun n _ => if n = m then a else 0

private theorem n08ConstantCircleField_self (m : ℕ) (a : ℝ) :
    n08ConstantCircleField m a m = fun _ : ℝ => a := by
  funext θ
  exact if_pos rfl

private theorem n08ConstantCircleField_ne {m n : ℕ} (a : ℝ) (hnm : n ≠ m) :
    n08ConstantCircleField m a n = (0 : ℝ → ℝ) := by
  funext θ
  exact if_neg hnm

private theorem n08_iteratedDeriv_zero_function (n : ℕ) :
    iteratedDeriv n (0 : ℝ → ℝ) = 0 :=
  funext fun _ => iteratedDeriv_const_zero

theorem n08ConstantCircleField_mem (T : MaterialData) (γ : ℝ) (m : ℕ) (a : ℝ) :
    CircleMember T γ (n08ConstantCircleField m a) := by
  have hc (n : ℕ) : ContDiff ℝ ∞ (n08ConstantCircleField m a n) := contDiff_const
  have hLp (n b : ℕ) : MemLp (iteratedDeriv b (n08ConstantCircleField m a n))
      2 angleMeasure := memLp_angleMeasure_iteratedDeriv_of_contDiff (hc n) b
  refine ⟨fun n => ⟨hc n, fun _ => rfl⟩, hLp, ?_⟩
  intro s
  rw [tsum_eq_single m (fun n hnm => by
    rw [n08ConstantCircleField_ne a hnm]
    simp only [n08_iteratedDeriv_zero_function, eLpNorm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero])]
  apply ENNReal.sum_lt_top.mpr
  intro j _
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.pow_lt_top (hLp m (j.val 0).val).eLpNorm_lt_top)

private theorem n08_angularMean_const (a : ℝ) : angularMean (fun _ : ℝ => a) = a := by
  rw [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_div]
  exact inv_mul_cancel_left₀ Real.pi_ne_zero a

def n08ControlBasis {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m : ℕ) : CircleSpace S :=
  ((hS.2.1 (3 / 4 : ℝ)).2.2.2.2.1
    (n08ConstantCircleField m (T.H (T.sample m) ^ (3 / 4 : ℝ)))
    (n08ConstantCircleField_mem T (3 / 4 : ℝ) m _)).choose

theorem n08ControlBasis_decode {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    (S.circle (3 / 4 : ℝ)).decode (n08ControlBasis hS m) =
      n08ConstantCircleField m (T.H (T.sample m) ^ (3 / 4 : ℝ)) :=
  ((hS.2.1 (3 / 4 : ℝ)).2.2.2.2.1
    (n08ConstantCircleField m (T.H (T.sample m) ^ (3 / 4 : ℝ)))
    (n08ConstantCircleField_mem T (3 / 4 : ℝ) m _)).choose_spec

theorem n08ControlBasis_mean {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m n : ℕ) :
    angularMean ((S.circle (3 / 4 : ℝ)).decode (n08ControlBasis hS m) n) =
      if n = m then T.H (T.sample m) ^ (3 / 4 : ℝ) else 0 := by
  rw [n08ControlBasis_decode]
  exact n08_angularMean_const _

theorem n08ControlBasis_restriction
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m : ℕ) (hH : 0 < T.H (T.sample m)) :
    n08ControlRestriction S (n08ControlBasis hS m) = lp.single 2 m (1 : ℝ) := by
  apply lp.ext
  funext n
  rw [n08ControlRestriction_apply hS, n08ControlBasis_mean]
  by_cases hn : n = m
  · subst n
    rw [if_pos rfl, lp.single_apply_self, ← Real.rpow_add hH,
      neg_add_cancel, Real.rpow_zero]
  · rw [if_neg hn, mul_zero, lp.single_apply_ne _ _ _ hn]

private def n08AngleConstantNorm : ℝ :=
  (eLpNorm (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure).toReal

private theorem n08AngleConstantNorm_nonneg : 0 ≤ n08AngleConstantNorm :=
  ENNReal.toReal_nonneg

private theorem n08_eLpNorm_const_toReal {a : ℝ} (ha : 0 ≤ a) :
    (eLpNorm (fun _ : ℝ => a) 2 angleMeasure).toReal = a * n08AngleConstantNorm := by
  have he : (fun _ : ℝ => a) = a • (fun _ : ℝ => (1 : ℝ)) := by
    funext θ
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  rw [he, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg ha,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
  rfl

private def n08ControlBasisLevelConstant (s : ℕ) : ℝ :=
  ((Fintype.card (CircleJetIndex s) : ℝ) + 1) * (n08AngleConstantNorm + 1)

private theorem n08ControlBasisLevelConstant_nonneg (s : ℕ) :
    0 ≤ n08ControlBasisLevelConstant s := by
  unfold n08ControlBasisLevelConstant
  exact mul_nonneg (add_nonneg (Nat.cast_nonneg _) zero_le_one)
    (add_nonneg n08AngleConstantNorm_nonneg zero_le_one)

private theorem n08_constantBasis_energy_term_le
    (T : MaterialData) (m s : ℕ) (hH : 0 < T.H (T.sample m))
    (hM : 1 ≤ T.M (T.sample m)) (j : CircleJetIndex s) :
    (ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-(3 / 4 : ℝ))) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val
        (n08ConstantCircleField m (T.H (T.sample m) ^ (3 / 4 : ℝ)) m))
        2 angleMeasure ^ 2).toReal ≤
      (T.M (T.sample m) ^ s * n08AngleConstantNorm) ^ 2 := by
  have hMn : 0 ≤ T.M (T.sample m) := zero_le_one.trans hM
  rw [n08ConstantCircleField_self]
  by_cases hb : (j.val 0).val = 0
  · simp only [hb, iteratedDeriv_zero,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (sq_nonneg _),
      n08_eLpNorm_const_toReal (Real.rpow_pos_of_pos hH _).le]
    have hcancel : T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
        T.H (T.sample m) ^ (3 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hH, neg_add_cancel, Real.rpow_zero]
    calc
      _ = (T.M (T.sample m) ^ (j.val 1).val * n08AngleConstantNorm) ^ 2 := by
        calc
          _ = (T.M (T.sample m) ^ (j.val 1).val *
              (T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
                T.H (T.sample m) ^ (3 / 4 : ℝ)) * n08AngleConstantNorm) ^ 2 := by ring
          _ = _ := by rw [hcancel, mul_one]
      _ ≤ _ := (sq_le_sq₀
        (mul_nonneg (pow_nonneg hMn _) n08AngleConstantNorm_nonneg)
        (mul_nonneg (pow_nonneg hMn _) n08AngleConstantNorm_nonneg)).mpr
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hM (by have hj := j.property; omega))
            n08AngleConstantNorm_nonneg)
  · have hzero : iteratedDeriv (j.val 0).val
        (fun _ : ℝ => T.H (T.sample m) ^ (3 / 4 : ℝ)) = (0 : ℝ → ℝ) := by
      funext θ
      simp only [iteratedDeriv_const, if_neg hb, Pi.zero_apply]
    rw [hzero, eLpNorm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, ENNReal.toReal_zero]
    exact sq_nonneg _

theorem n08ControlBasis_circleNorm_le (T : MaterialData) (m s : ℕ)
    (hH : 0 < T.H (T.sample m)) (hM : 1 ≤ T.M (T.sample m)) :
    circleNorm T (3 / 4 : ℝ) s
      (n08ConstantCircleField m (T.H (T.sample m) ^ (3 / 4 : ℝ))) ≤
        n08ControlBasisLevelConstant s * T.M (T.sample m) ^ s := by
  have hmem := n08ConstantCircleField_mem T (3 / 4 : ℝ) m
    (T.H (T.sample m) ^ (3 / 4 : ℝ))
  have hMn : 0 ≤ T.M (T.sample m) := zero_le_one.trans hM
  unfold circleNorm
  rw [tsum_eq_single m (fun n hnm => by
    rw [n08ConstantCircleField_ne _ hnm]
    simp only [n08_iteratedDeriv_zero_function, eLpNorm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero])]
  apply (Real.sqrt_le_left
    (mul_nonneg (n08ControlBasisLevelConstant_nonneg s) (pow_nonneg hMn _))).mpr
  rw [ENNReal.toReal_sum (fun j _ =>
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top (hmem.2.1 m (j.val 0).val).eLpNorm_lt_top)).ne)]
  calc
    _ ≤ ∑ _j : CircleJetIndex s, (T.M (T.sample m) ^ s * n08AngleConstantNorm) ^ 2 :=
      Finset.sum_le_sum (fun j _ => n08_constantBasis_energy_term_le T m s hH hM j)
    _ = (Fintype.card (CircleJetIndex s) : ℝ) *
        (T.M (T.sample m) ^ s * n08AngleConstantNorm) ^ 2 := by simp
    _ ≤ (n08ControlBasisLevelConstant s * T.M (T.sample m) ^ s) ^ 2 := by
      have hc : 0 ≤ (Fintype.card (CircleJetIndex s) : ℝ) := Nat.cast_nonneg _
      have hn := n08AngleConstantNorm_nonneg
      have hcard : (Fintype.card (CircleJetIndex s) : ℝ) ≤
          ((Fintype.card (CircleJetIndex s) : ℝ) + 1) ^ 2 := by nlinarith
      have hnorm : n08AngleConstantNorm ^ 2 ≤ (n08AngleConstantNorm + 1) ^ 2 := by
        nlinarith
      have h := mul_le_mul hcard hnorm (sq_nonneg n08AngleConstantNorm) (sq_nonneg _)
      have h' := mul_le_mul_of_nonneg_right h (sq_nonneg (T.M (T.sample m) ^ s))
      dsimp only [n08ControlBasisLevelConstant]
      nlinarith only [h']

/-- A single constant works at all lower levels in the projective maximum. -/
def n08ControlBasisConstant (s : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (s + 1), n08ControlBasisLevelConstant i

theorem n08ControlBasisConstant_nonneg (s : ℕ) : 0 ≤ n08ControlBasisConstant s :=
  Finset.sum_nonneg (fun i _ => n08ControlBasisLevelConstant_nonneg i)

theorem n08ControlBasis_grading_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m s : ℕ)
    (hH : 0 < T.H (T.sample m)) (hM : 1 ≤ T.M (T.sample m)) :
    (S.circle (3 / 4 : ℝ)).grading s (n08ControlBasis hS m) ≤
      n08ControlBasisConstant s * T.M (T.sample m) ^ s := by
  have hMn : 0 ≤ T.M (T.sample m) := zero_le_one.trans hM
  apply (gradedSeminorm_le_iff (fun i => (S.circle (3 / 4 : ℝ)).level i)
    (S.circle (3 / 4 : ℝ)).bond s _
    (mul_nonneg (n08ControlBasisConstant_nonneg s) (pow_nonneg hMn _))).mpr
  intro i hi
  rw [(hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2, n08ControlBasis_decode]
  refine (n08ControlBasis_circleNorm_le T m i hH hM).trans ?_
  have hc : n08ControlBasisLevelConstant i ≤ n08ControlBasisConstant s :=
    Finset.single_le_sum (fun j _ => n08ControlBasisLevelConstant_nonneg j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  exact mul_le_mul hc (pow_le_pow_right₀ hM hi) (pow_nonneg hMn _)
    (n08ControlBasisConstant_nonneg s)

end ContinuousFlexibility.Statements
