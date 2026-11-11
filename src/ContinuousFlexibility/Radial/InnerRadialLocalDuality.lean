import ContinuousFlexibility.Radial.InnerRadialPotentialGraph

/-!
# Actual local Dirichlet existence implies zero-kernel uniqueness

A homogeneous field is tested against the already constructed solution
for each genuine physical L² source and scalar row. The actual signed
potential is symmetric. This forces the value and scalar to vanish;
testing the homogeneous equation by itself then kills its gradient.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped InnerProductSpace

theorem innerRadialLocalKernel_unique_of_solutions (D : ReferenceData)
    (j a b : ℝ) (bordered : Bool) (column : RadialModeL2 D)
    (hsolve : ∀ (F : RadialModeL2 D) (rowF : ℝ),
      (bordered = false → rowF = 0) →
      ∃ (Q : InnerRadialH1Pair D) (V : RadialModeL2 D) (scalar : ℝ),
        Q ∈ innerRadialH1Zero D a b ∧ InnerRadialPotentialClass D j a b Q.1 V ∧
        (if bordered then ⟪column, Q.1⟫_ℝ = rowF else scalar = 0 ∧ rowF = 0) ∧
        ∀ T ∈ innerRadialH1Zero D a b,
          innerRadialWeakResidual D Q V F column scalar T = 0)
    (q : InnerRadialH1Pair D) (v : RadialModeL2 D) (scalar : ℝ)
    (hq : q ∈ innerRadialH1Zero D a b)
    (hv : InnerRadialPotentialClass D j a b q.1 v)
    (hrow : if bordered then ⟪column, q.1⟫_ℝ = 0 else scalar = 0)
    (hweak : ∀ T ∈ innerRadialH1Zero D a b,
      innerRadialWeakResidual D q v 0 column scalar T = 0) :
    q = 0 ∧ v = 0 ∧ scalar = 0 := by
  have hdual (F : RadialModeL2 D) (rowF : ℝ) (hF : bordered = false → rowF = 0) :
      ⟪F, q.1⟫_ℝ + scalar * rowF = 0 := by
    obtain ⟨Q, V, c, hQ, hV, hr, he⟩ := hsolve F rowF hF
    have hk := hweak Q hQ
    have hf := he q hq
    change ⟪q.2, Q.2⟫_ℝ + ⟪v, Q.1⟫_ℝ +
      scalar * ⟪column, Q.1⟫_ℝ - ⟪(0 : RadialModeL2 D), Q.1⟫_ℝ = 0 at hk
    change ⟪Q.2, q.2⟫_ℝ + ⟪V, q.1⟫_ℝ +
      c * ⟪column, q.1⟫_ℝ - ⟪F, q.1⟫_ℝ = 0 at hf
    rw [inner_zero_left, sub_zero, real_inner_comm Q.2 q.2, hv.inner_symm hV] at hk
    cases bordered with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hrow hr
      rw [hrow, zero_mul, add_zero] at hk
      rw [hr.1, zero_mul, add_zero] at hf
      rw [hrow, zero_mul, add_zero]
      linarith only [hk, hf]
    | true =>
      simp only [ite_true] at hrow hr
      rw [hr] at hk
      rw [hrow, mul_zero, add_zero] at hf
      linarith only [hk, hf]
  have hvalue : q.1 = 0 := by
    have h := hdual q.1 0 (fun _ => rfl)
    rw [mul_zero, add_zero] at h
    exact inner_self_eq_zero.mp h
  have hscalar : scalar = 0 := by
    cases bordered with
    | false => simpa only [Bool.false_eq_true, ite_false] using hrow
    | true =>
      have h := hdual 0 1 (by simp)
      simpa only [inner_zero_left, mul_one, zero_add] using h
  have hpotential : v = 0 := hv.eq_zero_of_value_eq_zero hvalue
  have hgrad : q.2 = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have h := hweak q hq
    simpa only [innerRadialWeakResidual_apply, hvalue, hpotential, inner_zero_left,
      inner_zero_right, mul_zero, add_zero, sub_zero] using h
  exact ⟨Prod.ext hvalue hgrad, hpotential, hscalar⟩

end ContinuousFlexibility.Radial
