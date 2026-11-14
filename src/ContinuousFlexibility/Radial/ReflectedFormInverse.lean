module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module

/-!
# Inverting a form by reflection in its low modes

Let a Hilbert form space have a function coordinate `base` and a derivative
coordinate `grad`. A bounded projection splits it into low and high modes.
If the derivative energy of every low mode is at most half its spectral
mass, and the mass of every high mode is at most half its derivative energy,
reflection of the test argument makes the shifted form coercive. The
Lax--Milgram inverse then solves the original form equation, with an actual
`L²` bound `4 / Λ` independent of the form norm of the projection.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Pull back the inner product along a bounded coordinate map. -/
def coordinateInner (a : V →L[ℝ] H) : V →L[ℝ] V →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ V H ℝ).flip a ∘L ((innerSL ℝ) ∘L a)

theorem coordinateInner_apply (a : V →L[ℝ] H) (u v : V) :
    coordinateInner a u v = ⟪a u, a v⟫_ℝ := by
  simp only [coordinateInner, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  exact innerSL_apply_apply ℝ (a u) (a v)

/-- The form of `A - Λ`, on its closed energy domain. -/
def shiftedEnergyForm (base grad : V →L[ℝ] H) (Λ : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  coordinateInner grad - Λ • coordinateInner base

theorem shiftedEnergyForm_apply (base grad : V →L[ℝ] H) (Λ : ℝ) (u v : V) :
    shiftedEnergyForm base grad Λ u v =
      ⟪grad u, grad v⟫_ℝ - Λ * ⟪base u, base v⟫_ℝ := by
  simp only [shiftedEnergyForm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, coordinateInner_apply, smul_eq_mul]

/-- Reflection across the high mode space. -/
def lowModeReflection (P : V →L[ℝ] V) : V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V - (2 : ℝ) • P

theorem lowModeReflection_apply (P : V →L[ℝ] V) (u : V) :
    lowModeReflection P u = u - (2 : ℝ) • P u := by
  simp only [lowModeReflection, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]

theorem lowModeReflection_involutive (P : V →L[ℝ] V)
    (hP : ∀ u : V, P (P u) = P u) : Function.Involutive (lowModeReflection P) := by
  intro u
  simp only [lowModeReflection_apply, map_sub, map_smul, hP]
  module

/-- The form with its test argument reflected. -/
def reflectedEnergyForm (base grad : V →L[ℝ] H) (Λ : ℝ) (P : V →L[ℝ] V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ V V ℝ).flip (lowModeReflection P) ∘L
    shiftedEnergyForm base grad Λ

theorem reflectedEnergyForm_apply (base grad : V →L[ℝ] H) (Λ : ℝ)
    (P : V →L[ℝ] V) (u v : V) :
    reflectedEnergyForm base grad Λ P u v =
      shiftedEnergyForm base grad Λ u (lowModeReflection P v) := by
  simp only [reflectedEnergyForm, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]

private theorem norm_add_sq_le_two (x y : H) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := mul_self_le_mul_self (norm_nonneg (x + y)) (norm_add_le x y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem norm_sub_sq_le_two (x y : H) :
    ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  simpa only [sub_eq_add_neg, norm_neg] using norm_add_sq_le_two x (-y)

theorem reflectedEnergyForm_diagonal (base grad : V →L[ℝ] H) (Λ : ℝ)
    (P : V →L[ℝ] V) (u : V) :
    reflectedEnergyForm base grad Λ P u u =
      ‖grad (u - P u)‖ ^ 2 - ‖grad (P u)‖ ^ 2 -
        Λ * ‖base (u - P u)‖ ^ 2 + Λ * ‖base (P u)‖ ^ 2 := by
  rw [reflectedEnergyForm_apply, shiftedEnergyForm_apply, lowModeReflection_apply]
  simp only [map_sub, map_smul, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_sub_sq_real]
  ring

/-- The two numerical inequalities give all estimates needed for coercivity
and for the final `L²` inverse bound. -/
theorem reflectedEnergyForm_bounds (base grad : V →L[ℝ] H) {Λ : ℝ}
    (hΛ : 0 < Λ) (P : V →L[ℝ] V)
    (hlow : ∀ u : V, ‖grad (P u)‖ ^ 2 ≤ (Λ / 2) * ‖base (P u)‖ ^ 2)
    (hhigh : ∀ u : V, Λ * ‖base (u - P u)‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖grad (u - P u)‖ ^ 2)
    (u : V) :
    0 ≤ reflectedEnergyForm base grad Λ P u u ∧
      ‖grad u‖ ^ 2 + Λ * ‖base u‖ ^ 2 ≤ 6 * reflectedEnergyForm base grad Λ P u u ∧
      Λ * ‖base u‖ ^ 2 ≤ 4 * reflectedEnergyForm base grad Λ P u u ∧
      Λ * ‖base (lowModeReflection P u)‖ ^ 2 ≤
        4 * reflectedEnergyForm base grad Λ P u u := by
  have hlow' := hlow u
  have hhigh' := hhigh u
  have hd := reflectedEnergyForm_diagonal base grad Λ P u
  have hnonneg₀ : 0 ≤ ‖grad (u - P u)‖ ^ 2 := sq_nonneg _
  have hnonneg₁ : 0 ≤ Λ * ‖base (P u)‖ ^ 2 := mul_nonneg hΛ.le (sq_nonneg _)
  have hmain : ‖grad (u - P u)‖ ^ 2 + Λ * ‖base (P u)‖ ^ 2 ≤
      2 * reflectedEnergyForm base grad Λ P u u := by
    linarith
  have hbase : ‖base u‖ ^ 2 ≤
      2 * (‖base (u - P u)‖ ^ 2 + ‖base (P u)‖ ^ 2) := by
    have heq : base (u - P u) + base (P u) = base u := by
      rw [← map_add, sub_add_cancel]
    simpa only [heq] using norm_add_sq_le_two (base (u - P u)) (base (P u))
  have hgrad : ‖grad u‖ ^ 2 ≤
      2 * (‖grad (u - P u)‖ ^ 2 + ‖grad (P u)‖ ^ 2) := by
    have heq : grad (u - P u) + grad (P u) = grad u := by
      rw [← map_add, sub_add_cancel]
    simpa only [heq] using norm_add_sq_le_two (grad (u - P u)) (grad (P u))
  have hreflect : ‖base (lowModeReflection P u)‖ ^ 2 ≤
      2 * (‖base (u - P u)‖ ^ 2 + ‖base (P u)‖ ^ 2) := by
    have heq : base (u - P u) - base (P u) = base (lowModeReflection P u) := by
      rw [← map_sub, lowModeReflection_apply]
      congr 1
      module
    simpa only [heq] using norm_sub_sq_le_two (base (u - P u)) (base (P u))
  have hbaseΛ := mul_le_mul_of_nonneg_left hbase hΛ.le
  have hreflectΛ := mul_le_mul_of_nonneg_left hreflect hΛ.le
  refine ⟨by linarith, ?_, ?_, ?_⟩ <;> nlinarith

theorem reflectedEnergyForm_isCoercive (base grad : V →L[ℝ] H) {Λ : ℝ}
    (hΛ : 0 < Λ) (P : V →L[ℝ] V)
    (hnorm : ∀ u : V, ‖u‖ ^ 2 = ‖base u‖ ^ 2 + ‖grad u‖ ^ 2)
    (hlow : ∀ u : V, ‖grad (P u)‖ ^ 2 ≤ (Λ / 2) * ‖base (P u)‖ ^ 2)
    (hhigh : ∀ u : V, Λ * ‖base (u - P u)‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖grad (u - P u)‖ ^ 2) :
    IsCoercive (reflectedEnergyForm base grad Λ P) := by
  refine ⟨min 1 Λ / 6, div_pos (lt_min zero_lt_one hΛ) (by norm_num), ?_⟩
  intro u
  have hb := (reflectedEnergyForm_bounds base grad hΛ P hlow hhigh u).2.1
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) Λ) (sq_nonneg ‖grad u‖)
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) Λ) (sq_nonneg ‖base u‖)
  have hn := congrArg (fun r : ℝ => min 1 Λ * r) (hnorm u)
  nlinarith

private theorem reflected_form_l2_bound (base grad : V →L[ℝ] H) {Λ : ℝ}
    (hΛ : 0 < Λ) (P : V →L[ℝ] V)
    (hlow : ∀ u : V, ‖grad (P u)‖ ^ 2 ≤ (Λ / 2) * ‖base (P u)‖ ^ 2)
    (hhigh : ∀ u : V, Λ * ‖base (u - P u)‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖grad (u - P u)‖ ^ 2)
    (u : V) (f : H)
    (heq : reflectedEnergyForm base grad Λ P u u = ⟪f, base (lowModeReflection P u)⟫_ℝ) :
    ‖base u‖ ≤ (4 / Λ) * ‖f‖ := by
  obtain ⟨hD, _, hu, hS⟩ := reflectedEnergyForm_bounds base grad hΛ P hlow hhigh u
  have hCS : reflectedEnergyForm base grad Λ P u u ≤
      ‖f‖ * ‖base (lowModeReflection P u)‖ := by
    rw [heq]
    exact real_inner_le_norm _ _
  have hSN : Λ * ‖base (lowModeReflection P u)‖ ≤ 4 * ‖f‖ := by
    by_cases hzero : ‖base (lowModeReflection P u)‖ = 0
    · rw [hzero, mul_zero]
      positivity
    · have hpos : 0 < ‖base (lowModeReflection P u)‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      have hprod : ‖base (lowModeReflection P u)‖ *
          (Λ * ‖base (lowModeReflection P u)‖ - 4 * ‖f‖) ≤ 0 := by
        nlinarith
      have hsub : Λ * ‖base (lowModeReflection P u)‖ - 4 * ‖f‖ ≤ 0 :=
        le_of_mul_le_mul_left (by simpa only [mul_zero] using hprod) hpos
      exact sub_nonpos.mp hsub
  have hΛD : Λ * reflectedEnergyForm base grad Λ P u u ≤ 4 * ‖f‖ ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hCS hΛ.le
    have h₂ := mul_le_mul_of_nonneg_left hSN (norm_nonneg f)
    nlinarith
  have huΛ := mul_le_mul_of_nonneg_left hu hΛ.le
  have hsq : (Λ * ‖base u‖) ^ 2 ≤ (4 * ‖f‖) ^ 2 := by nlinarith
  have hnorm : Λ * ‖base u‖ ≤ 4 * ‖f‖ :=
    (sq_le_sq₀ (mul_nonneg hΛ.le (norm_nonneg _)) (by positivity)).mp hsq
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hΛ).mpr
  nlinarith

/-- The reflection argument constructs a bounded solution operator, proves
uniqueness on the form domain, and obtains the quantitative ambient `L²` norm. -/
theorem exists_reflectedFormInverse (base grad : V →L[ℝ] H) {Λ : ℝ}
    (hΛ : 0 < Λ) (P : V →L[ℝ] V)
    (hP : ∀ u : V, P (P u) = P u)
    (hnorm : ∀ u : V, ‖u‖ ^ 2 = ‖base u‖ ^ 2 + ‖grad u‖ ^ 2)
    (hlow : ∀ u : V, ‖grad (P u)‖ ^ 2 ≤ (Λ / 2) * ‖base (P u)‖ ^ 2)
    (hhigh : ∀ u : V, Λ * ‖base (u - P u)‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖grad (u - P u)‖ ^ 2) :
    ∃ X : H →L[ℝ] V,
      (∀ f : H, ∀ v : V,
        shiftedEnergyForm base grad Λ (X f) v = ⟪f, base v⟫_ℝ) ∧
      (∀ f : H, ∀ u : V,
        (∀ v : V, shiftedEnergyForm base grad Λ u v = ⟪f, base v⟫_ℝ) → X f = u) ∧
      ‖base ∘L X‖ ≤ 4 / Λ := by
  let hc : IsCoercive (reflectedEnergyForm base grad Λ P) :=
    reflectedEnergyForm_isCoercive base grad hΛ P hnorm hlow hhigh
  let A : V ≃L[ℝ] V := hc.continuousLinearEquivOfBilin
  let R : H →L[ℝ] V := (base ∘L lowModeReflection P).adjoint
  let X : H →L[ℝ] V := A.symm.toContinuousLinearMap ∘L R
  have hX (f : H) : A (X f) = R f := by
    simp only [X, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  have hform (f : H) (v : V) :
      reflectedEnergyForm base grad Λ P (X f) v =
        ⟪f, base (lowModeReflection P v)⟫_ℝ := by
    rw [← hc.continuousLinearEquivOfBilin_apply, hX]
    exact ContinuousLinearMap.adjoint_inner_left (base ∘L lowModeReflection P) v f
  have hsolve (f : H) (v : V) :
      shiftedEnergyForm base grad Λ (X f) v = ⟪f, base v⟫_ℝ := by
    have h := hform f (lowModeReflection P v)
    rwa [reflectedEnergyForm_apply, lowModeReflection_involutive P hP v] at h
  refine ⟨X, hsolve, ?_, ?_⟩
  · intro f u hu
    have hAu : R f = A u := by
      apply hc.unique_continuousLinearEquivOfBilin
      intro v
      rw [ContinuousLinearMap.adjoint_inner_left, reflectedEnergyForm_apply]
      exact (hu (lowModeReflection P v)).symm
    apply A.injective
    exact (hX f).trans hAu
  · apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (by norm_num) hΛ.le)
    intro f
    rw [ContinuousLinearMap.comp_apply]
    exact reflected_form_l2_bound base grad hΛ P hlow hhigh (X f) f (hform f (X f))

end ContinuousFlexibility.Radial
