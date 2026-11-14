module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A genuine global time change of a compact-interval scalar flow

The smooth transition takes every real time into the prescribed closed
interval and retains its two endpoint values. The within-derivative ODE
on that interval therefore becomes a genuine global time ODE by the
chain rule, including at both ends. No continuation of the original
trajectory outside its time domain is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

/-- One smooth time map treats either order of the two endpoints. -/
def compactScalarFlowTime (a b t : ℝ) : ℝ :=
  a + (b - a) * Real.smoothTransition t

theorem compactScalarFlowTime_zero (a b : ℝ) :
    compactScalarFlowTime a b 0 = a := by
  simp only [compactScalarFlowTime, Real.smoothTransition.zero, mul_zero, add_zero]

theorem compactScalarFlowTime_one (a b : ℝ) :
    compactScalarFlowTime a b 1 = b := by
  simp only [compactScalarFlowTime, Real.smoothTransition.one, mul_one]
  ring

theorem compactScalarFlowTime_mem (a b t : ℝ) :
    compactScalarFlowTime a b t ∈ uIcc a b := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab]
    dsimp only [compactScalarFlowTime]
    have hm0 := mul_nonneg (sub_nonneg.mpr hab) h0
    have hm1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hab)
    constructor <;> nlinarith
  · rw [uIcc_of_ge hba]
    dsimp only [compactScalarFlowTime]
    have hm0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hba) h0
    have hm1 := mul_le_mul_of_nonpos_left h1 (sub_nonpos.mpr hba)
    constructor <;> nlinarith

theorem contDiff_compactScalarFlowTime (a b : ℝ) :
    ContDiff ℝ ∞ (compactScalarFlowTime a b) :=
  contDiff_const.add (contDiff_const.mul Real.smoothTransition.contDiff)

/-- The chosen trajectory is evaluated only on its original time interval. -/
def scalarFlowTimeChange {P : Type*} (Θ : P × ℝ → ℝ)
    (a b : ℝ) (p : P × ℝ) : ℝ :=
  Θ (p.1, compactScalarFlowTime a b p.2)

/-- The transformed speed is the actual chain-rule speed. -/
def scalarFieldTimeChange {P : Type*} (F : P × (ℝ × ℝ) → ℝ)
    (a b : ℝ) (p : P × (ℝ × ℝ)) : ℝ :=
  deriv (compactScalarFlowTime a b) p.2.1 *
    F (p.1, (compactScalarFlowTime a b p.2.1, p.2.2))

theorem continuous_scalarFlowTimeChange
    {P : Type*} [TopologicalSpace P] {Θ : P × ℝ → ℝ} {a b : ℝ}
    (hΘ : ContinuousOn Θ (univ ×ˢ uIcc a b)) :
    Continuous (scalarFlowTimeChange Θ a b) :=
  hΘ.comp_continuous
    (continuous_fst.prodMk ((contDiff_compactScalarFlowTime a b).continuous.comp continuous_snd))
    (fun p => ⟨mem_univ p.1, compactScalarFlowTime_mem a b p.2⟩)

theorem scalarFlowTimeChange_initial {P : Type*}
    (Θ : P × ℝ → ℝ) (a b : ℝ) (p : P) :
    scalarFlowTimeChange Θ a b (p, 0) = Θ (p, a) := by
  simp only [scalarFlowTimeChange, compactScalarFlowTime_zero]

theorem scalarFlowTimeChange_final {P : Type*}
    (Θ : P × ℝ → ℝ) (a b : ℝ) (p : P) :
    scalarFlowTimeChange Θ a b (p, 1) = Θ (p, b) := by
  simp only [scalarFlowTimeChange, compactScalarFlowTime_one]

/-- An actual within-derivative equation gives the global equation after
the smooth time change, without a separate endpoint differentiability assumption. -/
theorem scalarFlowTimeChange_hasDerivAt
    {P : Type*} {Θ : P × ℝ → ℝ} {F : P × (ℝ × ℝ) → ℝ} {a b : ℝ}
    (hflow : ∀ p t, t ∈ uIcc a b →
      HasDerivWithinAt (fun r => Θ (p, r)) (F (p, (t, Θ (p, t)))) (uIcc a b) t)
    (p : P) (t : ℝ) :
    HasDerivAt (fun r => scalarFlowTimeChange Θ a b (p, r))
      (scalarFieldTimeChange F a b (p, (t, scalarFlowTimeChange Θ a b (p, t)))) t := by
  have hτ : HasDerivAt (compactScalarFlowTime a b)
      (deriv (compactScalarFlowTime a b) t) t :=
    ((contDiff_compactScalarFlowTime a b).differentiable (by simp) t).hasDerivAt
  have h := (hflow p _ (compactScalarFlowTime_mem a b t)).comp_hasDerivAt t hτ
    (Eventually.of_forall (compactScalarFlowTime_mem a b))
  have hfun : (fun r => Θ (p, r)) ∘ compactScalarFlowTime a b =
      fun r => scalarFlowTimeChange Θ a b (p, r) := by
    funext r
    exact Function.comp_apply
  rw [hfun] at h
  apply h.congr_deriv
  exact mul_comm _ _

/-- A genuinely smooth vector field stays smooth under the explicit time change. -/
theorem contDiff_scalarFieldTimeChange
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P × (ℝ × ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (scalarFieldTimeChange F a b) := by
  have hτ := contDiff_compactScalarFlowTime a b
  have hτ' : ContDiff ℝ ∞ (deriv (compactScalarFlowTime a b)) :=
    (contDiff_infty_iff_deriv.mp hτ).2
  exact (hτ'.comp contDiff_snd.fst).mul
    (hF.comp (contDiff_fst.prodMk
      ((hτ.comp contDiff_snd.fst).prodMk contDiff_snd.snd)))

end ContinuousFlexibility.Analysis
