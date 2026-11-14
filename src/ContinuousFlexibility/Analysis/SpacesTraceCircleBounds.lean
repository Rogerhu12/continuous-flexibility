module

public import ContinuousFlexibility.Analysis.CircleJetEncoding
public import ContinuousFlexibility.Analysis.SpacesTraceGeometry
public import Mathlib.Analysis.MeanInequalities

/-!
# Pointwise control of the rows of circle jets

The actual weak first derivative evaluation controls a weighted angular jet by
two coordinates in its Hilbert row. Cauchy--Schwarz then supplies a summable
majorant for the localized extension packets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

def spaces_circle_jet_index (b c s : ℕ) (h : b + c ≤ s) : CircleJetIndex s :=
  ⟨![⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using h⟩

theorem spaces_contDiff_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (b : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv b f) := by
  induction b with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ b ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

theorem spaces_periodic_iteratedDeriv {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (b : ℕ) :
    Function.Periodic (iteratedDeriv b f) Real.pi := by
  intro x
  have hshift : (fun t : ℝ => f (t + Real.pi)) = f := funext hp
  have h := congrFun (iteratedDeriv_comp_add_const b f Real.pi) x
  rw [hshift] at h
  exact h.symm

/-- The bound uses the norm of one sample row, retaining the outer square
summability of the given circle datum. -/
theorem spaces_circle_weighted_pointwise {T : MaterialData} {γ : ℝ}
    {f : ℕ → ℝ → ℝ} (hf : CircleMember T γ f)
    (s m b c : ℕ) (horder : b + c + 1 ≤ s) (θ : ℝ) :
    |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) * iteratedDeriv b (f m) θ| ≤
      anglePairEvaluationConstant * ‖circleJetEncodeHilbert hf s m‖ := by
  let z := circleJetEncodeHilbert hf s m
  let j₀ := spaces_circle_jet_index b c s (by omega)
  let j₁ := spaces_circle_jet_index (b + 1) c s (by omega)
  let A := T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)
  let g : ℝ → ℝ := fun x => A * iteratedDeriv b (f m) x
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul (spaces_contDiff_iteratedDeriv (hf.1 m).1 b)
  have hp : Function.Periodic g Real.pi := by
    intro x
    exact congrArg (A * ·) (spaces_periodic_iteratedDeriv (hf.1 m).2 b x)
  have hd : iteratedDeriv 1 g = fun x => A * iteratedDeriv (b + 1) (f m) x := by
    rw [iteratedDeriv_one]
    change deriv (fun x => A * iteratedDeriv b (f m) x) = _
    rw [deriv_const_mul_field', iteratedDeriv_succ]
  have h₀ : MemLp g 2 angleMeasure := memLp_angleMeasure_of_continuous hg.continuous
  have h₁ : MemLp (iteratedDeriv 1 g) 2 angleMeasure :=
    memLp_angleMeasure_iteratedDeriv_of_contDiff hg 1
  have hz₀ : (⇑(z j₀)) =ᵐ[angleMeasure] g := by
    simpa only [z, j₀, spaces_circle_jet_index, circleJetWeight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, A, g] using circleJetEncodeHilbert_ae hf s m j₀
  have hz₁ : (⇑(z j₁)) =ᵐ[angleMeasure] iteratedDeriv 1 g := by
    rw [hd]
    simpa only [z, j₁, spaces_circle_jet_index, circleJetWeight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, A] using circleJetEncodeHilbert_ae hf s m j₁
  have he₀ : h₀.toLp g = z j₀ := Lp.ext ((MemLp.coeFn_toLp h₀).trans hz₀.symm)
  have he₁ : h₁.toLp (iteratedDeriv 1 g) = z j₁ :=
    Lp.ext ((MemLp.coeFn_toLp h₁).trans hz₁.symm)
  have hw := hasWeakAngularDerivative_toLp_iteratedDeriv hg hp 1 h₀ h₁
  rw [he₀, he₁] at hw
  have heval := anglePairEvaluation_of_weakDerivative hw hg.continuous hp hz₀ θ
  calc
    |g θ| = ‖anglePairEvaluation (toIocMod Real.pi_pos 0 θ) (z j₀, z j₁)‖ := by
      rw [heval, Real.norm_eq_abs]
    _ ≤ anglePairEvaluationConstant * ‖(z j₀, z j₁)‖ := anglePairEvaluation_norm_le _ _
    _ ≤ anglePairEvaluationConstant * ‖z‖ := by
      apply mul_le_mul_of_nonneg_left _ anglePairEvaluationConstant_nonneg
      rw [Prod.norm_def]
      exact max_le (PiLp.norm_apply_le z j₀) (PiLp.norm_apply_le z j₁)

/-- A square summable scalar weight converts Hilbert row norms into a summable
sequence, with the expected Cauchy--Schwarz bound. -/
theorem spaces_circle_weighted_row_summable {T : MaterialData} {γ : ℝ}
    {f : ℕ → ℝ → ℝ} (hf : CircleMember T γ f) (s : ℕ)
    {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) (hws : Summable (fun m => w m ^ 2)) :
    Summable (fun m => w m * ‖circleJetEncodeHilbert hf s m‖) ∧
      (∑' m, w m * ‖circleJetEncodeHilbert hf s m‖) ≤
        Real.sqrt (∑' m, w m ^ 2) * circleNorm T γ s f := by
  have ha : Summable (fun m => w m ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using hws
  have hb : Summable (fun m => ‖circleJetEncodeHilbert hf s m‖ ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using circleJetHilbert_summable_sq (circleJetEncodeHilbert hf s)
  obtain ⟨hs, hbound⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two hw (fun m => norm_nonneg (circleJetEncodeHilbert hf s m)) ha hb
  refine ⟨hs, ?_⟩
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, ← circleJetHilbert_norm_sq] at hbound
  rw [Real.sqrt_sq (norm_nonneg _), circleJetEncodeHilbert_norm] at hbound
  exact hbound

end ContinuousFlexibility.Statements
