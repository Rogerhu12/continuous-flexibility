module

public import ContinuousFlexibility.Analysis.IntervalSobolevCutoffBounds
public import ContinuousFlexibility.Analysis.SmoothSobolevCore

/-!
# A fixed interval cutoff as a linear map of actual smooth Sobolev cores

The map acts on functions by multiplication with one fixed cutoff. Its domain
and codomain use actual within-derivatives and Lebesgue `L²` norms. No Sobolev
order occurs in the definition of the map.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

/-- The complementary cutoff seen from the other endpoint. -/
def intervalSobolevRightCutoff (L : ℝ) (hL : 0 < L) (x : ℝ) : ℝ :=
  1 - intervalSobolevCutoff L hL (L - x)

theorem contDiff_intervalSobolevRightCutoff (L : ℝ) (hL : 0 < L) :
    ContDiff ℝ ∞ (intervalSobolevRightCutoff L hL) :=
  contDiff_const.sub ((contDiff_intervalSobolevCutoff L hL).comp
    (contDiff_const.sub contDiff_id))

theorem intervalSobolevRightCutoff_one (L : ℝ) (hL : 0 < L) {x : ℝ}
    (hx : x ≤ L / 3) : intervalSobolevRightCutoff L hL x = 1 := by
  rw [intervalSobolevRightCutoff,
    intervalSobolevCutoff_zero L hL (show 2 * L / 3 ≤ L - x by linarith), sub_zero]

theorem intervalSobolevRightCutoff_zero (L : ℝ) (hL : 0 < L) {x : ℝ}
    (hx : 2 * L / 3 ≤ x) : intervalSobolevRightCutoff L hL x = 0 := by
  rw [intervalSobolevRightCutoff,
    intervalSobolevCutoff_one L hL (show L - x ≤ L / 3 by linarith), sub_self]

theorem intervalSobolevRightCutoff_range (L : ℝ) (hL : 0 < L) (x : ℝ) :
    intervalSobolevRightCutoff L hL x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := intervalSobolevCutoff_range L hL (L - x)
  exact ⟨sub_nonneg.mpr h1, sub_le_self _ h0⟩

theorem intervalSobolevRightCutoff_deriv_bounded (L : ℝ) (hL : 0 < L) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n (intervalSobolevRightCutoff L hL) x‖ ≤ C := by
  obtain ⟨M, hM0, hM⟩ := intervalSobolevCutoff_deriv_bounded L hL n
  have hc : ContDiff ℝ ∞ (fun x => intervalSobolevCutoff L hL (L - x)) :=
    (contDiff_intervalSobolevCutoff L hL).comp (contDiff_const.sub contDiff_id)
  refine ⟨1 + M, by linarith, fun x => ?_⟩
  have hconst : ‖iteratedDeriv n (fun _ : ℝ => (1 : ℝ)) x‖ ≤ 1 := by
    rw [iteratedDeriv_const]
    split_ifs <;> norm_num
  have hcomp : ‖iteratedDeriv n (fun y => intervalSobolevCutoff L hL (L - y)) x‖ ≤ M := by
    calc
      ‖iteratedDeriv n (fun y => intervalSobolevCutoff L hL (L - y)) x‖ =
          ‖(-1 : ℝ) ^ n • iteratedDeriv n (intervalSobolevCutoff L hL) (L - x)‖ :=
        congrArg norm (congrFun
          (iteratedDeriv_comp_const_sub n (intervalSobolevCutoff L hL) L) x)
      _ = ‖iteratedDeriv n (intervalSobolevCutoff L hL) (L - x)‖ := by
        rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      _ ≤ M := hM (L - x)
  have he : iteratedDeriv n (intervalSobolevRightCutoff L hL) x =
      iteratedDeriv n (fun _ : ℝ => (1 : ℝ)) x -
        iteratedDeriv n (fun y => intervalSobolevCutoff L hL (L - y)) x :=
    iteratedDeriv_fun_sub (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℝ => (1 : ℝ)) x)
      (hc.contDiffAt.of_le (by simp))
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hconst hcomp)

theorem intervalSobolevCutoff_partition (L : ℝ) (hL : 0 < L) (x : ℝ) :
    intervalSobolevCutoff L hL x + intervalSobolevRightCutoff L hL (L - x) = 1 := by
  simp only [intervalSobolevRightCutoff, sub_sub_cancel]
  ring

/-- Choose one bound for each derivative of a fixed cutoff. -/
def cutoffDerivativeBound {χ : ℝ → ℝ}
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (n : ℕ) : ℝ := (hbounded n).choose

theorem cutoffDerivativeBound_nonneg {χ : ℝ → ℝ}
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (n : ℕ) : 0 ≤ cutoffDerivativeBound hbounded n := (hbounded n).choose_spec.1

theorem norm_iteratedDeriv_le_cutoffDerivativeBound {χ : ℝ → ℝ}
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (n : ℕ) (x : ℝ) : ‖iteratedDeriv n χ x‖ ≤ cutoffDerivativeBound hbounded n :=
  (hbounded n).choose_spec.2 x

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual smooth Sobolev core on a nondegenerate closed interval. -/
abbrev IntervalSobolevCore (L : ℝ) (hL : 0 < L) : Submodule ℝ (ℝ → F) :=
  smoothSobolevCore F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL)

variable {F}

/-- One fixed cutoff map at all Sobolev orders. -/
def cutoffHalfLineCoreLinear {L c : ℝ} (hL : 0 < L) (hc : c < L)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C) :
    IntervalSobolevCore F L hL →ₗ[ℝ] HalfLineSobolevCore F where
  toFun f := ⟨cutoffHalfLine χ f,
    contDiffOn_cutoffHalfLine_of_vanishing hc hχ hzero f.property.1,
    fun n => memLp_cutoffHalfLine_jet hL hc hχ hzero f.property.1
      (cutoffDerivativeBound hbounded) (norm_iteratedDeriv_le_cutoffDerivativeBound hbounded)
      n 2 (by norm_num) (fun k _ => f.property.2 k)⟩
  map_add' f g := by
    apply Subtype.ext
    simpa only [Submodule.coe_add] using cutoffHalfLine_add χ (f : ℝ → F) (g : ℝ → F)
  map_smul' a f := by
    apply Subtype.ext
    simpa only [Submodule.coe_smul, RingHom.id_apply] using
      cutoffHalfLine_smul χ a (f : ℝ → F)

@[simp] theorem cutoffHalfLineCoreLinear_coe {L c : ℝ} (hL : 0 < L) (hc : c < L)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (f : IntervalSobolevCore F L hL) :
    (cutoffHalfLineCoreLinear hL hc hχ hzero hbounded f : ℝ → F) = cutoffHalfLine χ f := rfl

@[simp] theorem cutoffHalfLineCoreLinear_apply {L c : ℝ} (hL : 0 < L) (hc : c < L)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (f : IntervalSobolevCore F L hL) (x : ℝ) :
    cutoffHalfLineCoreLinear hL hc hχ hzero hbounded f x = χ x • f x := rfl

/-- The order-`n` coordinate bound in actual `L²` norms. -/
theorem cutoffHalfLineCoreLinear_jet_norm_le {L c : ℝ} (hL : 0 < L) (hc : c < L)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    (hbounded : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n χ x‖ ≤ C)
    (f : IntervalSobolevCore F L hL) (n : ℕ) :
    (eLpNorm (iteratedDerivWithin n
        (cutoffHalfLineCoreLinear hL hc hχ hzero hbounded f) (Ici 0)) 2
      (volume.restrict (Ici 0))).toReal ≤
      ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * cutoffDerivativeBound hbounded i) *
        (eLpNorm (iteratedDerivWithin (n - i) f (Icc 0 L)) 2
          (volume.restrict (Icc 0 L))).toReal := by
  rw [cutoffHalfLineCoreLinear_coe]
  exact cutoffHalfLine_jet_norm_le hL hc hχ hzero f.property.1
    (cutoffDerivativeBound hbounded) (norm_iteratedDeriv_le_cutoffDerivativeBound hbounded)
    n 2 (by norm_num) (fun k _ => f.property.2 k)

end ContinuousFlexibility.Analysis
