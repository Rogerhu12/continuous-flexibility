module

public import ContinuousFlexibility.Analysis.N06WeightedHeight
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The three actual scalar columns in the relative operator

The scalar coordinates are projected from the already chosen graph inverse.
All three columns are retained, including the source-normalizing column:
its canonical pullback need not be independent of the current state.
The resulting finite-rank map acts on the original source space.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Synthesis of the left-height, mode, and source-normalizing columns. -/
def n06ScalarSynthesis (s k c : E) : (ℝ × ℝ × ℝ) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight s +
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight k +
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight c

theorem n06ScalarSynthesis_apply (s k c : E) (v : ℝ × ℝ × ℝ) :
    n06ScalarSynthesis s k c v = v.1 • s + v.2.1 • k + v.2.2 • c := by
  simp only [n06ScalarSynthesis, add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

theorem norm_n06ScalarSynthesis_le (s k c : E) :
    ‖n06ScalarSynthesis s k c‖ ≤ ‖s‖ + ‖k‖ + ‖c‖ := by
  have hf : ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.norm_fst_le ..
  have hg : ‖(ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))‖ ≤ 1 := by
    calc
      _ ≤ ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ *
          ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (ContinuousLinearMap.norm_fst_le ..)
        (ContinuousLinearMap.norm_snd_le ..) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hh : ‖(ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))‖ ≤ 1 := by
    calc
      _ ≤ ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ *
          ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (ContinuousLinearMap.norm_snd_le ..)
        (ContinuousLinearMap.norm_snd_le ..) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  unfold n06ScalarSynthesis
  calc
    _ ≤ ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight s‖ +
        ‖((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight k‖ +
        ‖((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight c‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 1 * ‖s‖ + 1 * ‖k‖ + 1 * ‖c‖ := by
      simp only [ContinuousLinearMap.norm_smulRight_apply]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hf (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hg (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
    _ = _ := by rw [one_mul, one_mul, one_mul]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

variable {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ}

/-- The scalar coordinates belong to the same inverse as the weighted height. -/
def n06InverseScalars (B : CanonicalDomainData S K V b) :
    V.level (3 / 4 : ℝ) 0 b →L[ℝ] (ℝ × ℝ × ℝ) :=
  (ContinuousLinearMap.snd ℝ (CanonicalL2Sequence S K) (ℝ × ℝ × ℝ)).comp
    ((ContinuousLinearMap.fst ℝ (CanonicalUnknown S K)
      (V.level (3 / 4 : ℝ) 0 b)).comp (B.graph.subtypeL.comp B.inverse))

theorem n06InverseScalars_apply (B : CanonicalDomainData S K V b)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    n06InverseScalars B F = (B.inverse F).val.1.2 := by
  simp only [n06InverseScalars, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Submodule.subtypeL_apply]

/-- The scalar contribution to the relative operator is an endomorphism
of the selected canonical source space. -/
def n06ScalarColumnOperator (B : CanonicalDomainData S K V b)
    (s k c : V.level (3 / 4 : ℝ) 0 b) :
    V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
  (n06ScalarSynthesis s k c).comp (n06InverseScalars B)

theorem n06ScalarColumnOperator_apply (B : CanonicalDomainData S K V b)
    (s k c F : V.level (3 / 4 : ℝ) 0 b) :
    n06ScalarColumnOperator B s k c F =
      (B.inverse F).val.1.2.1 • s + (B.inverse F).val.1.2.2.1 • k +
        (B.inverse F).val.1.2.2.2 • c := by
  change n06ScalarSynthesis s k c (n06InverseScalars B F) = _
  exact (congrArg (n06ScalarSynthesis s k c) (n06InverseScalars_apply B F)).trans
    (n06ScalarSynthesis_apply s k c ((B.inverse F).val.1.2))

theorem n06ScalarColumnOperator_forget (B : CanonicalDomainData S K V b)
    (s k c F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    V.forget (3 / 4 : ℝ) 0 b (n06ScalarColumnOperator B s k c F) m =
      (B.inverse F).val.1.2.1 • V.forget (3 / 4 : ℝ) 0 b s m +
      (B.inverse F).val.1.2.2.1 • V.forget (3 / 4 : ℝ) 0 b k m +
      (B.inverse F).val.1.2.2.2 • V.forget (3 / 4 : ℝ) 0 b c m := by
  have he := congrArg (fun Y : V.level (3 / 4 : ℝ) 0 b =>
    V.forget (3 / 4 : ℝ) 0 b Y m) (n06ScalarColumnOperator_apply B s k c F)
  apply he.trans
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply]

theorem norm_n06ScalarColumnOperator_le (B : CanonicalDomainData S K V b)
    (s k c : V.level (3 / 4 : ℝ) 0 b) :
    ‖n06ScalarColumnOperator B s k c‖ ≤
      (‖s‖ + ‖k‖ + ‖c‖) * ‖n06InverseScalars B‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_n06ScalarSynthesis_le s k c) (norm_nonneg _))

/-- Three small actual column differences give a small operator on the fixed
source space, with no derivative or material loss in its codomain. -/
theorem norm_n06ScalarColumnOperator_small (B : CanonicalDomainData S K V b)
    (s k c : V.level (3 / 4 : ℝ) 0 b) {δ : ℝ}
    (hs : ‖s‖ ≤ δ) (hk : ‖k‖ ≤ δ) (hc : ‖c‖ ≤ δ) :
    ‖n06ScalarColumnOperator B s k c‖ ≤ 3 * δ * ‖n06InverseScalars B‖ := by
  exact (norm_n06ScalarColumnOperator_le B s k c).trans
    (mul_le_mul_of_nonneg_right (by linarith only [hs, hk, hc])
      (norm_nonneg (n06InverseScalars B)))

end ContinuousFlexibility.Statements
