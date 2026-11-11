import ContinuousFlexibility.Statements.Analysis
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Exponential shell analysis and synthesis

This file supplies the sequence-space part of the Fourier construction in
Lemma 7.4.  A family of linear shell coefficients satisfying uniform
exponential estimates gives an actual continuous tame analysis map.  Compatible
Banach-level synthesis operators with exponential growth give an actual
continuous tame synthesis map, with one extra order for summing the shells.
The reconstruction identity then gives a genuine tame retraction.

The shell operators and their estimates are hypotheses of this general lemma;
their construction for the physical and circle spaces is a separate Fourier
analysis obligation.  No assertion of tameness of those spaces is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ENNReal BigOperators
open ContinuousFlexibility.Statements

/-! ## The concrete model already has smoothing operators -/

theorem hasSmoothing_exponentialSequence (B : Type*)
    [NormedAddCommGroup B] [NormedSpace ℝ B] :
    HasSmoothing (exponentialSequenceSeminorm B) := by
  refine ⟨0, 0, exponentialSequenceSmoothing B, ?_, ?_,
    tendsto_exponentialSequenceSmoothing B⟩
  · intro m n _ hmn
    refine ⟨1, zero_le_one, fun N u => ?_⟩
    simpa only [Nat.cast_zero, add_zero, one_mul] using
      exponentialSequenceSmoothing_forward B hmn N u
  · intro m n _ hmn
    refine ⟨1, zero_le_one, fun N u => ?_⟩
    simpa only [Nat.cast_zero, sub_zero, one_mul, neg_mul] using
      exponentialSequenceSmoothing_tail B hmn N u

theorem hasSmoothing_modelGrading : HasSmoothing modelGrading :=
  hasSmoothing_exponentialSequence PhysicalModelBanach

/-! ## Analysis: uniformly bounded weighted shell coefficients -/

section Analysis

variable {X B : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

variable (p : ℕ → Seminorm ℝ X) (loss : ℕ)
  (A : ℕ → X →ₗ[ℝ] B) (C : ℕ → ℝ≥0)
  (hA : ∀ s k x,
    ‖Real.exp ((s : ℝ) * k) • A k x‖ ≤ C s * p (s + loss) x)

private theorem shellAnalysis_mem (x : X) (s : ℕ) :
    Memℓp (fun k : ℕ => Real.exp ((s : ℝ) * k) • A k x) ∞ := by
  apply memℓp_infty
  refine ⟨C s * p (s + loss) x, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact hA s k x

/-- The analysis map is constructed from the original coefficients, rather
than being postulated as a map into the rapid sequence space. -/
def shellAnalysisLinear : X →ₗ[ℝ] ExponentialSequenceSpace B where
  toFun := fun x => exponentialSequenceOfRaw B (fun k => A k x)
    (shellAnalysis_mem p loss A C hA x)
  map_add' := by
    intro x y
    apply Subtype.ext
    funext s
    apply lp.ext
    funext k
    simp only [exponentialSequenceOfRaw, Submodule.coe_add, Pi.add_apply,
      lp.coeFn_add, map_add, smul_add]
  map_smul' := by
    intro c x
    apply Subtype.ext
    funext s
    apply lp.ext
    funext k
    simp only [exponentialSequenceOfRaw, Submodule.coe_smul, Pi.smul_apply,
      lp.coeFn_smul, map_smul, RingHom.id_apply]
    exact smul_comm _ _ _

theorem shellAnalysisLinear_raw (x : X) :
    exponentialSequenceRaw B (shellAnalysisLinear p loss A C hA x) =
      fun k => A k x :=
  exponentialSequenceRaw_ofRaw B _ _

theorem shellAnalysisLinear_bound (s : ℕ) (x : X) :
    exponentialSequenceSeminorm B s (shellAnalysisLinear p loss A C hA x) ≤
      C s * p (s + loss) x := by
  rw [exponentialSequenceSeminorm_apply]
  apply lp.norm_le_of_forall_le (mul_nonneg (C s).property (apply_nonneg _ _))
  intro k
  exact hA s k x

theorem shellAnalysisLinear_isTame :
    IsTameLinear p (exponentialSequenceSeminorm B)
      (shellAnalysisLinear p loss A C hA) loss 0 := by
  intro s _
  exact ⟨C s, shellAnalysisLinear_bound p loss A C hA s⟩

/-- The same analysis map, with continuity proved from its shell estimate. -/
def shellAnalysisMap (hp : WithSeminorms p) :
    X →L[ℝ] ExponentialSequenceSpace B :=
  (shellAnalysisLinear_isTame p loss A C hA).toContinuousLinearMap hp
    (withSeminorms_exponentialSequence B) (exponentialSequenceSeminorm_monotone B)

theorem shellAnalysisMap_raw (hp : WithSeminorms p) (x : X) :
    exponentialSequenceRaw B (shellAnalysisMap p loss A C hA hp x) =
      fun k => A k x :=
  shellAnalysisLinear_raw p loss A C hA x

theorem shellAnalysisMap_isTame (hp : WithSeminorms p) :
    IsTameLinear p (exponentialSequenceSeminorm B)
      (shellAnalysisMap p loss A C hA hp).toLinearMap loss 0 :=
  shellAnalysisLinear_isTame p loss A C hA

end Analysis

/-! ## A convergent operator series on a bounded sequence space -/

private theorem summable_shellDecay : Summable (fun k : ℕ => Real.exp (-(k : ℝ))) := by
  simpa only [mul_neg_one] using
    (Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-1 : ℝ) < 0))

/-- The fixed finite constant introduced by summing one extra exponential order. -/
def shellSummationConstant : ℝ≥0 :=
  ⟨∑' k : ℕ, Real.exp (-(k : ℝ)), tsum_nonneg (fun k => (Real.exp_pos _).le)⟩

section BanachSynthesis

variable {B F : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

variable (A : ℕ → B →L[ℝ] F) (C : ℝ≥0)
  (hA : ∀ k b, ‖A k b‖ ≤ C * Real.exp (-(k : ℝ)) * ‖b‖)

private theorem decayingSeries_term_bound (u : ExponentialSequenceLevel B) (k : ℕ) :
    ‖A k (u k)‖ ≤ (C * ‖u‖) * Real.exp (-(k : ℝ)) := by
  calc
    ‖A k (u k)‖ ≤ C * Real.exp (-(k : ℝ)) * ‖u k‖ := hA k (u k)
    _ ≤ C * Real.exp (-(k : ℝ)) * ‖u‖ :=
      mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) u k)
        (mul_nonneg C.property (Real.exp_pos _).le)
    _ = _ := by ring

theorem summable_decayingSeries (u : ExponentialSequenceLevel B) :
    Summable (fun k : ℕ => A k (u k)) :=
  (summable_shellDecay.mul_left (C * ‖u‖)).of_norm_bounded
    (decayingSeries_term_bound A C hA u)

theorem norm_decayingSeries_le (u : ExponentialSequenceLevel B) :
    ‖∑' k : ℕ, A k (u k)‖ ≤ (C * shellSummationConstant : ℝ≥0) * ‖u‖ := by
  have h := tsum_of_norm_bounded
    (summable_shellDecay.hasSum.mul_left (C * ‖u‖))
    (decayingSeries_term_bound A C hA u)
  simpa only [NNReal.coe_mul, shellSummationConstant,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Synthesis on one Banach level is an actual convergent series of operators. -/
def decayingSeriesMap : ExponentialSequenceLevel B →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun u => ∑' k : ℕ, A k (u k)
      map_add' := by
        intro u v
        simp only [lp.coeFn_add, Pi.add_apply, map_add]
        exact (summable_decayingSeries A C hA u).tsum_add
          (summable_decayingSeries A C hA v)
      map_smul' := by
        intro c u
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
        exact (summable_decayingSeries A C hA u).tsum_const_smul c }
    (C * shellSummationConstant : ℝ≥0) (norm_decayingSeries_le A C hA)

theorem decayingSeriesMap_apply (u : ExponentialSequenceLevel B) :
    decayingSeriesMap A C hA u = ∑' k : ℕ, A k (u k) :=
  LinearMap.mkContinuous_apply _ _ _ _

theorem decayingSeriesMap_bound (u : ExponentialSequenceLevel B) :
    ‖decayingSeriesMap A C hA u‖ ≤ (C * shellSummationConstant : ℝ≥0) * ‖u‖ :=
  norm_decayingSeries_le A C hA u

end BanachSynthesis

/-! ## Compatible synthesis into a projective Banach scale -/

section Synthesis

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, CompleteSpace (E n)] (bond : ∀ n, E (n + 1) →L[ℝ] E n)

variable (loss : ℕ) (P : ∀ n, ℕ → B →L[ℝ] E n) (C : ℕ → ℝ≥0)
  (hP : ∀ n k b,
    ‖P n k b‖ ≤ C n * Real.exp (((n + loss : ℕ) : ℝ) * k) * ‖b‖)

private def scaledShell (n k : ℕ) : B →L[ℝ] E n :=
  Real.exp (-(((n + loss + 1 : ℕ) : ℝ) * k)) • P n k

private theorem scaledShell_apply (n k : ℕ) (b : B) :
    scaledShell E loss P n k b =
      Real.exp (-(((n + loss + 1 : ℕ) : ℝ) * k)) • P n k b :=
  smul_apply _ _ _

private theorem scaledShell_bound (n k : ℕ) (b : B) :
    ‖scaledShell E loss P n k b‖ ≤ C n * Real.exp (-(k : ℝ)) * ‖b‖ := by
  rw [scaledShell_apply, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    Real.exp (-(((n + loss + 1 : ℕ) : ℝ) * k)) * ‖P n k b‖ ≤
        Real.exp (-(((n + loss + 1 : ℕ) : ℝ) * k)) *
          (C n * Real.exp (((n + loss : ℕ) : ℝ) * k) * ‖b‖) :=
      mul_le_mul_of_nonneg_left (hP n k b) (Real.exp_pos _).le
    _ = C n * Real.exp (-(k : ℝ)) * ‖b‖ := by
      have he : Real.exp (-(((n + loss + 1 : ℕ) : ℝ) * k)) *
          Real.exp (((n + loss : ℕ) : ℝ) * k) = Real.exp (-(k : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      calc
        _ = C n * (Real.exp (-(((n + loss + 1 : ℕ) : ℝ) * k)) *
          Real.exp (((n + loss : ℕ) : ℝ) * k)) * ‖b‖ := by ring
        _ = _ := by rw [he]

private theorem scaledShell_level (u : ExponentialSequenceSpace B) (n k : ℕ) :
    scaledShell E loss P n k (u.val (n + loss + 1) k) =
      P n k (exponentialSequenceRaw B u k) := by
  rw [scaledShell_apply, exponentialSequence_level_eq_weighted_raw, map_smul,
    smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

/-- One coordinate of synthesis. Its input is one higher exponential order
than the growth order of the shell operators. -/
def shellSynthesisLevel (n : ℕ) : ExponentialSequenceSpace B →L[ℝ] E n :=
  (decayingSeriesMap (scaledShell E loss P n) (C n)
    (scaledShell_bound E loss P C hP n)).comp
      (projectiveCoordinate (fun _ => ExponentialSequenceLevel B)
        (exponentialSequenceBond B) (n + loss + 1))

theorem shellSynthesisLevel_apply (u : ExponentialSequenceSpace B) (n : ℕ) :
    shellSynthesisLevel E loss P C hP n u =
      ∑' k : ℕ, P n k (exponentialSequenceRaw B u k) := by
  rw [shellSynthesisLevel, ContinuousLinearMap.comp_apply, decayingSeriesMap_apply,
    projectiveCoordinate_apply]
  exact tsum_congr (scaledShell_level E loss P u n)

theorem summable_shellSynthesis (u : ExponentialSequenceSpace B) (n : ℕ) :
    Summable (fun k : ℕ => P n k (exponentialSequenceRaw B u k)) := by
  have h := summable_decayingSeries (scaledShell E loss P n) (C n)
    (scaledShell_bound E loss P C hP n) (u.val (n + loss + 1))
  exact h.congr (scaledShell_level E loss P u n)

theorem shellSynthesisLevel_bound (u : ExponentialSequenceSpace B) (n : ℕ) :
    ‖shellSynthesisLevel E loss P C hP n u‖ ≤
      (C n * shellSummationConstant : ℝ≥0) *
        exponentialSequenceSeminorm B (n + loss + 1) u :=
  decayingSeriesMap_bound (scaledShell E loss P n) (C n)
    (scaledShell_bound E loss P C hP n) (u.val (n + loss + 1))

variable (hcompat : ∀ n k b, bond n (P (n + 1) k b) = P n k b)

theorem shellSynthesisLevel_compatible (n : ℕ) :
    (bond n).comp (shellSynthesisLevel E loss P C hP (n + 1)) =
      shellSynthesisLevel E loss P C hP n := by
  ext u
  rw [ContinuousLinearMap.comp_apply, shellSynthesisLevel_apply,
    shellSynthesisLevel_apply, (bond n).map_tsum (summable_shellSynthesis E loss P C hP u (n + 1))]
  exact tsum_congr (fun k => hcompat n k _)

/-- The synthesis map lands in the actual compatible projective limit. -/
def shellSynthesis : ExponentialSequenceSpace B →L[ℝ] ProjectiveLimit E bond :=
  projectiveLift E bond (shellSynthesisLevel E loss P C hP)
    (shellSynthesisLevel_compatible E bond loss P C hP hcompat)

theorem shellSynthesis_apply (u : ExponentialSequenceSpace B) (n : ℕ) :
    (shellSynthesis E bond loss P C hP hcompat u).val n =
      ∑' k : ℕ, P n k (exponentialSequenceRaw B u k) :=
  shellSynthesisLevel_apply E loss P C hP u n

theorem shellSynthesis_isTame :
    IsTameLinear (exponentialSequenceSeminorm B) (gradedSeminorm E bond)
      (shellSynthesis E bond loss P C hP hcompat).toLinearMap (loss + 1) 0 := by
  intro s _
  refine ⟨(Finset.Iic s).sum C * shellSummationConstant, fun u => ?_⟩
  apply (gradedSeminorm_le_iff E bond s _ (by positivity)).mpr
  intro i hi
  have hCi : C i ≤ (Finset.Iic s).sum C :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_Iic.mpr hi)
  have hq : exponentialSequenceSeminorm B (i + loss + 1) u ≤
      exponentialSequenceSeminorm B (s + (loss + 1)) u :=
    exponentialSequenceSeminorm_monotone B (by omega) u
  have hb := shellSynthesisLevel_bound E loss P C hP u i
  calc
    ‖(shellSynthesis E bond loss P C hP hcompat u).val i‖ ≤
        (C i * shellSummationConstant : ℝ≥0) *
          exponentialSequenceSeminorm B (i + loss + 1) u := hb
    _ ≤ ((Finset.Iic s).sum C * shellSummationConstant : ℝ≥0) *
        exponentialSequenceSeminorm B (s + (loss + 1)) u := by
      exact mul_le_mul (by exact_mod_cast mul_le_mul_right' hCi shellSummationConstant)
        hq (apply_nonneg _ _) (NNReal.coe_nonneg _)

end Synthesis

/-! ## Reconstruction gives an actual tame retraction -/

theorem tameRetraction_of_shells
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, CompleteSpace (E n)] (bond : ∀ n, E (n + 1) →L[ℝ] E n)
    (analysisLoss synthesisLoss : ℕ)
    (A : ℕ → ProjectiveLimit E bond →ₗ[ℝ] B) (CA : ℕ → ℝ≥0)
    (hA : ∀ s k x, ‖Real.exp ((s : ℝ) * k) • A k x‖ ≤
      CA s * gradedSeminorm E bond (s + analysisLoss) x)
    (P : ∀ n, ℕ → B →L[ℝ] E n) (CP : ℕ → ℝ≥0)
    (hP : ∀ n k b, ‖P n k b‖ ≤
      CP n * Real.exp (((n + synthesisLoss : ℕ) : ℝ) * k) * ‖b‖)
    (hcompat : ∀ n k b, bond n (P (n + 1) k b) = P n k b)
    (hreconstruct : ∀ x n, HasSum (fun k : ℕ => P n k (A k x)) (x.val n)) :
    TameRetraction (gradedSeminorm E bond) (exponentialSequenceSeminorm B) := by
  let J := shellAnalysisMap (gradedSeminorm E bond) analysisLoss A CA hA
    (withSeminorms_graded E bond)
  let Q := shellSynthesis E bond synthesisLoss P CP hP hcompat
  refine ⟨J, Q, ?_, ⟨analysisLoss, 0, ?_⟩, ⟨synthesisLoss + 1, 0, ?_⟩⟩
  · intro x
    apply Subtype.ext
    funext n
    rw [shellSynthesis_apply, shellAnalysisMap_raw]
    exact (hreconstruct x n).tsum_eq
  · exact shellAnalysisMap_isTame (gradedSeminorm E bond) analysisLoss A CA hA
      (withSeminorms_graded E bond)
  · exact shellSynthesis_isTame E bond synthesisLoss P CP hP hcompat

end ContinuousFlexibility.Analysis
