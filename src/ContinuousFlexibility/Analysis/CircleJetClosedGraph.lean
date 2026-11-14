module

public import ContinuousFlexibility.Statements.Analysis

@[expose] public section

open Set Filter MeasureTheory
open scoped ContDiff RealInnerProductSpace InnerProductSpace

namespace ContinuousFlexibility.Statements

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem memLp_angleMeasure_of_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) :
    MemLp φ 2 angleMeasure := by
  let : IsFiniteMeasure angleMeasure :=
    ⟨by
      rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      exact ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) Real.pi)).bddAbove_image hφ.norm.continuousOn
  refine MemLp.of_bound hφ.aestronglyMeasurable C ?_
  have ha : ∀ᵐ θ ∂angleMeasure, θ ∈ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [ha] with θ hθ
  exact hC ⟨θ, ⟨hθ.1.le, hθ.2⟩, rfl⟩

theorem memLp_angleMeasure_iteratedDeriv_of_contDiff {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (b : ℕ) : MemLp (iteratedDeriv b φ) 2 angleMeasure := by
  apply memLp_angleMeasure_of_continuous
  have h : ∀ n : ℕ, ContDiff ℝ ∞ (iteratedDeriv n φ) := by
    intro n
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hφ
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp ih).2
  exact (h b).continuous

/-- The real L² pairing with an angular test function. -/
def angleL2TestPairing (φ : ℝ → ℝ) (hφ : MemLp φ 2 angleMeasure) :
    AngleL2 →L[ℝ] ℝ :=
  innerSL ℝ (hφ.toLp φ)

theorem angleL2TestPairing_apply (φ : ℝ → ℝ) (hφ : MemLp φ 2 angleMeasure)
    (u : AngleL2) :
    angleL2TestPairing φ hφ u = ∫ θ, u θ * φ θ ∂angleMeasure := by
  change ⟪hφ.toLp φ, u⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hφ] with θ hθ
  rw [hθ]
  simp only [RCLike.inner_apply, conj_trivial]

/-- Evaluation in the actual outer lp and inner PiLp models. -/
def circleJetCoordinate (s m : ℕ) (j : CircleJetIndex s) :
    CircleJetHilbert s →L[ℝ] AngleL2 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : CircleJetIndex s => AngleL2) j).comp
    (lp.evalCLM ℝ (fun _ : ℕ => PiLp 2 (fun _ : CircleJetIndex s => AngleL2)) 2 m)

@[simp] theorem circleJetCoordinate_apply (s m : ℕ) (j : CircleJetIndex s)
    (z : CircleJetHilbert s) : circleJetCoordinate s m j z = z m j := rfl

def circleJetWeight (T : MaterialData) (m : ℕ) {s : ℕ} (j : CircleJetIndex s) : ℝ :=
  T.M (T.sample m) ^ (j.val 1).val

/-- Recover the unweighted weak derivative by scalar multiplication in L². -/
def circleJetNormalizedDerivative (T : MaterialData) (m : ℕ) {s : ℕ}
    (j : CircleJetIndex s) : CircleJetHilbert s →L[ℝ] AngleL2 :=
  (circleJetWeight T m j)⁻¹ • circleJetCoordinate s m j

@[simp] theorem circleJetNormalizedDerivative_apply (T : MaterialData) (m : ℕ) {s : ℕ}
    (j : CircleJetIndex s) (z : CircleJetHilbert s) :
    circleJetNormalizedDerivative T m j z = (circleJetWeight T m j)⁻¹ • z m j := rfl

theorem mem_circleJetGraph_iff_normalized {T : MaterialData} {s : ℕ}
    (hM : ∀ m, 0 < T.M (T.sample m)) (z : CircleJetHilbert s) :
    z ∈ circleJetGraph T s ↔ ∀ m j,
      HasWeakAngularDerivative (z m (zeroCircleJetIndex s))
        (circleJetNormalizedDerivative T m j z) (j.val 0).val := by
  constructor
  · intro hz m j
    obtain ⟨d, hd, hw⟩ := hz m j
    have hW : circleJetWeight T m j ≠ 0 := pow_ne_zero _ (hM m).ne'
    have he : d = (circleJetWeight T m j)⁻¹ • z m j := by
      apply Lp.ext
      filter_upwards [hw, Lp.coeFn_smul (circleJetWeight T m j)⁻¹ (z m j)] with θ hθ hsmul
      change z m j θ = circleJetWeight T m j * d θ at hθ
      rw [hsmul, Pi.smul_apply, smul_eq_mul, hθ, ← mul_assoc, inv_mul_cancel₀ hW, one_mul]
    rw [circleJetNormalizedDerivative_apply, ← he]
    exact hd
  · intro hz m j
    refine ⟨circleJetNormalizedDerivative T m j z, hz m j, ?_⟩
    have hW : circleJetWeight T m j ≠ 0 := pow_ne_zero _ (hM m).ne'
    rw [circleJetNormalizedDerivative_apply]
    filter_upwards [Lp.coeFn_smul (circleJetWeight T m j)⁻¹ (z m j)] with θ hθ
    change z m j θ = circleJetWeight T m j * ((circleJetWeight T m j)⁻¹ • z m j : AngleL2) θ
    rw [hθ, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hW, one_mul]

/-- The residual of one weak angular derivative test as a continuous linear functional. -/
def circleJetWeakTest (T : MaterialData) (m : ℕ) {s : ℕ} (j : CircleJetIndex s)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) : CircleJetHilbert s →L[ℝ] ℝ :=
  (angleL2TestPairing φ (memLp_angleMeasure_of_continuous hφ.continuous)).comp
      (circleJetNormalizedDerivative T m j) -
    ((-1 : ℝ) ^ (j.val 0).val) •
      ((angleL2TestPairing (iteratedDeriv (j.val 0).val φ)
        (memLp_angleMeasure_iteratedDeriv_of_contDiff hφ (j.val 0).val)).comp
          (circleJetCoordinate s m (zeroCircleJetIndex s)))

theorem circleJetWeakTest_apply (T : MaterialData) (m : ℕ) {s : ℕ}
    (j : CircleJetIndex s) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : CircleJetHilbert s) :
    circleJetWeakTest T m j φ hφ z =
      (∫ θ, circleJetNormalizedDerivative T m j z θ * φ θ ∂angleMeasure) -
        ((-1 : ℝ) ^ (j.val 0).val) *
          ∫ θ, z m (zeroCircleJetIndex s) θ * iteratedDeriv (j.val 0).val φ θ ∂angleMeasure := by
  change angleL2TestPairing φ _ (circleJetNormalizedDerivative T m j z) -
    ((-1 : ℝ) ^ (j.val 0).val) * angleL2TestPairing (iteratedDeriv (j.val 0).val φ) _
      (z m (zeroCircleJetIndex s)) = _
  rw [angleL2TestPairing_apply, angleL2TestPairing_apply]

theorem mem_circleJetGraph_iff_weakTests {T : MaterialData} {s : ℕ}
    (hM : ∀ m, 0 < T.M (T.sample m)) (z : CircleJetHilbert s) :
    z ∈ circleJetGraph T s ↔ ∀ m j φ (hφ : ContDiff ℝ ∞ φ),
      Function.Periodic φ Real.pi → circleJetWeakTest T m j φ hφ z = 0 := by
  rw [mem_circleJetGraph_iff_normalized hM z]
  constructor
  · intro hz m j φ hφ hp
    rw [circleJetWeakTest_apply, sub_eq_zero]
    exact hz m j φ hφ hp
  · intro hz m j φ hφ hp
    simpa only [circleJetWeakTest_apply, sub_eq_zero] using hz m j φ hφ hp

/-- Intersection of the kernels of all periodic weak angular tests. -/
def circleJetClosedSubmodule (T : MaterialData) (s : ℕ) : Submodule ℝ (CircleJetHilbert s) :=
  ⨅ m : ℕ, ⨅ j : CircleJetIndex s, ⨅ φ : ℝ → ℝ, ⨅ hφ : ContDiff ℝ ∞ φ,
    ⨅ _ : Function.Periodic φ Real.pi, (circleJetWeakTest T m j φ hφ).toLinearMap.ker

theorem circleJetClosedSubmodule_carrier {T : MaterialData} {s : ℕ}
    (hM : ∀ m, 0 < T.M (T.sample m)) :
    (circleJetClosedSubmodule T s : Set (CircleJetHilbert s)) = circleJetGraph T s := by
  ext z
  rw [mem_circleJetGraph_iff_weakTests hM z]
  simp only [SetLike.mem_coe, circleJetClosedSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

theorem isClosed_circleJetClosedSubmodule (T : MaterialData) (s : ℕ) :
    IsClosed (circleJetClosedSubmodule T s : Set (CircleJetHilbert s)) := by
  simp only [circleJetClosedSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun m => isClosed_iInter fun j => isClosed_iInter fun φ =>
    isClosed_iInter fun hφ => isClosed_iInter fun _ => (circleJetWeakTest T m j φ hφ).isClosed_ker

instance circleJetClosedSubmodule_completeSpace (T : MaterialData) (s : ℕ) :
    CompleteSpace (circleJetClosedSubmodule T s) :=
  (isClosed_circleJetClosedSubmodule T s).isComplete.completeSpace_coe

theorem isClosed_circleJetGraph {T : MaterialData} {s : ℕ}
    (hM : ∀ m, 0 < T.M (T.sample m)) : IsClosed (circleJetGraph T s) := by
  rw [← circleJetClosedSubmodule_carrier hM]
  exact isClosed_circleJetClosedSubmodule T s

end

end ContinuousFlexibility.Statements
