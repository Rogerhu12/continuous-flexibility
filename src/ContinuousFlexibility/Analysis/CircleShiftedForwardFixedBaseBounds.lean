import ContinuousFlexibility.Analysis.TameInverseExpressions
import ContinuousFlexibility.Analysis.CoupledCircleCompositionCurveDerivative
import ContinuousFlexibility.Analysis.CircleTranslationUniformBounds
import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Fixed low-base bounds for the actual shifted forward family

The ordered derivatives of the given genuine tower are the existing
composition kernels. Only the source is normalized; parameter increments
stay in one fixed low-seminorm ball. Translation costs no grading order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements
set_option backward.isDefEq.respectTransparency false
open Set Filter ContinuousFlexibility.Analysis
open scoped BigOperators Topology
set_option diagnostics true
local instance circleShiftedForwardFixedBasePairSMul (M : CircleModelData) :
    SMul ℝ (M.Space × M.Space) := Prod.instSMul

private theorem circleShiftedForward_scalar_sum {ι : Type*} [Fintype ι]
    (P a : ℝ) (f : ι → ℝ) :
    a * P + ∑ i, f i * P = P * (a + ∑ i, f i) := by
  rw [← Finset.sum_mul]; ring

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

private theorem circleShiftedChartCompose_zero_kernel
    (travel : ℕ → ℝ) (e y : M.Space) :
    circleShiftedChartComposeContinuousLinear hM hT hD hγ travel e y =
      coupledCircleKernel hD hT hγ hM hI 0 0 e
        (circleTranslationContinuousLinear hM hT hD hγ travel y) Fin.elim0 := by
  apply hM.2.2.2.2.2.1
  funext m θ
  have hc := circleShiftedChartComposeContinuousLinear_apply hM hT hD hγ travel e y
  have hl := circleShiftedChartComposeLinear_decode hM hT hD hγ travel e y m θ
  have ht := congrFun (congrFun
    (circleTranslationContinuousLinear_decode hM hT hD hγ travel y) m)
    (θ + M.decode e m θ)
  have hk := coupledCircleKernel_decode_apply hD hT hγ hM hI 0 0 e
    (circleTranslationContinuousLinear hM hT hD hγ travel y) Fin.elim0 m θ
  calc
    _ = M.decode (circleShiftedChartComposeLinear hM hT hD hγ travel e y) m θ :=
      congrArg (fun z : M.Space => M.decode z m θ) hc
    _ = M.decode y m (θ + travel m + M.decode e m θ) := hl
    _ = M.decode y m ((θ + M.decode e m θ) + travel m) :=
      congrArg (M.decode y m) (by ring)
    _ = M.decode (circleTranslationContinuousLinear hM hT hD hγ travel y) m
        (θ + M.decode e m θ) := ht.symm
    _ = _ := by
      simpa only [iteratedDeriv_zero, Fin.prod_univ_zero, mul_one] using hk.symm

/-- The existing ordered tower has the literal shifted kernel as its jet. -/
theorem circleShiftedChartCompose_orderedJet_eq_kernel
    (travel : ℕ → ℝ) {U : Set M.Space} (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ univ) (fun z : M.Space × M.Space =>
      circleShiftedChartComposeContinuousLinear hM hT hD hγ travel z.1 z.2))
    (n : ℕ) :
    ∀ e ∈ U, ∀ (v : Fin n → M.Space) (y : M.Space),
      inverseForwardJet J n e v y =
        coupledCircleKernel hD hT hγ hM hI n n e
          (circleTranslationContinuousLinear hM hT hD hγ travel y) v := by
  induction n with
  | zero =>
    intro e he v y
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    subst v
    rw [inverseForwardJet_zero J he y]
    exact circleShiftedChartCompose_zero_kernel hD hT hγ hM hI travel e y
  | succ n ih =>
    intro e he v y
    have hf : HasProjectiveLineDerivAt
        (fun z : M.Space => inverseForwardJet J n z (Fin.tail v) y)
        (inverseForwardJet J (n + 1) e (Fin.cons (v 0) (Fin.tail v)) y) e (v 0) := by
      have hd := J.derivative (n + 1) (e, (0 : M.Space)) ⟨he, mem_univ _⟩
        (Fin.snoc (fun i => (Fin.tail v i, (0 : M.Space))) ((0 : M.Space), y)) (v 0, (0 : M.Space))
      have hi : Fin.cons (v 0, (0 : M.Space))
          (Fin.snoc (fun i => (Fin.tail v i, (0 : M.Space))) ((0 : M.Space), y)) =
          Fin.snoc (α := fun _ : Fin (n + 2) => M.Space × M.Space) (fun i : Fin (n + 1) => (Fin.cons (α := fun _ : Fin (n + 1) => M.Space) (v 0) (Fin.tail v) i, (0 : M.Space)))
            ((0 : M.Space), y) := by
        rw [Fin.cons_snoc_eq_snoc_cons]; congr 1
        funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      simpa only [HasProjectiveLineDerivAt, inverseForwardJet,
        Prod.smul_mk, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
        smul_zero, add_zero, zero_add, hi] using hd
    have hk := coupledCircleKernel_hasProjectiveLineDerivAt hD hT hγ hM hI
      n n e (v 0) (circleTranslationContinuousLinear hM hT hD hγ travel y) (Fin.tail v)
    have hg : (fun z => coupledCircleKernel hD hT hγ hM hI n n z
        (circleTranslationContinuousLinear hM hT hD hγ travel y) (Fin.tail v)) =ᶠ[𝓝 e]
        (fun z => inverseForwardJet J n z (Fin.tail v) y) := by
      filter_upwards [hU.mem_nhds he] with z hz
      exact (ih z hz (Fin.tail v) y).symm
    have hsame : inverseForwardJet J (n + 1) e (Fin.cons (v 0) (Fin.tail v)) y = coupledCircleKernel hD hT hγ hM hI (n + 1) (n + 1) e (circleTranslationContinuousLinear hM hT hD hγ travel y) (Fin.cons (v 0) (Fin.tail v)) := HasProjectiveLineDerivAt.unique (V := M.Space) (F := M.Space) (HasProjectiveLineDerivAt.congr_germ (V := M.Space) (W := M.Space) hf hg) hk
    simpa only [Fin.cons_self_tail] using hsame

private theorem circleShiftedChartCompose_unit_majorant
    (base H n : ℕ) (R : ℝ) (hR : 1 ≤ R) (travel : ℕ → ℝ)
    (e : M.Space) (v : Fin n → M.Space) (hv : ∀ i, M.grading base (v i) ≤ R)
    (u : M.Space) (hu : M.grading base u < 1) :
    coupledCircleKernelMajorant M base H e
        (Fin.cons (circleTranslationContinuousLinear hM hT hD hγ travel u) v) ≤
      R ^ (n + 1) * ((1 + M.grading H e + ∑ i, M.grading H (v i)) + M.grading H u) := by
  classical
  let τ := circleTranslationContinuousLinear hM hT hD hγ travel
  let P := R ^ (n + 1)
  let a : ℝ := 1 + M.grading H e + ∑ i, M.grading H (v i)
  have hP : 0 ≤ P := pow_nonneg (zero_le_one.trans hR) _
  let w : Fin (n + 1) → M.Space := Fin.cons (τ u) v
  have hw (i : Fin (n + 1)) : M.grading base (w i) ≤ R := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (circleTranslationContinuousLinear_grading_le hM hT hD hγ travel base u).trans
        (hu.le.trans hR)
    · exact hv j
  have hp (I : Finset (Fin (n + 1))) : (∏ i ∈ I, M.grading base (w i)) ≤ P := by
    have hcard : I.card ≤ n + 1 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ I)
    calc
      _ ≤ ∏ _i ∈ I, R := Finset.prod_le_prod₀
        (fun i _ => apply_nonneg _ _) (fun i _ => hw i)
      _ = R ^ I.card := by simp only [Finset.prod_const]
      _ ≤ P := pow_le_pow_right₀ hR hcard
  have hsum : (∑ i, M.grading H (w i)) ≤
      M.grading H u + ∑ i, M.grading H (v i) := by
    simpa only [w, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
      add_le_add (circleTranslationContinuousLinear_grading_le hM hT hD hγ travel H u)
        (le_refl (∑ i, M.grading H (v i)))
  have hmajor : coupledCircleKernelMajorant M base H e w ≤ P * (a + M.grading H u) := by
    unfold coupledCircleKernelMajorant
    calc
      _ ≤ (1 + M.grading H e) * P + ∑ i, M.grading H (w i) * P :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hp Finset.univ)
            (add_nonneg zero_le_one (apply_nonneg _ _)))
          (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
            (hp (Finset.univ.erase i)) (apply_nonneg _ _)))
      _ = P * (1 + M.grading H e + ∑ i, M.grading H (w i)) :=
        circleShiftedForward_scalar_sum P (1 + M.grading H e) (fun i : Fin (n + 1) => M.grading H (w i))
      _ ≤ P * (1 + M.grading H e +
          (M.grading H u + ∑ i, M.grading H (v i))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hP
      _ = P * (a + M.grading H u) :=
        congrArg (fun t : ℝ => P * t) ((add_assoc (1 + M.grading H e) (M.grading H u) (∑ i, M.grading H (v i))).symm.trans (add_right_comm (1 + M.grading H e) (M.grading H u) (∑ i, M.grading H (v i))))
  exact hmajor

include hI in
/-- One base and loss precede every parameter order, spatial order and
travel. The source remains linear and the old tower is unchanged. -/
theorem circleShiftedChartCompose_orderedJets_fixedBase_bound :
    ∃ base loss : ℕ, ∀ (n : ℕ) (R : ℝ), 1 ≤ R →
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ (travel : ℕ → ℝ) (U : Set M.Space) (hU : IsOpen U)
          (J : SmoothDirections (U ×ˢ univ) (fun z : M.Space × M.Space =>
            circleShiftedChartComposeContinuousLinear hM hT hD hγ travel z.1 z.2)),
          ∀ e ∈ U, M.grading base e ≤ R → ∀ v : Fin n → M.Space,
            (∀ i, M.grading base (v i) ≤ R) → ∀ y : M.Space,
              M.grading s (inverseForwardJet J n e v y) ≤ C *
                ((1 + M.grading (s + (n + loss)) e +
                    ∑ i, M.grading (s + (n + loss)) (v i)) * M.grading base y +
                  M.grading (s + (n + loss)) y) := by
  classical
  let kernelBounds := coupled_circle_kernel_grading_bounds
    (D := D) (T := T) (γ := γ) (M := M) hD hT hγ hM hI
  let base : ℕ := kernelBounds.choose
  let loss : ℕ := kernelBounds.choose_spec.choose
  have hkernel : ∀ (r k s : ℕ) (R : ℝ), 1 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : M.Space, M.grading base ψ ≤ R →
        ∀ (u : M.Space) (w : Fin k → M.Space),
          M.grading s (coupledCircleKernel hD hT hγ hM hI r k ψ u w) ≤
            C * coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons u w) :=
    kernelBounds.choose_spec.choose_spec
  refine ⟨base, loss, fun n R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hkernel n n s R hR
  have horder : n + s + loss = s + (n + loss) := by omega
  rw [horder] at hc
  let H := s + (n + loss)
  let P := R ^ (n + 1)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hP : 0 ≤ P := pow_nonneg hR0 _
  refine ⟨C * P, mul_nonneg hC hP, fun travel U hU J e he heR v hv y => ?_⟩
  let τ := circleTranslationContinuousLinear hM hT hD hγ travel
  let a : ℝ := 1 + M.grading H e + ∑ i, M.grading H (v i)
  have hlocal (u : M.Space) (hu : M.grading base u < 1) :
      M.grading s (inverseForwardJet J n e v u) ≤ C * P * (a + M.grading H u) := by
    have hmajor : coupledCircleKernelMajorant M base H e (Fin.cons (τ u) v) ≤
        P * (a + M.grading H u) :=
      circleShiftedChartCompose_unit_majorant hD hT hγ hM base H n R hR travel e v hv u hu
    rw [circleShiftedChartCompose_orderedJet_eq_kernel hD hT hγ hM hI travel hU J n e he v u]
    exact (hc e heR (τ u) v).trans
      ((mul_le_mul_of_nonneg_left hmajor hC).trans_eq (mul_assoc C P _).symm)
  let A : M.Space [×1]→L[ℝ] M.Space :=
    ContinuousMultilinearMap.ofSubsingleton ℝ M.Space M.Space (0 : Fin 1)
      (inverseForwardJetLinear J n e v)
  have hA (w : Fin 1 → M.Space) : A w = inverseForwardJet J n e v (w 0) := by
    simpa only [A, ContinuousMultilinearMap.ofSubsingleton_apply_apply] using
      inverseForwardJetLinear_apply J n e v (w 0)
  have hunit (w : Fin 1 → M.Space) (hw : ∀ i, M.grading base (w i) < 1) :
      M.grading s (A w) ≤ C * P * (a + ∑ i, M.grading H (w i)) := by
    rw [hA]
    simpa only [Fin.sum_univ_one] using hlocal (w 0) (hw 0)
  have hbound : M.grading s (A (fun _ : Fin 1 => y)) ≤ (C * P) * multilinearTameSize (M.grading base) (M.grading H) 1 a (fun _ : Fin 1 => y) :=
    multilinear_bound_of_unitBall (E := M.Space) (F := M.Space) (k := 1) (C := C * P) (a := a) A (M.grading s) (M.grading base) (M.grading H) (mul_nonneg hC hP) hunit (fun _ : Fin 1 => y)
  rw [hA] at hbound
  have he0 : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  simpa only [multilinearTameSize, Fin.prod_univ_one, Fin.sum_univ_one,
    he0, Finset.prod_empty, mul_one, a, H] using hbound

end ContinuousFlexibility.Statements
