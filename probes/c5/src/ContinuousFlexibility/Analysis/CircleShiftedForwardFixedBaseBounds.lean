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
open Set Filter ContinuousFlexibility.Analysis
open scoped BigOperators Topology
private theorem circleShiftedForward_ordered_kernel
    {X Y Z : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]
    {U : Set X} {L : X → Y →L[ℝ] Z} (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (K : (n : ℕ) → X → (Fin n → X) → Y → Z)
    (hzero : ∀ e ∈ U, ∀ y, L e y = K 0 e Fin.elim0 y)
    (hstep : ∀ (n : ℕ) (e : X), e ∈ U →
      ∀ (h : X) (v : Fin n → X) (y : Y),
        HasProjectiveLineDerivAt (fun z => K n z v y)
          (K (n + 1) e (Fin.cons h v) y) e h) :
    ∀ (n : ℕ) (e : X), e ∈ U → ∀ (v : Fin n → X) (y : Y),
      inverseForwardJet J n e v y = K n e v y := by
  intro n
  induction n with
  | zero =>
    intro e he v y
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    subst v
    rw [inverseForwardJet_zero J he y]
    exact hzero e he y
  | succ n ih =>
    intro e he v y
    have hf := hasProjectiveLineDerivAt_inverseForwardJet
      (X := X) (Y := Y) (Z := Z) (U := U) (L := L) J he n (Fin.tail v) y (v 0)
    have hg : (fun z => K n z (Fin.tail v) y) =ᶠ[𝓝 e]
        (fun z => inverseForwardJet J n z (Fin.tail v) y) := by
      filter_upwards [hU.mem_nhds he] with z hz
      exact (ih z hz (Fin.tail v) y).symm
    have hs := (hf.congr_germ hg).unique (hstep n e he (v 0) (Fin.tail v) y)
    simpa only [Fin.cons_self_tail] using hs

private theorem circleShiftedForward_linear_unit_bound
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (A : E →L[ℝ] F) (q : Seminorm ℝ F) (low high : Seminorm ℝ E)
    {C a : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ u, low u < 1 → q (A u) ≤ C * (a + high u)) (y : E) :
    q (A y) ≤ C * (a * low y + high y) := by
  classical
  let B : E [×1]→L[ℝ] F :=
    ContinuousMultilinearMap.ofSubsingleton ℝ E F (0 : Fin 1) A
  have hB (w : Fin 1 → E) : B w = A (w 0) := by
    simp only [B, ContinuousMultilinearMap.ofSubsingleton_apply_apply]
  have hunit (w : Fin 1 → E) (hw : ∀ i, low (w i) < 1) :
      q (B w) ≤ C * (a + ∑ i, high (w i)) := by
    rw [hB]
    simpa only [Fin.sum_univ_one] using hlocal (w 0) (hw 0)
  have hbound := multilinear_bound_of_unitBall
    (E := E) (F := F) (k := 1) (C := C) (a := a) B q low high hC hunit
    (fun _ : Fin 1 => y)
  rw [hB] at hbound
  have he0 : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  simpa only [multilinearTameSize, Fin.prod_univ_one, Fin.sum_univ_one,
    he0, Finset.prod_empty, mul_one] using hbound

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
  exact circleShiftedForward_ordered_kernel
    (X := M.Space) (Y := M.Space) (Z := M.Space) (U := U)
    (L := circleShiftedChartComposeContinuousLinear hM hT hD hγ travel) hU J
    (fun k e v y => coupledCircleKernel hD hT hγ hM hI k k e
      (circleTranslationContinuousLinear hM hT hD hγ travel y) v)
    (fun e _ y => circleShiftedChartCompose_zero_kernel hD hT hγ hM hI travel e y)
    (fun k e _ h v y => coupledCircleKernel_hasProjectiveLineDerivAt hD hT hγ hM hI
      k k e h (circleTranslationContinuousLinear hM hT hD hγ travel y) v) n

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
  have hbound := circleShiftedForward_linear_unit_bound
    (E := M.Space) (F := M.Space)
    (inverseForwardJetLinear (X := M.Space) (Y := M.Space) (Z := M.Space)
      (U := U) (L := circleShiftedChartComposeContinuousLinear hM hT hD hγ travel) J n e v)
    (M.grading s) (M.grading base) (M.grading H)
    (C := C * P) (a := a) (mul_nonneg hC hP)
    (fun u hu => by simpa only [inverseForwardJetLinear_apply] using hlocal u hu) y
  simpa only [inverseForwardJetLinear_apply, a, H] using hbound

end ContinuousFlexibility.Statements
