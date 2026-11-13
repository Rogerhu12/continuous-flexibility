import ContinuousFlexibility.Analysis.CircleShiftedForwardFixedBaseBounds
import ContinuousFlexibility.Analysis.CircleCompositionSmoothDirections

/-!
# One low order for joint circle composition

The full joint jets of composition are the actual circle jets. Their
explicit formula is a finite sum of the existing composition kernels.
The common kernel base therefore works before every parameter order and
every travel selector. Multilinear normalization retains one high factor.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

local instance n04NegativeChartCompositionPairSMul (H : CircleModelData) :
    SMul ℝ (H.Space × H.Space) := Prod.instSMul

private theorem composition_seminorm_sum_bound
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (q : Seminorm ℝ E) (I : Finset ι) (v : ι → E) :
    q (∑ i ∈ I, v i) ≤ ∑ i ∈ I, q (v i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero, le_refl]
  | @insert i I hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add q (v i) _).trans (add_le_add le_rfl ih)

private theorem composition_majorant_on_low_ball
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (low high : Seminorm ℝ E) {n : ℕ} (v : Fin n → E)
    {a A R : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (haA : a ≤ A)
    (hR : 1 ≤ R) (hlow : ∀ i, low (v i) ≤ R)
    (hhigh : ∀ i, high (v i) ≤ A) :
    multilinearTameSize low high n a v ≤ ((n : ℝ) + 1) * R ^ n * A := by
  classical
  have hp (I : Finset (Fin n)) : (∏ i ∈ I, low (v i)) ≤ R ^ n := by
    have hcard : I.card ≤ n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ I)
    calc
      _ ≤ ∏ _i ∈ I, R := Finset.prod_le_prod₀
        (fun _ _ => apply_nonneg _ _) (fun i _ => hlow i)
      _ = R ^ I.card := by simp only [Finset.prod_const]
      _ ≤ R ^ n := pow_le_pow_right₀ hR hcard
  have hsum : (∑ i, high (v i) * ∏ j ∈ Finset.univ.erase i, low (v j)) ≤
      (n : ℝ) * (A * R ^ n) := by
    calc
      _ ≤ ∑ _i : Fin n, A * R ^ n := Finset.sum_le_sum (fun i _ =>
        mul_le_mul (hhigh i) (hp _) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) hA)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  exact (add_le_add
    (mul_le_mul haA (hp _) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) hA)
    hsum).trans_eq (by ring)

private theorem composition_prod_erase_succAbove {n : ℕ}
    (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (∏ j ∈ Finset.univ.erase i, f j) = ∏ j : Fin n, f (i.succAbove j) := by
  have h := Fin.prod_univ_succAbove (fun j => if j = i then (1 : ℝ) else f j) i
  rw [prod_single_replacement f i 1, one_mul] at h
  simpa only [ite_true, Fin.succAbove_ne, ite_false, one_mul] using h

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
  (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hI : HasInterpolation H.grading)

private def shiftedCompositionKernel (travel : ℕ → ℝ) (r k : ℕ)
    (e u : H.Space) (v : Fin k → H.Space) : H.Space :=
  coupledCircleKernel hD hT hγ hH hI r k e
    (circleTranslationContinuousLinear hH hT hD hγ travel u) v

private theorem shiftedCompositionKernel_decode (travel : ℕ → ℝ) (r k : ℕ)
    (e u : H.Space) (v : Fin k → H.Space) (m : ℕ) (θ : ℝ) :
    H.decode (shiftedCompositionKernel hH hT hD hγ hI travel r k e u v) m θ =
      iteratedDeriv r (H.decode u m) (θ + travel m + H.decode e m θ) *
        ∏ j, H.decode (v j) m θ := by
  have hk := coupledCircleKernel_decode_apply hD hT hγ hH hI r k e
    (circleTranslationContinuousLinear hH hT hD hγ travel u) v m θ
  have ht := congrFun
    (circleTranslationContinuousLinear_decode hH hT hD hγ travel u) m
  have hj :
      iteratedDeriv r
          (H.decode (circleTranslationContinuousLinear hH hT hD hγ travel u) m)
          (θ + H.decode e m θ) =
        iteratedDeriv r (H.decode u m) ((θ + H.decode e m θ) + travel m) := by
    rw [ht]
    exact congrFun (iteratedDeriv_comp_add_const r (H.decode u m) (travel m)) _
  have heq : (θ + H.decode e m θ) + travel m = θ + travel m + H.decode e m θ := by ring
  exact hk.trans (congrArg (fun a => a * ∏ j, H.decode (v j) m θ)
    (hj.trans (congrArg (iteratedDeriv r (H.decode u m)) heq)))

include hI in
private theorem fullCompositionJet_decode
    (travel : ℕ → ℝ) {U : Set (H.Space × H.Space)}
    (J : SmoothDirections U (fun x : H.Space × H.Space =>
      circleShiftedChartComposeContinuousLinear hH hT hD hγ travel x.1 x.2))
    (n : ℕ) (x : H.Space × H.Space) (hx : x ∈ U)
    (v : Fin n → H.Space × H.Space) :
    H.decode (J.D n x v) = circleChartCompositionJets hH travel n x v := by
  let data := exists_circleChartComposition_smoothDirections hH hT hD hγ hI travel
  let K := data.choose
  have he := congrArg (fun A : (H.Space × H.Space) [×n]→L[ℝ] H.Space => H.decode (A v))
    (J.unique (K.restrict J.open_domain (fun _ _ => mem_univ _)) n x hx)
  exact he.trans (data.choose_spec n x v)

private theorem fullCompositionJet_zero_kernel
    (travel : ℕ → ℝ) {U : Set (H.Space × H.Space)}
    (J : SmoothDirections U (fun x : H.Space × H.Space =>
      circleShiftedChartComposeContinuousLinear hH hT hD hγ travel x.1 x.2))
    (x : H.Space × H.Space) (hx : x ∈ U) (v : Fin 0 → H.Space × H.Space) :
    J.D 0 x v = shiftedCompositionKernel hH hT hD hγ hI travel 0 0 x.1 x.2 Fin.elim0 := by
  apply hH.2.2.2.2.2.1
  rw [fullCompositionJet_decode hH hT hD hγ hI travel J 0 x hx v]
  funext m θ
  simp only [circleChartCompositionJets_apply, shiftedCompositionKernel_decode,
    circleCompositionPhase, Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]

private theorem fullCompositionJet_succ_kernels
    (travel : ℕ → ℝ) {U : Set (H.Space × H.Space)}
    (J : SmoothDirections U (fun x : H.Space × H.Space =>
      circleShiftedChartComposeContinuousLinear hH hT hD hγ travel x.1 x.2))
    (n : ℕ) (x : H.Space × H.Space) (hx : x ∈ U)
    (v : Fin (n + 1) → H.Space × H.Space) :
    J.D (n + 1) x v =
      shiftedCompositionKernel hH hT hD hγ hI travel (n + 1) (n + 1) x.1 x.2
        (fun i => (v i).1) +
      ∑ i : Fin (n + 1), shiftedCompositionKernel hH hT hD hγ hI travel n n x.1
        (v i).2 (fun j => (v (i.succAbove j)).1) := by
  apply hH.2.2.2.2.2.1
  rw [fullCompositionJet_decode hH hT hD hγ hI travel J (n + 1) x hx v,
    map_add, map_sum]
  funext m θ
  simp only [Pi.add_apply, Pi.sum_apply, circleChartCompositionJets_apply,
    shiftedCompositionKernel_decode, circleCompositionPhase, Nat.add_sub_cancel]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (_ * ·) (composition_prod_erase_succAbove (fun j => H.decode (v j).1 m θ) i)

private theorem shiftedCompositionKernel_uniform_affine_bound :
    ∃ base loss : ℕ, ∀ r k s : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ travel e u v (A : ℝ), 0 ≤ A →
      H.grading base e ≤ R → H.grading base u ≤ R →
      (∀ i : Fin k, H.grading base (v i) ≤ R) →
      1 + H.grading (r + s + loss) e ≤ A →
      H.grading (r + s + loss) u ≤ A →
      (∀ i, H.grading (r + s + loss) (v i) ≤ A) →
      H.grading s (shiftedCompositionKernel hH hT hD hγ hI travel r k e u v) ≤ C * A := by
  let data := coupled_circle_kernel_grading_bounds hD hT hγ hH hI
  let base : ℕ := data.choose
  let loss : ℕ := data.choose_spec.choose
  refine ⟨base, loss, fun r k s R hR => ?_⟩
  let estimate := data.choose_spec.choose_spec r k s R hR
  let C : ℝ := estimate.choose
  have hC : 0 ≤ C := estimate.choose_spec.1
  refine ⟨C * (((k + 1 : ℕ) : ℝ) + 1) * R ^ (k + 1), by positivity,
    fun travel e u v A hA he hu hv hAe hAu hAv => ?_⟩
  let τ := circleTranslationContinuousLinear hH hT hD hγ travel
  have hlow (i : Fin (k + 1)) :
      H.grading base ((Fin.cons (τ u) v : Fin (k + 1) → H.Space) i) ≤ R := by
    refine Fin.cases ?_ hv i
    exact (circleTranslationContinuousLinear_grading_le hH hT hD hγ travel base u).trans hu
  have hhigh (i : Fin (k + 1)) :
      H.grading (r + s + loss) ((Fin.cons (τ u) v : Fin (k + 1) → H.Space) i) ≤ A := by
    refine Fin.cases ?_ hAv i
    exact (circleTranslationContinuousLinear_grading_le hH hT hD hγ travel
      (r + s + loss) u).trans hAu
  have hb := composition_majorant_on_low_ball (H.grading base)
    (H.grading (r + s + loss)) (Fin.cons (τ u) v)
    (by positivity) hA hAe hR hlow hhigh
  exact (estimate.choose_spec.2 e he (τ u) v).trans
    ((mul_le_mul_of_nonneg_left hb hC).trans_eq (by ring))

include hI in
/-- The base and the additive loss are chosen before every parameter
order, spatial order, travel selector and genuine tower. -/
theorem n04NegativeChart_circleComposition_fixedBase_oneHigh :
    ∃ base loss : ℕ, ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ travel : ℕ → ℝ,
      ∀ (U : Set (H.Space × H.Space))
        (J : SmoothDirections U (fun x : H.Space × H.Space =>
          circleShiftedChartComposeContinuousLinear hH hT hD hγ travel x.1 x.2)),
      ∀ x ∈ U, pairGrading H.grading H.grading base x ≤ R →
      ∀ v : Fin n → H.Space × H.Space,
        H.grading s (J.D n x v) ≤
          C * tameJetSize (pairGrading H.grading H.grading) n s (n + loss) base x v := by
  classical
  let data := shiftedCompositionKernel_uniform_affine_bound hH hT hD hγ hI
  let base : ℕ := data.choose
  let loss : ℕ := data.choose_spec.choose
  have hb := data.choose_spec.choose_spec
  let p := pairGrading H.grading H.grading
  refine ⟨base, loss, fun n R hR s => ?_⟩
  let R' : ℝ := max R 1
  have hR' : 1 ≤ R' := le_max_right _ _
  let main := hb n n s R' hR'
  let tail := hb (n - 1) (n - 1) s R' hR'
  let C : ℝ := main.choose + (n : ℝ) * tail.choose
  have hC : 0 ≤ C := add_nonneg main.choose_spec.1
    (mul_nonneg (Nat.cast_nonneg _) tail.choose_spec.1)
  refine ⟨C, hC, fun travel U J x hx hxR => ?_⟩
  apply multilinear_bound_of_unitBall (J.D n x) (H.grading s)
    (p base) (p (s + (n + loss))) hC
  intro v hv
  let A : ℝ := 1 + p (s + (n + loss)) x + ∑ i, p (s + (n + loss)) (v i)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he : H.grading base x.1 ≤ R' :=
    (circleGrading_fst_le_pair le_rfl x).trans (hxR.trans (le_max_left _ _))
  have hu : H.grading base x.2 ≤ R' :=
    (circleGrading_snd_le_pair le_rfl x).trans (hxR.trans (le_max_left _ _))
  have hv1 (i : Fin n) : H.grading base (v i).1 ≤ R' :=
    (circleGrading_fst_le_pair le_rfl (v i)).trans ((hv i).le.trans hR')
  have hv2 (i : Fin n) : H.grading base (v i).2 ≤ R' :=
    (circleGrading_snd_le_pair le_rfl (v i)).trans ((hv i).le.trans hR')
  have hAe {t : ℕ} (ht : t ≤ s + (n + loss)) : 1 + H.grading t x.1 ≤ A :=
    (add_le_add le_rfl (circleGrading_fst_le_pair ht x)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)))
  have hAu {t : ℕ} (ht : t ≤ s + (n + loss)) : H.grading t x.2 ≤ A :=
    (circleGrading_snd_le_pair ht x).trans ((le_add_of_nonneg_left zero_le_one).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))))
  have hAv (i : Fin n) {t : ℕ} (ht : t ≤ s + (n + loss)) :
      H.grading t (v i).1 ≤ A ∧ H.grading t (v i).2 ≤ A := by
    have hs : p (s + (n + loss)) (v i) ≤ A :=
      (Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left (by positivity))
    exact ⟨(circleGrading_fst_le_pair ht (v i)).trans hs,
      (circleGrading_snd_le_pair ht (v i)).trans hs⟩
  have hmain := main.choose_spec.2 travel x.1 x.2 (fun i => (v i).1) A hA
    he hu hv1 (hAe (by omega)) (hAu (by omega)) (fun i => (hAv i (by omega)).1)
  cases n with
  | zero =>
      rw [fullCompositionJet_zero_kernel hH hT hD hγ hI travel J x hx v]
      have hdirs : (fun i : Fin 0 => (v i).1) = Fin.elim0 := Subsingleton.elim _ _
      simpa only [C, Nat.cast_zero, zero_mul, add_zero, hdirs] using hmain
  | succ n =>
      have htail (i : Fin (n + 1)) :
          H.grading s (shiftedCompositionKernel hH hT hD hγ hI travel n n x.1
            (v i).2 (fun j => (v (i.succAbove j)).1)) ≤ tail.choose * A := by
        exact tail.choose_spec.2 travel x.1 (v i).2
          (fun j => (v (i.succAbove j)).1) A hA he (hv2 i)
          (fun j => hv1 (i.succAbove j)) (hAe (by omega))
          (hAv i (by omega)).2 (fun j => (hAv (i.succAbove j) (by omega)).1)
      rw [fullCompositionJet_succ_kernels hH hT hD hγ hI travel J n x hx v]
      apply (map_add_le_add (H.grading s) _ _).trans
      apply (add_le_add hmain ((composition_seminorm_sum_bound _ _ _).trans
        (Finset.sum_le_sum (fun i _ => htail i)))).trans_eq
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only [C]
      ring

/-- info: 'ContinuousFlexibility.Statements.n04NegativeChart_circleComposition_fixedBase_oneHigh'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n04NegativeChart_circleComposition_fixedBase_oneHigh

end ContinuousFlexibility.Statements
