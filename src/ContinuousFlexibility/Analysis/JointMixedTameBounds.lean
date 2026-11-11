import ContinuousFlexibility.Analysis.MixedJointTameBounds
import ContinuousFlexibility.Analysis.PhysicalJetLinearity

/-!
# Recovering the mixed one-high bounds from the actual joint tower

Spatial derivatives fix unit spatial directions in genuine joint jets.
Their parameter components vanish, so they add no high parameter
factor. At fixed parameter arity `n`, a joint loss `L` therefore gives
the mixed loss `n + L`. Algebraic multilinearity of the actual mixed
derivative then removes the unit-direction restriction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}

private theorem fixedSpatial_unit_bound
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (low high : Seminorm ℝ E) (x : E) (p e : PolarPoint) (he : ‖e‖ ≤ 1)
    (n : ℕ) (C H : ℝ)
    (hbound : ∀ v : Fin (n + 1) → E × PolarPoint,
      (∀ i, low (v i).1 + ‖(v i).2‖ ≤ 1) →
      |J.D (n + 1) (x, p) v| ≤ C * (H + ∑ i : Fin (n + 1), high (v i).1))
    (v : Fin n → E × PolarPoint) (hv : ∀ i, low (v i).1 + ‖(v i).2‖ ≤ 1) :
    |(J.fixedLast (0, e)).D n (x, p) v| ≤ C * (H + ∑ i : Fin n, high (v i).1) := by
  have hl0 : low (0 : E) = 0 := low.map_zero'
  have hh0 : high (0 : E) = 0 := high.map_zero'
  have hs (i : Fin (n + 1)) :
      low (Fin.snoc (α := fun _ : Fin (n + 1) => E × PolarPoint) v ((0 : E), e) i).1 +
        ‖(Fin.snoc (α := fun _ : Fin (n + 1) => E × PolarPoint) v ((0 : E), e) i).2‖ ≤ 1 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last, hl0, zero_add] using he
    · simpa only [Fin.snoc_castSucc] using hv j
  have hb := hbound
    (Fin.snoc (α := fun _ : Fin (n + 1) => E × PolarPoint) v ((0 : E), e)) hs
  rw [J.fixedLast_apply]
  simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    hh0, add_zero] using hb

private theorem mixedJet_unit_bound_aux
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (low high : Seminorm ℝ E) (x : E) (hx : x ∈ U)
    (p : PolarPoint) (hp : p ∈ V) :
    ∀ s a b : ℕ, a + b ≤ s → ∀ n : ℕ, ∀ f : E × PolarPoint → ℝ,
    ∀ J : SmoothDirections (U ×ˢ V) f, ∀ C H : ℝ,
      (∀ v : Fin (n + a + b) → E × PolarPoint,
        (∀ i, low (v i).1 + ‖(v i).2‖ ≤ 1) →
        |J.D (n + a + b) (x, p) v| ≤ C * (H + ∑ i : Fin (n + a + b), high (v i).1)) →
      ∀ u : Fin n → E, (∀ i, low (u i) ≤ 1) →
        |mixedDerivative a b (fun q => J.D n (x, q) (fun i => (u i, 0))) p| ≤
          C * (H + ∑ i : Fin n, high (u i)) := by
  have hzero (n : ℕ) (f : E × PolarPoint → ℝ) (J : SmoothDirections (U ×ˢ V) f)
      (C H : ℝ)
      (hbound : ∀ v : Fin n → E × PolarPoint,
        (∀ i, low (v i).1 + ‖(v i).2‖ ≤ 1) →
        |J.D n (x, p) v| ≤ C * (H + ∑ i : Fin n, high (v i).1))
      (u : Fin n → E) (hu : ∀ i, low (u i) ≤ 1) :
      |mixedDerivative 0 0 (fun q => J.D n (x, q) (fun i => (u i, 0))) p| ≤
        C * (H + ∑ i : Fin n, high (u i)) := by
    have hv (i : Fin n) : low (u i) + ‖(0 : PolarPoint)‖ ≤ 1 := by
      simpa only [norm_zero, add_zero] using hu i
    simpa only [mixedDerivative, iteratedDeriv_zero] using
      hbound (fun i => (u i, 0)) hv
  intro s
  induction s with
  | zero =>
      intro a b hab n f J C H hbound u hu
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a
      subst b
      exact hzero n f J C H hbound u hu
  | succ s ih =>
      intro a b hab n f J C H hbound u hu
      cases a with
      | succ a =>
          have horder : n + (a + 1) + b = (n + a + b) + 1 := by omega
          rw [horder] at hbound
          have hfixed := fixedSpatial_unit_bound J low high x p (1, 0)
            (by simp only [Prod.norm_def, norm_one, norm_zero,
              max_eq_left zero_le_one, le_refl])
            (n + a + b) C H hbound
          rw [J.jointJet_mixed_radial_step hV hc a b n x hx
            (fun i => (u i, 0)) hp]
          exact ih a b (by omega) n _ (J.fixedLast (0, (1, 0))) C H hfixed u hu
      | zero =>
          cases b with
          | zero => exact hzero n f J C H hbound u hu
          | succ b =>
              have horder : n + 0 + (b + 1) = (n + 0 + b) + 1 := by omega
              rw [horder] at hbound
              have hfixed := fixedSpatial_unit_bound J low high x p (0, 1)
                (by simp only [Prod.norm_def, norm_one, norm_zero,
                  max_eq_right zero_le_one, le_refl])
                (n + 0 + b) C H hbound
              rw [J.jointJet_mixed_angular_step hV hc 0 b n x hx
                (fun i => (u i, 0)) hp]
              exact ih 0 b (by omega) n _ (J.fixedLast (0, (0, 1))) C H hfixed u hu

/-- Restricting joint jets to the two spatial unit directions does not
change the parameter growth factor. -/
theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.mixedJet_unit_bound_of_jointJet
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (low high : Seminorm ℝ E) (n a b : ℕ)
    (x : E) (hx : x ∈ U) (p : PolarPoint) (hp : p ∈ V) (C H : ℝ)
    (hbound : ∀ v : Fin (n + a + b) → E × PolarPoint,
      (∀ i, low (v i).1 + ‖(v i).2‖ ≤ 1) →
      |J.D (n + a + b) (x, p) v| ≤ C * (H + ∑ i : Fin (n + a + b), high (v i).1))
    (u : Fin n → E) (hu : ∀ i, low (u i) ≤ 1) :
    |mixedDerivative a b (fun q => J.D n (x, q) (fun i => (u i, 0))) p| ≤
      C * (H + ∑ i : Fin n, high (u i)) :=
  mixedJet_unit_bound_aux hV hc low high x hx p hp (a + b) a b le_rfl
    n f J C H hbound u hu

private theorem mixedDerivative_add_on_open
    {f g : PolarPoint → ℝ} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g V)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ V) :
    mixedDerivative a b (fun q => f q + g q) p =
      mixedDerivative a b f p + mixedDerivative a b g p := by
  have h := mixedDerivative_sub_of_contDiffOn hV hf
    ((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : PolarPoint => (-1 : ℝ)) V).mul hg)
    a b hp
  have he : (fun q : PolarPoint => f q - (-1) * g q) = fun q => f q + g q := by
    funext q
    ring
  rw [he, mixedDerivative_const_mul] at h
  simpa only [neg_one_mul, sub_neg_eq_add] using h

private def pureJointParameterLinear : E →L[ℝ] E × PolarPoint :=
  (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] PolarPoint)

private theorem pureJointParameterLinear_apply (v : E) :
    pureJointParameterLinear v = (v, (0 : PolarPoint)) := rfl

/-- The actual mixed spatial derivative is an algebraic multilinear map
of its parameter slots. Smoothness is used to justify its additivity. -/
def _root_.ContinuousFlexibility.Statements.SmoothDirections.mixedParameterMultilinearMap
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (hV : IsOpen V) (n a b : ℕ) (x : E) (hx : x ∈ U)
    (p : PolarPoint) (hp : p ∈ V) : MultilinearMap ℝ (fun _ : Fin n => E) ℝ where
  toFun v := mixedDerivative a b (fun q => J.D n (x, q) (fun i => (v i, 0))) p
  map_update_add' v i u w := by
    have heq : (fun q => J.D n (x, q) (fun j => (Function.update v i (u + w) j, 0))) =
        fun q => J.D n (x, q) (fun j => (Function.update v i u j, 0)) +
          J.D n (x, q) (fun j => (Function.update v i w j, 0)) := by
      funext q
      have h := ((J.D n (x, q)).compContinuousLinearMap
        (fun _ => pureJointParameterLinear (E := E))).map_update_add v i u w
      simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        pureJointParameterLinear_apply] using h
    exact (congrArg (fun g : PolarPoint → ℝ => mixedDerivative a b g p) heq).trans
      (mixedDerivative_add_on_open hV
        (J.jointJet_spatial_contDiffOn hV n x hx (fun j => (Function.update v i u j, 0)))
        (J.jointJet_spatial_contDiffOn hV n x hx (fun j => (Function.update v i w j, 0)))
        a b hp)
  map_update_smul' v i c u := by
    have heq : (fun q => J.D n (x, q) (fun j => (Function.update v i (c • u) j, 0))) =
        fun q => c * J.D n (x, q) (fun j => (Function.update v i u j, 0)) := by
      funext q
      have h := ((J.D n (x, q)).compContinuousLinearMap
        (fun _ => pureJointParameterLinear (E := E))).map_update_smul v i c u
      simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        pureJointParameterLinear_apply, smul_eq_mul] using h
    exact (congrArg (fun g : PolarPoint → ℝ => mixedDerivative a b g p) heq).trans
      (mixedDerivative_const_mul c _ a b p)

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.mixedParameterMultilinearMap_apply
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (hV : IsOpen V) (n a b : ℕ) (x : E) (hx : x ∈ U)
    (p : PolarPoint) (hp : p ∈ V) (v : Fin n → E) :
    J.mixedParameterMultilinearMap hV n a b x hx p hp v =
      mixedDerivative a b (fun q => J.D n (x, q) (fun i => (v i, 0))) p := rfl

/-- A fixed joint loss becomes `n + loss` at parameter order `n`.
The low order stays fixed, and all directions are unrestricted. -/
theorem UniformWeightedJointGrowth.mixed_parameter_oneHigh
    {ι : Type*} {V : ι → Set PolarPoint} {f : ι → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {p : ℕ → Seminorm ℝ E} {W : ι → ℝ} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (hp : Monotone p) (hW : ∀ i, 1 ≤ W i)
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (R : ℝ) (hR : 0 ≤ R) (n s : ℕ) :
    ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p base x ≤ R → ∀ y ∈ V i, ∀ v : Fin n → E,
      ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (fun q => (J i).D n (x, q) (fun j => (v j, 0))) y| ≤
          C * W i ^ Q * oneHighVariationWeight p base (s + (n + loss)) x v := by
  classical
  choose C Q hC hQ hb using fun k : Fin (n + s + 1) => hJ R hR k
  let A : ℝ := ∑ k : Fin (n + s + 1), C k
  let P : ℝ := ∑ k : Fin (n + s + 1), Q k
  have hA : 0 ≤ A := Finset.sum_nonneg (fun k _ => hC k)
  have hP : 0 ≤ P := Finset.sum_nonneg (fun k _ => hQ k)
  refine ⟨A, P, hA, hP, fun i x hx hlow y hy v a b hab => ?_⟩
  let high : ℕ := s + (n + loss)
  let L := (J i).mixedParameterMultilinearMap (hV i) n a b x hx y hy
  have hscale : 0 ≤ A * W i ^ P :=
    mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)
  have hunit (u : Fin n → E) (hu : ∀ j, p base (u j) < 1) :
      (normSeminorm ℝ ℝ) (L u) ≤
        (A * W i ^ P) * ((1 + p high x) + ∑ j : Fin n, p high (u j)) := by
    have hjoint (w : Fin (n + a + b) → E × PolarPoint)
        (hw : ∀ j, p base (w j).1 + ‖(w j).2‖ ≤ 1) :
        |(J i).D (n + a + b) (x, y) w| ≤
          (A * W i ^ P) * ((1 + p high x) + ∑ j : Fin (n + a + b), p high (w j).1) := by
      let k : Fin (n + s + 1) := ⟨n + a + b, by omega⟩
      have hCA : C k ≤ A := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ k)
      have hQP : Q k ≤ P := Finset.single_le_sum (fun j _ => hQ j) (Finset.mem_univ k)
      have hweight : W i ^ Q k ≤ W i ^ P :=
        Real.rpow_le_rpow_of_exponent_le (hW i) hQP
      have hcoef : C k * W i ^ Q k ≤ A * W i ^ P :=
        mul_le_mul hCA hweight (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) hA
      have hindex : (k : ℕ) + loss ≤ high := by dsimp only [k, high]; omega
      have hgrowth : (1 + p ((k : ℕ) + loss) x) +
          (∑ j : Fin (n + a + b), p ((k : ℕ) + loss) (w j).1) ≤
          (1 + p high x) + ∑ j : Fin (n + a + b), p high (w j).1 :=
        add_le_add (add_le_add le_rfl (hp hindex x))
          (Finset.sum_le_sum (fun j _ => hp hindex (w j).1))
      have hg0 : 0 ≤ (1 + p ((k : ℕ) + loss) x) +
          ∑ j : Fin (n + a + b), p ((k : ℕ) + loss) (w j).1 := by positivity
      have h := hb k i x hx hlow y hy w hw
      rw [Real.norm_eq_abs] at h
      exact h.trans (mul_le_mul hcoef hgrowth hg0 hscale)
    have h := (J i).mixedJet_unit_bound_of_jointJet (hV i) (hc i)
      (p base) (p high) n a b x hx y hy (A * W i ^ P) (1 + p high x)
      hjoint u (fun j => (hu j).le)
    simpa only [L, ContinuousFlexibility.Statements.SmoothDirections.mixedParameterMultilinearMap_apply,
      coe_normSeminorm, Real.norm_eq_abs] using h
  have h := multilinearMap_bound_of_unitBall L (normSeminorm ℝ ℝ)
    (p base) (p high) hscale hunit v
  simpa only [L, ContinuousFlexibility.Statements.SmoothDirections.mixedParameterMultilinearMap_apply,
    coe_normSeminorm, Real.norm_eq_abs, high, multilinearTameSize,
    oneHighVariationWeight] using h

end ContinuousFlexibility.Analysis
