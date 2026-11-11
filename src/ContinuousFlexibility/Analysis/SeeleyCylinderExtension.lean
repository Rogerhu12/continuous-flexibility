import ContinuousFlexibility.Analysis.SeeleyCoefficients
import ContinuousFlexibility.Analysis.SeeleyJetExtension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# A joint smooth Seeley extension on the cylinder

The same reflection coefficients extend every radial and angular jet.
Radial differentiability follows from the one-dimensional Seeley theorem;
angular differentiation is justified by its summable absolute moments.
Joint continuity of the extended jets then proves actual differentiability
on the product, including the entire boundary line. This constructs one
jointly smooth function, not a collection of unrelated slice extensions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Actual half-plane derivative relations, continuity up to the boundary,
and a uniform bound at every mixed order. These data include no extension. -/
structure IsBoundedCylinderHalfLineJet (J : ℕ → ℕ → ℝ × ℝ → ℝ) : Prop where
  continuous : ∀ a b, ContinuousOn (J a b) {p | 0 ≤ p.1}
  radial : ∀ a b r θ, 0 < r →
    HasDerivAt (fun x => J a b (x, θ)) (J (a + 1) b (r, θ)) r
  angular : ∀ a b r θ, 0 ≤ r →
    HasDerivAt (fun t => J a b (r, t)) (J a (b + 1) (r, θ)) θ
  bounded : ∀ a b, ∃ M : ℝ, ∀ p, 0 ≤ p.1 → ‖J a b p‖ ≤ M

variable {ι : Type*}

/-- The fixed Seeley formula is applied in the radial coordinate only. -/
def seeleyCylinderExtend (S : SeeleyData ι) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  seeleyExtend S (fun r => f (r, p.2)) p.1

/-- The candidate mixed jets use the radial moment of the same coefficients. -/
def seeleyCylinderJet (S : SeeleyData ι) (J : ℕ → ℕ → ℝ × ℝ → ℝ)
    (a b : ℕ) (p : ℝ × ℝ) : ℝ :=
  seeleyExtensionJet S (fun n r => J n b (r, p.2)) a p.1

@[simp] theorem seeleyCylinderExtend_of_nonneg (S : SeeleyData ι)
    (f : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    seeleyCylinderExtend S f p = f p := by
  exact seeleyExtend_of_nonneg S (fun r => f (r, p.2)) hp

@[simp] theorem seeleyCylinderJet_of_nonneg (S : SeeleyData ι)
    (J : ℕ → ℕ → ℝ × ℝ → ℝ) (a b : ℕ) {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    seeleyCylinderJet S J a b p = J a b p := by
  exact seeleyExtensionJet_of_nonneg S (fun n r => J n b (r, p.2)) a hp

@[simp] theorem seeleyCylinderJet_zero (S : SeeleyData ι)
    (J : ℕ → ℕ → ℝ × ℝ → ℝ) :
    seeleyCylinderJet S J 0 0 = seeleyCylinderExtend S (J 0 0) := rfl

private theorem cylinderHalfLineJet_slice
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J)
    (b : ℕ) (θ : ℝ) : IsBoundedHalfLineJet (fun a r => J a b (r, θ)) where
  continuous a :=
    (hJ.continuous a b).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => hr)
  derivative a r hr := hJ.radial a b r θ hr
  bounded a := by
    obtain ⟨M, hM⟩ := hJ.bounded a b
    exact ⟨M, fun r hr => hM (r, θ) hr⟩

/-- Every extended candidate mixed jet is jointly continuous. -/
theorem continuous_seeleyCylinderJet (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J) (a b : ℕ) :
    Continuous (seeleyCylinderJet S J a b) := by
  obtain ⟨M, hM⟩ := hJ.bounded a b
  have hleft : ContinuousOn
      (fun p : ℝ × ℝ => ∑' i, (S.a i * (-S.b i) ^ a) •
        J a b (-S.b i * p.1, p.2)) {p | p.1 ≤ 0} := by
    refine continuousOn_tsum ?_ ((S.summable_moment a).mul_right M) ?_
    · intro i
      have hm : Continuous (fun p : ℝ × ℝ => (-S.b i * p.1, p.2)) :=
        (continuous_const.mul continuous_fst).prodMk continuous_snd
      have hc : ContinuousOn
          (fun p : ℝ × ℝ => J a b (-S.b i * p.1, p.2))
          {p : ℝ × ℝ | p.1 ≤ 0} :=
        (hJ.continuous a b).comp hm.continuousOn
          (fun p (hp : p.1 ≤ 0) => mul_nonneg_of_nonpos_of_nonpos
            (neg_nonpos.mpr (S.b_nonneg i)) hp)
      exact continuousOn_const.smul hc
    · intro i p hp
      rw [norm_smul, norm_seeley_coefficient]
      exact mul_le_mul_of_nonneg_left
        (hM _ (mul_nonneg_of_nonpos_of_nonpos
          (neg_nonpos.mpr (S.b_nonneg i)) hp))
        (mul_nonneg (abs_nonneg _) (pow_nonneg (S.b_nonneg i) a))
  change Continuous (fun p : ℝ × ℝ => if 0 ≤ p.1 then J a b p else
    ∑' i, (S.a i * (-S.b i) ^ a) • J a b (-S.b i * p.1, p.2))
  apply continuous_if_le continuous_const continuous_fst (hJ.continuous a b) hleft
  intro p hp
  change (0 : ℝ) = p.1 at hp
  change J a b p = seeleyReflection S a (fun r => J a b (r, p.2)) p.1
  rw [← hp, seeleyReflection_at_zero]
  exact congrArg (J a b) (Prod.ext hp.symm rfl)

/-- The radial derivative, including at zero, is the next extended jet. -/
theorem hasDerivAt_seeleyCylinderJet_radial (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J)
    (a b : ℕ) (r θ : ℝ) :
    HasDerivAt (fun x => seeleyCylinderJet S J a b (x, θ))
      (seeleyCylinderJet S J (a + 1) b (r, θ)) r := by
  exact hasDerivAt_seeleyExtensionJet S (cylinderHalfLineJet_slice hJ b θ) a r

/-- Angular differentiation of the actual reflection series commutes with
extension. The bound is uniform in the angle, so the same coefficients work
at every angular order. -/
theorem hasDerivAt_seeleyCylinderJet_angular (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J)
    (a b : ℕ) (r θ : ℝ) :
    HasDerivAt (fun t => seeleyCylinderJet S J a b (r, t))
      (seeleyCylinderJet S J a (b + 1) (r, θ)) θ := by
  by_cases hr : 0 ≤ r
  · have he : (fun t => seeleyCylinderJet S J a b (r, t)) =
        fun t => J a b (r, t) :=
      funext fun _ => seeleyCylinderJet_of_nonneg S J a b hr
    rw [he, seeleyCylinderJet_of_nonneg S J a (b + 1) hr]
    exact hJ.angular a b r θ hr
  · have hrneg : r < 0 := lt_of_not_ge hr
    obtain ⟨M, hM⟩ := hJ.bounded a (b + 1)
    obtain ⟨M₀, hM₀⟩ := hJ.bounded a b
    have hsum : Summable (fun i => (S.a i * (-S.b i) ^ a) •
        J a b (-S.b i * r, θ)) :=
      summable_seeleyReflection S a ⟨M₀, fun y hy => hM₀ (y, θ) hy⟩ hrneg.le
    simp only [seeleyCylinderJet, seeleyExtensionJet, if_neg hr]
    change HasDerivAt
      (fun t => ∑' i, (S.a i * (-S.b i) ^ a) • J a b (-S.b i * r, t))
      (∑' i, (S.a i * (-S.b i) ^ a) • J a (b + 1) (-S.b i * r, θ)) θ
    refine hasDerivAt_tsum_of_isPreconnected
      (t := univ)
      (g := fun i t => (S.a i * (-S.b i) ^ a) • J a b (-S.b i * r, t))
      (g' := fun i t => (S.a i * (-S.b i) ^ a) • J a (b + 1) (-S.b i * r, t))
      (y₀ := θ) ((S.summable_moment a).mul_right M)
      isOpen_univ isPreconnected_univ ?_ ?_ (mem_univ _) hsum (mem_univ _)
    · intro i t _
      exact (hJ.angular a b (-S.b i * r) t
        (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (S.b_nonneg i)) hrneg.le)).const_smul
          (S.a i * (-S.b i) ^ a)
    · intro i t _
      rw [norm_smul, norm_seeley_coefficient]
      exact mul_le_mul_of_nonneg_left
        (hM _ (mul_nonneg_of_nonpos_of_nonpos
          (neg_nonpos.mpr (S.b_nonneg i)) hrneg.le))
        (mul_nonneg (abs_nonneg _) (pow_nonneg (S.b_nonneg i) a))

private theorem continuous_toSpanSingleton_comp
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
    Continuous (fun x => ContinuousLinearMap.toSpanSingleton ℝ (f x)) := by
  have he : (fun x => ContinuousLinearMap.toSpanSingleton ℝ (f x)) =
      fun x => f x • ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) := by
    funext x
    simpa only [smul_eq_mul, mul_one] using
      ContinuousLinearMap.toSpanSingleton_smul ℝ (f x) (1 : ℝ)
  rw [he]
  exact hf.smul continuous_const

/-- The two actual partial derivatives and their joint continuity give the
true Fréchet derivative at every point, including the boundary line. -/
theorem hasFDerivAt_seeleyCylinderJet (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J)
    (a b : ℕ) (p : ℝ × ℝ) :
    HasFDerivAt (seeleyCylinderJet S J a b)
      ((ContinuousLinearMap.toSpanSingleton ℝ (seeleyCylinderJet S J (a + 1) b p)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (seeleyCylinderJet S J a (b + 1) p))) p := by
  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun r θ => seeleyCylinderJet S J a b (r, θ))
    (f₁ := fun r θ => ContinuousLinearMap.toSpanSingleton ℝ
      (seeleyCylinderJet S J (a + 1) b (r, θ)))
    (f₂ := fun r θ => ContinuousLinearMap.toSpanSingleton ℝ
      (seeleyCylinderJet S J a (b + 1) (r, θ)))
    (Eventually.of_forall fun q =>
      (hasDerivAt_seeleyCylinderJet_radial S hJ a b q.1 q.2).hasFDerivAt)
    (Eventually.of_forall fun q =>
      (hasDerivAt_seeleyCylinderJet_angular S hJ a b q.1 q.2).hasFDerivAt)
    (continuous_toSpanSingleton_comp
      (continuous_seeleyCylinderJet S hJ (a + 1) b)).continuousAt
    (continuous_toSpanSingleton_comp
      (continuous_seeleyCylinderJet S hJ a (b + 1))).continuousAt).hasFDerivAt

theorem fderiv_seeleyCylinderJet_apply (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J)
    (a b : ℕ) (p v : ℝ × ℝ) :
    fderiv ℝ (seeleyCylinderJet S J a b) p v =
      v.1 * seeleyCylinderJet S J (a + 1) b p +
        v.2 * seeleyCylinderJet S J a (b + 1) p := by
  rw [(hasFDerivAt_seeleyCylinderJet S hJ a b p).fderiv]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]

private theorem contDiff_nat_seeleyCylinderJet (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J)
    (n : ℕ) : ∀ a b, ContDiff ℝ n (seeleyCylinderJet S J a b) := by
  induction n with
  | zero =>
      intro a b
      exact contDiff_zero.mpr (continuous_seeleyCylinderJet S hJ a b)
  | succ n ih =>
      intro a b
      have hnext : ContDiff ℝ ((n : ℕ∞ω) + 1) (seeleyCylinderJet S J a b) := by
        apply contDiff_succ_iff_fderiv_apply.mpr
        refine ⟨fun p => (hasFDerivAt_seeleyCylinderJet S hJ a b p).differentiableAt,
          by simp, ?_⟩
        intro v
        have he : (fun p => fderiv ℝ (seeleyCylinderJet S J a b) p v) =
            fun p => v.1 * seeleyCylinderJet S J (a + 1) b p +
              v.2 * seeleyCylinderJet S J a (b + 1) p :=
          funext fun p => fderiv_seeleyCylinderJet_apply S hJ a b p v
        rw [he]
        have hr : ContDiff ℝ n (seeleyCylinderJet S J (a + 1) b) := ih (a + 1) b
        have hθ : ContDiff ℝ n (seeleyCylinderJet S J a (b + 1)) := ih a (b + 1)
        have hr' : ContDiff ℝ n (fun p => v.1 * seeleyCylinderJet S J (a + 1) b p) :=
          contDiff_const.mul hr
        have hθ' : ContDiff ℝ n (fun p => v.2 * seeleyCylinderJet S J a (b + 1) p) :=
          contDiff_const.mul hθ
        exact hr'.add hθ'
      simpa only [Nat.cast_add, Nat.cast_one] using hnext

/-- Every candidate extended jet is jointly smooth of all orders. -/
theorem contDiff_seeleyCylinderJet (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J) (a b : ℕ) :
    ContDiff ℝ ∞ (seeleyCylinderJet S J a b) := by
  exact contDiff_infty.mpr fun n => contDiff_nat_seeleyCylinderJet S hJ n a b

theorem contDiff_seeleyCylinderExtend (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J) :
    ContDiff ℝ ∞ (seeleyCylinderExtend S (J 0 0)) := by
  rw [← seeleyCylinderJet_zero]
  exact contDiff_seeleyCylinderJet S hJ 0 0

theorem iteratedDeriv_seeleyCylinderJet_radial (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J)
    (a b n : ℕ) (θ : ℝ) :
    iteratedDeriv n (fun r => seeleyCylinderJet S J a b (r, θ)) =
      fun r => seeleyCylinderJet S J (a + n) b (r, θ) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext r
      simpa only [Nat.add_assoc] using
        (hasDerivAt_seeleyCylinderJet_radial S hJ (a + n) b r θ).deriv

theorem iteratedDeriv_seeleyCylinderJet_angular (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J)
    (a b n : ℕ) (r : ℝ) :
    iteratedDeriv n (fun θ => seeleyCylinderJet S J a b (r, θ)) =
      fun θ => seeleyCylinderJet S J a (b + n) (r, θ) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext θ
      simpa only [Nat.add_assoc] using
        (hasDerivAt_seeleyCylinderJet_angular S hJ a (b + n) r θ).deriv

/-- The constructed function has the actual mixed derivatives prescribed
by the fixed reflection formula. No candidate jet is assumed to be a
derivative of the extension. -/
theorem iteratedDeriv_seeleyCylinderExtend (S : SeeleyData ι)
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J)
    (a b : ℕ) (p : ℝ × ℝ) :
    iteratedDeriv a
      (fun r => iteratedDeriv b (fun θ => seeleyCylinderExtend S (J 0 0) (r, θ)) p.2)
      p.1 = seeleyCylinderJet S J a b p := by
  rw [← seeleyCylinderJet_zero]
  simp only [iteratedDeriv_seeleyCylinderJet_angular S hJ, Nat.zero_add]
  rw [iteratedDeriv_seeleyCylinderJet_radial S hJ]
  simp only [Nat.zero_add]

/-- The already-constructed fixed Seeley coefficients give one global,
jointly smooth extension agreeing with the input on the closed half-plane. -/
theorem exists_contDiff_cylinder_extension
    {J : ℕ → ℕ → ℝ × ℝ → ℝ} (hJ : IsBoundedCylinderHalfLineJet J) :
    ∃ f : ℝ × ℝ → ℝ, ContDiff ℝ ∞ f ∧ ∀ p, 0 ≤ p.1 → f p = J 0 0 p := by
  exact ⟨seeleyCylinderExtend seeleyData (J 0 0), contDiff_seeleyCylinderExtend seeleyData hJ,
    fun p hp => seeleyCylinderExtend_of_nonneg seeleyData (J 0 0) hp⟩

end ContinuousFlexibility.Analysis
