import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets
import ContinuousFlexibility.Analysis.RootCharacteristicFactor
import ContinuousFlexibility.Geometry.PlanarOrientation

/-!
# Removing the fixed inward root scale from actual ordinary jets

An invertible radial affine map only changes the numerical majorant.
The state neighborhood and derivative loss are unchanged. The actual
Jacobian changes by the signed radial scale, so its absolute lower
bound has the same positive scaling at both endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootProfileInverseLinear (ℓ : ℝ) : PolarPoint →L[ℝ] PolarPoint :=
  (ℓ⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

def rootAffineJetEnvelope (ℓ : ℝ) (A : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 + ‖rootProfileInverseLinear ℓ‖ ^ n) * A n

theorem rootAffineJetEnvelope_pos {A : ℕ → ℝ} (hA : ∀ n, 0 < A n)
    (ℓ : ℝ) (n : ℕ) : 0 < rootAffineJetEnvelope ℓ A n :=
  mul_pos (add_pos_of_pos_of_nonneg zero_lt_one
    (pow_nonneg (norm_nonneg _) _)) (hA n)

theorem pointwiseMaterialJetBound_of_iteratedFDeriv_eq
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {z : E}
    {f g : X → Y} {x : X}
    (he : ∀ n, iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x)
    (hb : PointwiseMaterialJetBound p loss A z g x) :
    PointwiseMaterialJetBound p loss A z f x := by
  intro n
  rw [he n]
  exact hb n

theorem root_fderiv_eq_of_firstJet_eq
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f g : X → Y} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (he : iteratedFDeriv ℝ 1 f x = iteratedFDeriv ℝ 1 g x) :
    fderiv ℝ f x = fderiv ℝ g x := by
  have hz : iteratedFDeriv ℝ 1 (f - g) x = 0 := by
    rw [iteratedFDeriv_sub_apply (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
      (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)), he, sub_self]
  have hd : HasFDerivAt (f - g) (fderiv ℝ f x - fderiv ℝ g x) x :=
    (hf.differentiableAt (by simp)).hasFDerivAt.sub
      (hg.differentiableAt (by simp)).hasFDerivAt
  have hn : ‖fderiv ℝ f x - fderiv ℝ g x‖ = 0 := by
    simpa only [norm_iteratedFDeriv_one, hd.fderiv, norm_zero] using congrArg norm hz
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

private theorem rootProfileShift_inverse_affine
    (r ℓ : ℝ) (hℓ : ℓ ≠ 0) (y : PolarPoint) :
    rootProfileShift r ℓ ((-r / ℓ, 0) + rootProfileInverseLinear ℓ y) = y := by
  ext <;> simp only [rootProfileInverseLinear, rootProfileShift,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd, smul_eq_mul, zero_add] <;>
    field_simp [hℓ] <;> ring

private theorem rootProfile_inverse_affine_shift
    (r ℓ : ℝ) (hℓ : ℓ ≠ 0) (q : PolarPoint) :
    (-r / ℓ, 0) + rootProfileInverseLinear ℓ (rootProfileShift r ℓ q) = q := by
  ext <;> simp only [rootProfileInverseLinear, rootProfileShift,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd, smul_eq_mul, zero_add] <;>
    field_simp [hℓ] <;> ring

theorem PointwiseMaterialJetBound.unscale_rootProfile
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {z : E}
    (r ℓ : ℝ) (hℓ : ℓ ≠ 0) (hA : ∀ n, 0 ≤ A n)
    {f : PolarPoint → Y} {q : PolarPoint}
    (hf : ContDiffAt ℝ ∞ (fun y => f (rootProfileShift r ℓ y)) q)
    (hb : PointwiseMaterialJetBound p loss A z
      (fun y => f (rootProfileShift r ℓ y)) q) :
    PointwiseMaterialJetBound p loss (rootAffineJetEnvelope ℓ A) z
      f (rootProfileShift r ℓ q) := by
  let a : PolarPoint := (-r / ℓ, 0)
  let L := rootProfileInverseLinear ℓ
  have hback (y : PolarPoint) : rootProfileShift r ℓ (a + L y) = y :=
    rootProfileShift_inverse_affine r ℓ hℓ y
  have harg : a + L (rootProfileShift r ℓ q) = q :=
    rootProfile_inverse_affine_shift r ℓ hℓ q
  have hs : ContDiffAt ℝ ∞ (fun y => f (rootProfileShift r ℓ y))
      (a + L (rootProfileShift r ℓ q)) := by rw [harg]; exact hf
  have hj : PointwiseMaterialJetBound p loss A z
      (fun y => f (rootProfileShift r ℓ y)) (a + L (rootProfileShift r ℓ q)) := by
    rw [harg]
    exact hb
  have ha : PointwiseMaterialJetBound p loss (fun n => ‖L‖ ^ n * A n) z
      (fun y => f (rootProfileShift r ℓ (a + L y))) (rootProfileShift r ℓ q) :=
    PointwiseMaterialJetBound.affine_comp
      (E := E) (X := PolarPoint) (Y := PolarPoint) (Z := Y)
      (p := p) (loss := loss) (A := A) (z := z)
      (f := fun y => f (rootProfileShift r ℓ y))
      (x := rootProfileShift r ℓ q) L a hs hj
  have he : (fun y => f (rootProfileShift r ℓ (a + L y))) = f := by
    funext y
    rw [hback y]
  rw [he] at ha
  intro n
  exact (ha n).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (hA n))
    (add_nonneg zero_le_one (apply_nonneg _ _)))

theorem hasFDerivAt_rootProfileShift (r ℓ : ℝ) (q : PolarPoint) :
    HasFDerivAt (rootProfileShift r ℓ)
      ((ℓ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) q := by
  let M : PolarPoint →L[ℝ] PolarPoint :=
    (ℓ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hM : HasFDerivAt (M : PolarPoint → PolarPoint) M q := M.hasFDerivAt
  have hd : HasFDerivAt (fun y : PolarPoint => (r, 0) + M y) M q :=
    hM.const_add (r, 0)
  have he : (fun y : PolarPoint => (r, 0) + M y) = rootProfileShift r ℓ := by
    funext y
    ext <;> simp only [M, rootProfileShift, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd,
      smul_eq_mul, zero_add]
  rw [he] at hd
  exact hd

/-- The positive-order estimate does not require a bounded angular
lift value. The temporary zeroth majorant disappears at every positive
order because the change of variables is affine. -/
theorem rootProfile_unscale_positiveJets
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {z : E}
    (r ℓ : ℝ) (hℓ : ℓ ≠ 0) (hA : ∀ n, 0 ≤ A n)
    {f : PolarPoint → Y} {q : PolarPoint}
    (hf : ContDiffAt ℝ ∞ (fun y => f (rootProfileShift r ℓ y)) q)
    (hb : ∀ n : ℕ, 1 ≤ n →
      ‖iteratedFDeriv ℝ n (fun y => f (rootProfileShift r ℓ y)) q‖ ≤
        A n * (1 + p (n + loss) z)) :
    ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n f (rootProfileShift r ℓ q)‖ ≤
      rootAffineJetEnvelope ℓ A n * (1 + p (n + loss) z) := by
  let A' : ℕ → ℝ := fun n => if n = 0 then
    ‖iteratedFDeriv ℝ 0 (fun y => f (rootProfileShift r ℓ y)) q‖ else A n
  have hA' (n : ℕ) : 0 ≤ A' n := by
    by_cases hn : n = 0
    · simp only [A', hn, ite_true]; exact norm_nonneg _
    · simp only [A', hn, ite_false]; exact hA n
  have hjet : PointwiseMaterialJetBound p loss A' z
      (fun y => f (rootProfileShift r ℓ y)) q := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [A', ite_true]
      exact le_mul_of_one_le_right (norm_nonneg _)
        (le_add_of_nonneg_right (apply_nonneg _ _))
    · simpa only [A', if_neg hn] using hb n (Nat.one_le_iff_ne_zero.mpr hn)
  have he := hjet.unscale_rootProfile r ℓ hℓ hA' hf
  intro n hn
  simpa only [rootAffineJetEnvelope, A', if_neg (by omega : n ≠ 0)] using he n

theorem planeJacobian_rootProfileShift (r ℓ : ℝ) (q : PolarPoint) :
    planeJacobian (rootProfileShift r ℓ) q = ℓ := by
  unfold planeJacobian
  rw [(hasFDerivAt_rootProfileShift r ℓ q).fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd,
    smul_eq_mul, mul_one, mul_zero, zero_mul, sub_zero]

theorem planeJacobian_unscale_rootProfile_lower
    (r ℓ : ℝ) (hℓ : ℓ ≠ 0) {F : PolarPoint → PolarPoint} {q : PolarPoint}
    (hF : DifferentiableAt ℝ F (rootProfileShift r ℓ q)) {J₀ : ℝ}
    (hJ : J₀ ≤ planeJacobian (fun y => F (rootProfileShift r ℓ y)) q) :
    J₀ / |ℓ| ≤ |planeJacobian F (rootProfileShift r ℓ q)| := by
  have hc := planeJacobian_comp (hasFDerivAt_rootProfileShift r ℓ q).differentiableAt hF
  have he : F ∘ rootProfileShift r ℓ = (fun y => F (rootProfileShift r ℓ y)) := by
    funext y
    exact Function.comp_apply
  rw [he, planeJacobian_rootProfileShift] at hc
  apply (div_le_iff₀ (abs_pos.mpr hℓ)).mpr
  exact hJ.trans ((le_abs_self _).trans_eq (by rw [hc, abs_mul]))

end ContinuousFlexibility.Analysis
