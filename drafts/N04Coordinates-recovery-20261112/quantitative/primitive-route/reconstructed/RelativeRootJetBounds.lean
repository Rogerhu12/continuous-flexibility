import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds
import ContinuousFlexibility.Analysis.PlanarInverseJacobianMaterialJets
import ContinuousFlexibility.Analysis.PointwiseProductMaterialJets
import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations

/-!
# Fixed-loss bounds for actual relative root maps and height products

These pointwise calculus adapters keep the genuine inverse germs. They
introduce no bound on the zeroth-order angular lift. Every low order and
loss is selected before the numerical component envelopes and Jacobian
lower bound. Scalar values are handled by their actual zeroth-order jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem relativeRoot_bound_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) {z : E}
    {n l L : ℕ} (hl : l ≤ L) {v A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hv : v ≤ A * (1 + p (n + l) z)) :
    v ≤ B * (1 + p (n + L) z) :=
  hv.trans (mul_le_mul hAB
    (add_le_add le_rfl (hp (Nat.add_le_add_left hl n) z))
    (add_nonneg zero_le_one (apply_nonneg _ _)) (hA.trans hAB))

theorem coordinateComposition_positiveJets_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ f : Y → Z, ∀ g : X → Y, ∀ x : X,
        ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n f (g x)‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n g x‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤
          B n * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, hcomp⟩ :=
    coordinateComposition_fixed_loss_material_bound (X := X) (Y := Y) (Z := Z)
      hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA
  obtain ⟨B, hB, hbound⟩ := hcomp (fun n => 1 + A n)
    (fun n => le_add_of_nonneg_right (hA n).le)
  refine ⟨fun n => B (n - 1), fun n => hB (n - 1), ?_⟩
  intro z hz f g x hf hg hfj hgj n hn
  have hmajor {F : X → Y} {q : X} {k : ℕ}
      (h : ‖iteratedFDeriv ℝ k F q‖ ≤ A k * (1 + p (k + inputLoss) z)) :
      ‖iteratedFDeriv ℝ k F q‖ ≤
        (1 + A k) * (1 : ℝ) ^ (1 + A k) * (1 + p (k + inputLoss) z) := by
    simpa only [Real.one_rpow, mul_one] using
      relativeRoot_bound_mono hp le_rfl (hA k).le
        (le_add_of_nonneg_left zero_le_one) h
  have houter (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k f (g x)‖ ≤
        (1 + A k) * (1 : ℝ) ^ (1 + A k) * (1 + p (k + inputLoss) z) := by
    simpa only [Real.one_rpow, mul_one] using
      relativeRoot_bound_mono hp le_rfl (hA k).le
        (le_add_of_nonneg_left zero_le_one) (hfj k hk)
  simpa only [Real.one_rpow, mul_one, Nat.sub_add_cancel hn] using
    hbound z hz 1 le_rfl f g x hf hg houter (fun k hk => hmajor (hgj k hk)) (n - 1)

theorem pointwiseComposition_allJets_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ f : Y → ℝ, ∀ g : X → Y, ∀ x : X,
        ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
        PointwiseMaterialJetBound p inputLoss A z f (g x) →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n g x‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        PointwiseMaterialJetBound p loss B z (f ∘ g) x := by
  obtain ⟨base, lossC, hcomp⟩ :=
    coordinateComposition_positiveJets_fixed_loss (X := X) (Y := Y) (Z := ℝ)
      hp hI inputLoss
  refine ⟨base, max inputLoss lossC, ?_⟩
  intro A hA
  obtain ⟨B, hB, hb⟩ := hcomp A hA
  refine ⟨fun n => A n + B n, fun n => add_pos (hA n) (hB n), ?_⟩
  intro z hz f g x hf hg hfj hgj n
  cases n with
  | zero =>
      have hzero : ‖iteratedFDeriv ℝ 0 (f ∘ g) x‖ ≤
          A 0 * (1 + p (0 + inputLoss) z) := by
        simpa only [norm_iteratedFDeriv_zero, Function.comp_apply] using hfj 0
      exact relativeRoot_bound_mono hp (le_max_left _ _) (hA 0).le
        (le_add_of_nonneg_right (hB 0).le) hzero
  | succ n =>
      exact relativeRoot_bound_mono hp (le_max_right _ _) (hB (n + 1)).le
        (le_add_of_nonneg_left (hA (n + 1)).le)
        (hb z hz f g x hf hg (fun k _ => hfj k) hgj (n + 1) (Nat.succ_pos n))

/-- Forward chart jets and an actual determinant lower bound suffice for
all positive relative jets; the inverse derivatives are proved internally. -/
theorem relativeChart_positiveJets_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ κ : ℝ, 0 < κ → ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ F G F₀ : PolarPoint → PolarPoint, ∀ x : PolarPoint,
        ContDiffAt ℝ ∞ F (G (F₀ x)) → ContDiffAt ℝ ∞ G (F₀ x) →
        ContDiffAt ℝ ∞ F₀ x →
        F ∘ G =ᶠ[𝓝 (F₀ x)] (id : PolarPoint → PolarPoint) →
        G ∘ F =ᶠ[𝓝 (G (F₀ x))] (id : PolarPoint → PolarPoint) →
        κ ≤ |planeJacobian F (G (F₀ x))| →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F (G (F₀ x))‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F₀ x‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (G ∘ F₀) x‖ ≤
          B n * (1 + p (n + loss) z) := by
  obtain ⟨lowI, lossI, hinverse⟩ :=
    planarInverse_positiveJets_of_jacobian_fixed_loss hp hI inputLoss
  let midLoss := max inputLoss lossI
  obtain ⟨lowC, lossC, hcomp⟩ :=
    coordinateComposition_positiveJets_fixed_loss
      (X := PolarPoint) (Y := PolarPoint) (Z := PolarPoint) hp hI midLoss
  refine ⟨max lowI lowC, lossC, ?_⟩
  intro A hA κ hκ
  obtain ⟨I, hIpos, hInv⟩ := hinverse (fun n => 1 + A n)
    (fun n => le_add_of_nonneg_right (hA n).le) κ hκ
  let Q : ℕ → ℝ := fun n => 1 + A n + I n
  have hQ (n : ℕ) : 0 < Q n := add_pos (add_pos zero_lt_one (hA n)) (hIpos n)
  have hAQ (n : ℕ) : A n ≤ Q n := by dsimp only [Q]; linarith [hIpos n]
  have hIQ (n : ℕ) : I n ≤ Q n := by dsimp only [Q]; linarith [hA n]
  obtain ⟨B, hB, hb⟩ := hcomp Q hQ
  refine ⟨B, hB, ?_⟩
  intro z hz F G F₀ x hF hG hF₀ hright hleft hJ hFjets hF₀jets
  have hGjets := hInv z ((hp (le_max_left _ _) z).trans hz)
    F G (F₀ x) hF hG hright hleft hJ
    (fun n hn => relativeRoot_bound_mono hp le_rfl (hA n).le
      (le_add_of_nonneg_left zero_le_one) (hFjets n hn))
  exact hb z ((hp (le_max_right _ _) z).trans hz) G F₀ x hG hF₀
    (fun n hn => relativeRoot_bound_mono hp (le_max_right _ _) (hIpos n).le
      (hIQ n) (hGjets n hn))
    (fun n hn => relativeRoot_bound_mono hp (le_max_left _ _) (hA n).le
      (hAQ n) (hF₀jets n hn))

/-- The same constants cover a height and its reciprocal: apply this
single product-composition statement to the two actual factor pairs. -/
theorem relativeHeightProduct_allJets_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ f₀ f : PolarPoint → ℝ,
      ∀ g : PolarPoint → PolarPoint, ∀ x : PolarPoint,
        ContDiffAt ℝ ∞ f₀ x → ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
        PointwiseMaterialJetBound p inputLoss A z f₀ x →
        PointwiseMaterialJetBound p inputLoss A z f (g x) →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n g x‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        PointwiseMaterialJetBound p loss B z (fun y => f₀ y * f (g y)) x := by
  obtain ⟨lowC, lossC, hcomp⟩ :=
    pointwiseComposition_allJets_fixed_loss (X := PolarPoint) (Y := PolarPoint)
      hp hI inputLoss
  let midLoss := max inputLoss lossC
  obtain ⟨lowP, lossP, hprod⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := PolarPoint) hp hI midLoss
  refine ⟨max lowC lowP, lossP, ?_⟩
  intro A hA
  obtain ⟨C, hC, hc⟩ := hcomp A hA
  let Q : ℕ → ℝ := fun n => A n + C n
  have hQ (n : ℕ) : 0 < Q n := add_pos (hA n) (hC n)
  obtain ⟨B, hB, hb⟩ := hprod Q hQ
  refine ⟨B, hB, ?_⟩
  intro z hz f₀ f g x hf₀ hf hg hf₀jets hfjets hgjets
  have hcompJets := hc z ((hp (le_max_left _ _) z).trans hz) f g x hf hg hfjets hgjets
  have hscalar : ContDiffAt ℝ ∞ (f ∘ g) x := hf.comp x hg
  have hbound := hb z ((hp (le_max_right _ _) z).trans hz) f₀ (f ∘ g) x hf₀ hscalar
    (fun n => relativeRoot_bound_mono hp (le_max_left _ _) (hA n).le
      (le_add_of_nonneg_right (hC n).le) (hf₀jets n))
    (fun n => relativeRoot_bound_mono hp (le_max_right _ _) (hC n).le
      (le_add_of_nonneg_left (hA n).le) (hcompJets n))
  simpa only [Function.comp_apply] using hbound

end ContinuousFlexibility.Analysis
