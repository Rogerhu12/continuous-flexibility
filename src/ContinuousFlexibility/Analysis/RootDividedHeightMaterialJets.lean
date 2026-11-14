module

public import ContinuousFlexibility.Analysis.RootDividedHeight
public import ContinuousFlexibility.Analysis.PositivePowerMaterialJets
public import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations

/-!
# Fixed-loss jets of the actual divided root height

The height and its reciprocal are powers of the same nonsingular
formula. Two uses of the existing positive-power estimate and one
product estimate suffice. The common low order and loss precede the
scale, exponent, positive value intervals, and state. The inputs are
the actual odd coefficient and divided determinant, not height jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem rootDividedHeight_rpow_eq
    {δ : ℝ} {V : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ} {x : PolarPoint}
    (hδ : 0 < δ) (hV : 0 < V x) (hχ : 0 < extendedRootOddCoefficient G x) (a : ℝ) :
    rootDividedHeight δ V G x ^ a =
      (((3 / 2 : ℝ) * extendedRootOddCoefficient G x) ^ (a / 6)) *
        (δ * V x) ^ (-a / 4) := by
  have hχ' : 0 < (3 / 2 : ℝ) * extendedRootOddCoefficient G x := mul_pos (by norm_num) hχ
  have hV' : 0 < δ * V x := mul_pos hδ hV
  rw [rootDividedHeight_eq_powers hδ hV hχ,
    Real.mul_rpow (Real.rpow_nonneg hχ'.le _) (Real.rpow_nonneg hV'.le _),
    ← Real.rpow_mul hχ'.le, ← Real.rpow_mul hV'.le,
    show (1 / 6 : ℝ) * a = a / 6 by ring,
    show (-(1 / 4 : ℝ)) * a = -a / 4 by ring]

/-- Taking exponent `1` gives the actual height; exponent `-1` gives
its reciprocal with the same low order and loss. -/
theorem rootDividedHeight_power_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ δ a lχ uχ lV uV : ℝ,
      0 < δ → 0 < lχ → lχ ≤ uχ → 0 < lV → lV ≤ uV →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ G : ℝ × ℝ × ℝ → ℝ,
      ∀ V : PolarPoint → ℝ, ∀ x : PolarPoint,
      ContDiffAt ℝ ∞ (extendedRootOddCoefficient G) x → ContDiffAt ℝ ∞ V x →
      extendedRootOddCoefficient G x ∈ Icc lχ uχ → V x ∈ Icc lV uV →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootOddCoefficient G) x →
      PointwiseMaterialJetBound p inputLoss A z V x →
      PointwiseMaterialJetBound p loss B z (fun y => rootDividedHeight δ V G y ^ a) x := by
  obtain ⟨powerBase, powerLoss, hpower⟩ :=
    positivePower_fixed_loss_material_bound (X := PolarPoint) hp hI inputLoss
  obtain ⟨productBase, productLoss, hproduct⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := PolarPoint) hp hI powerLoss
  refine ⟨max powerBase productBase, productLoss, ?_⟩
  intro A hA δ a lχ uχ lV uV hδ hlχ hluχ hlV hluV
  have hc : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨C, hC, hχpower⟩ := hpower (fun n => (3 / 2 : ℝ) * A n)
    (fun n => mul_pos hc (hA n)) ((3 / 2) * lχ) ((3 / 2) * uχ) (a / 6)
    (mul_pos hc hlχ) (mul_le_mul_of_nonneg_left hluχ hc.le)
  obtain ⟨D, hD, hVpower⟩ := hpower (fun n => δ * A n)
    (fun n => mul_pos hδ (hA n)) (δ * lV) (δ * uV) (-a / 4)
    (mul_pos hδ hlV) (mul_le_mul_of_nonneg_left hluV hδ.le)
  let Q : ℕ → ℝ := fun n => C n + D n
  have hQ (n : ℕ) : 0 < Q n := add_pos (hC n) (hD n)
  obtain ⟨B, hB, hbound⟩ := hproduct Q hQ
  refine ⟨B, hB, ?_⟩
  intro z hz G V x hχ hV hχvalue hVvalue hχjet hVjet
  have hpz : p powerBase z ≤ 1 := (hp (le_max_left _ _) z).trans hz
  have hqz : p productBase z ≤ 1 := (hp (le_max_right _ _) z).trans hz
  have hχpos := hlχ.trans_le hχvalue.1
  have hVpos := hlV.trans_le hVvalue.1
  have hχscaled : ContDiffAt ℝ ∞
      (fun y => (3 / 2 : ℝ) * extendedRootOddCoefficient G y) x :=
    contDiffAt_const.mul hχ
  have hVscaled : ContDiffAt ℝ ∞ (fun y => δ * V y) x :=
    contDiffAt_const.mul hV
  have hχscaledJet : PointwiseMaterialJetBound p inputLoss
      (fun n => (3 / 2 : ℝ) * A n) z
      (fun y => (3 / 2 : ℝ) * extendedRootOddCoefficient G y) x := by
    simpa only [abs_of_pos hc] using hχjet.const_mul hχ (3 / 2 : ℝ)
  have hVscaledJet : PointwiseMaterialJetBound p inputLoss (fun n => δ * A n) z
      (fun y => δ * V y) x := by
    simpa only [abs_of_pos hδ] using hVjet.const_mul hV δ
  have hχpow : PointwiseMaterialJetBound p powerLoss C z
      (fun y => ((3 / 2 : ℝ) * extendedRootOddCoefficient G y) ^ (a / 6)) x :=
    hχpower z hpz _ x hχscaled
      ⟨mul_le_mul_of_nonneg_left hχvalue.1 hc.le,
        mul_le_mul_of_nonneg_left hχvalue.2 hc.le⟩ (fun n _ => hχscaledJet n)
  have hVpow : PointwiseMaterialJetBound p powerLoss D z
      (fun y => (δ * V y) ^ (-a / 4)) x :=
    hVpower z hpz _ x hVscaled
      ⟨mul_le_mul_of_nonneg_left hVvalue.1 hδ.le,
        mul_le_mul_of_nonneg_left hVvalue.2 hδ.le⟩ (fun n _ => hVscaledJet n)
  have hχpowQ := hχpow.mono hp le_rfl (fun n => (hC n).le)
    (fun n => le_add_of_nonneg_right (hD n).le)
  have hVpowQ := hVpow.mono hp le_rfl (fun n => (hD n).le)
    (fun n => le_add_of_nonneg_left (hC n).le)
  have hraw := hbound z hqz _ _ x
    (hχscaled.rpow_const_of_ne (mul_pos hc hχpos).ne')
    (hVscaled.rpow_const_of_ne (mul_pos hδ hVpos).ne') hχpowQ hVpowQ
  have hnearχ : ∀ᶠ y in 𝓝 x, 0 < extendedRootOddCoefficient G y :=
    hχ.continuousAt.eventually (Ioi_mem_nhds hχpos)
  have hnearV : ∀ᶠ y in 𝓝 x, 0 < V y :=
    hV.continuousAt.eventually (Ioi_mem_nhds hVpos)
  have he : (fun y => ((3 / 2 : ℝ) * extendedRootOddCoefficient G y) ^ (a / 6) *
      (δ * V y) ^ (-a / 4)) =ᶠ[𝓝 x] (fun y => rootDividedHeight δ V G y ^ a) := by
    filter_upwards [hnearχ, hnearV] with y hyχ hyV
    exact (rootDividedHeight_rpow_eq hδ hyV hyχ a).symm
  intro n
  rw [← (he.iteratedFDeriv ℝ n).self_of_nhds]
  exact hraw n

end ContinuousFlexibility.Analysis
