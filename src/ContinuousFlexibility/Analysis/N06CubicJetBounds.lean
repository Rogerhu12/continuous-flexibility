import ContinuousFlexibility.Analysis.N06AngularProductSum
import ContinuousFlexibility.Analysis.N06CubicMultipliers

/-!
# The genuine cubic divergence estimate at every fixed angular order

The actual divergence expression is factored into the five weighted graph
fields. Small spatial coefficient jets through order b + 1 then control
all actual output angular jets through b in the same L² space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

theorem n06_unitCubic_divergence_eq_sum
    {A B C U : PolarPoint → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C) (hU : ContDiff ℝ ∞ U)
    {p : PolarPoint} (hp : p.1 ∈ Icc (0 : ℝ) 1) :
    divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) U p =
      ∑ i, n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p *
        n06CubicGraphFields (fun q => cylinderWeight q.1) U i p := by
  have hd : ContDiff ℝ ∞ (fun q : PolarPoint => cylinderWeight q.1) := by
    change ContDiff ℝ ∞ (fun q : PolarPoint => q.1 * (1 - q.1))
    exact contDiff_fst.mul (contDiff_const.sub contDiff_fst)
  have hdr : radialPartial (fun q => cylinderWeight q.1) p = 1 - 2 * p.1 := by
    rw [← deriv_cylinder_radial_slice (hd.differentiable (by simp)) p.1 p.2]
    exact (cylinderWeight_hasDerivAt p.1).deriv
  have hdt : angularPartial (fun q => cylinderWeight q.1) p = 0 := by
    rw [← deriv_cylinder_angular_slice (hd.differentiable (by simp)) p.1 p.2]
    exact (hasDerivAt_const p.2 (cylinderWeight p.1)).deriv
  rw [n06CubicCoefficients_divergence (hd.differentiable (by simp) p)
    (hA.differentiable (by simp) p) (hB.differentiable (by simp) p)
    (hC.differentiable (by simp) p) (hU.contDiffAt.of_le (by simp)) hdt, hdr]
  exact n06CubicGraphMultipliers_decomposition cylinderWeight (fun r => 1 - 2 * r)
    A B C U p (cylinderWeight_nonneg hp)

/-- The seven coefficient values used by a differentiated divergence are
all among the ordinary spatial jets through b + 1. -/
theorem n06_unitCubicMultipliers_angularJet_abs_le
    {A B C : PolarPoint → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    {b : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {p : PolarPoint} (hp : p.1 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ a j : ℕ, a + j ≤ b + 1 →
      |mixedDerivative a j A p| ≤ δ ∧ |mixedDerivative a j B p| ≤ δ ∧
        |mixedDerivative a j C p| ≤ δ)
    (k : Fin (b + 1)) (i : Fin 5) :
    |mixedDerivative 0 k.val
      (n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i) p| ≤ 5 * δ := by
  have hk := k.isLt
  have h₀ := hcoeff 0 k.val (by omega)
  have hr := hcoeff 1 k.val (by omega)
  have ht := hcoeff 0 (k.val + 1) (by omega)
  have he : |1 - 2 * p.1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hp.1, hp.2]
  rw [n06CubicGraphMultipliers_angularJet cylinderWeight (fun r => 1 - 2 * r)
    hA hB hC k.val i]
  apply n06CubicGraphMultipliers_abs_le cylinderWeight (fun r => 1 - 2 * r)
    (mixedDerivative 0 k.val A) (mixedDerivative 0 k.val B) (mixedDerivative 0 k.val C)
    p (cylinderWeight_nonneg hp) (cylinderWeight_le_one hp) he hδ
    h₀.1 h₀.2.1 h₀.2.2
  · simpa only [radialPartial_mixedDerivative hA, Nat.zero_add] using hr.1
  · simpa only [angularPartial_mixedDerivative hB] using ht.2.1
  · simpa only [radialPartial_mixedDerivative hB, Nat.zero_add] using hr.2.1
  · simpa only [angularPartial_mixedDerivative hC] using ht.2.2

/-- All actual angular output jets of the genuine cubic divergence belong
to the original L² space and have a bound linear in the small coefficient
size after taking square roots. Only source jets through b occur. -/
theorem n06_unitCubic_divergence_angularJet_lp_bound
    {μ : Measure PolarPoint} {A B C U : PolarPoint → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hC : ContDiff ℝ ∞ C) (hU : ContDiff ℝ ∞ U)
    (b : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hstrip : ∀ᵐ p ∂μ, p.1 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ᵐ p ∂μ, ∀ a j : ℕ, a + j ≤ b + 1 →
      |mixedDerivative a j A p| ≤ δ ∧ |mixedDerivative a j B p| ≤ δ ∧
        |mixedDerivative a j C p| ≤ δ)
    (hgraph : ∀ k : Fin (b + 1), ∀ i : Fin 5,
      MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1)
        (mixedDerivative 0 k.val U) i) 2 μ) :
    ∃ hout : ∀ k : Fin (b + 1), MemLp
        (mixedDerivative 0 k.val
          (divergenceOperator (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) U)) 2 μ,
      (∑ k : Fin (b + 1), ‖(hout k).toLp
        (mixedDerivative 0 k.val
          (divergenceOperator (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) U))‖ ^ 2) ≤
        (125 * n06AngularMultiplierCost b * δ ^ 2) *
          ∑ k : Fin (b + 1), ∑ i : Fin 5, ‖(hgraph k i).toLp
            (n06CubicGraphFields (fun p => cylinderWeight p.1) (mixedDerivative 0 k.val U) i)‖ ^ 2 := by
  let M := n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C
  let G := n06CubicGraphFields (fun p => cylinderWeight p.1) U
  let P := divergenceOperator (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) U
  let Q : PolarPoint → ℝ := fun p => ∑ i, M i p * G i p
  have hMmeas (i : Fin 5) (k : Fin (b + 1)) :
      AEStronglyMeasurable (mixedDerivative 0 k.val (M i)) μ := by
    change AEStronglyMeasurable (mixedDerivative 0 k.val
      (n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i)) μ
    rw [n06CubicGraphMultipliers_angularJet cylinderWeight (fun r => 1 - 2 * r)
      hA hB hC k.val i]
    exact (n06CubicGraphMultipliers_continuous cylinderWeight_continuous
      (continuous_const.sub (continuous_const.mul continuous_id))
      (contDiff_mixedDerivative hA 0 k.val) (contDiff_mixedDerivative hB 0 k.val)
      (contDiff_mixedDerivative hC 0 k.val) i).aestronglyMeasurable
  have hGLp (i : Fin 5) (k : Fin (b + 1)) : MemLp (mixedDerivative 0 k.val (G i)) 2 μ := by
    change MemLp (mixedDerivative 0 k.val
      (n06CubicGraphFields (fun p => cylinderWeight p.1) U i)) 2 μ
    rw [n06_cubicGraphFields_angularJet_commute cylinderWeight hU k.val i]
    exact hgraph k i
  have hsmall : ∀ᵐ p ∂μ, ∀ i : Fin 5, ∀ k : Fin (b + 1),
      |mixedDerivative 0 k.val (M i) p| ≤ 5 * δ := by
    filter_upwards [hstrip, hcoeff] with p hp hc
    intro i k
    exact n06_unitCubicMultipliers_angularJet_abs_le hA hB hC hδ hp hc k i
  obtain ⟨hQ, hQbound⟩ := n06_angularJet_sum_mul_lp_bound M G
    (n06CubicGraphMultipliers_slice_smooth cylinderWeight (fun r => 1 - 2 * r) hA hB hC)
    (n06CubicGraphFields_slice_smooth cylinderWeight hU) b
    (by linarith only [hδ] : 0 ≤ 5 * δ) hMmeas hGLp hsmall
  have hjetAE (k : Fin (b + 1)) :
      mixedDerivative 0 k.val P =ᵐ[μ] mixedDerivative 0 k.val Q := by
    filter_upwards [hstrip] with p hp
    have hs : (fun θ => P (p.1, θ)) = (fun θ => Q (p.1, θ)) := by
      funext θ
      exact n06_unitCubic_divergence_eq_sum hA hB hC hU hp
    simpa only [mixedDerivative, iteratedDeriv_zero] using
      congrArg (fun f : ℝ → ℝ => iteratedDeriv k.val f p.2) hs
  let hout (k : Fin (b + 1)) : MemLp (mixedDerivative 0 k.val P) 2 μ :=
    (memLp_congr_ae (hjetAE k)).mpr (hQ k)
  have hnorm (k : Fin (b + 1)) :
      ‖(hout k).toLp (mixedDerivative 0 k.val P)‖ ^ 2 =
        ‖(hQ k).toLp (mixedDerivative 0 k.val Q)‖ ^ 2 := by
    rw [r11b_norm_toLp_sq, r11b_norm_toLp_sq]
    exact integral_congr_ae ((hjetAE k).mono (fun _ hp => congrArg (fun x : ℝ => x ^ 2) hp))
  have hGnorm (i : Fin 5) (k : Fin (b + 1)) :
      ‖(hGLp i k).toLp (mixedDerivative 0 k.val (G i))‖ ^ 2 =
        ‖(hgraph k i).toLp (n06CubicGraphFields (fun p => cylinderWeight p.1)
          (mixedDerivative 0 k.val U) i)‖ ^ 2 := by
    have heq : mixedDerivative 0 k.val (G i) =
        n06CubicGraphFields (fun p => cylinderWeight p.1) (mixedDerivative 0 k.val U) i :=
      n06_cubicGraphFields_angularJet_commute cylinderWeight hU k.val i
    rw [r11b_norm_toLp_sq, r11b_norm_toLp_sq, heq]
  refine ⟨hout, ?_⟩
  calc
    _ = ∑ k : Fin (b + 1), ‖(hQ k).toLp (mixedDerivative 0 k.val Q)‖ ^ 2 :=
      Finset.sum_congr rfl (fun k _ => hnorm k)
    _ ≤ ((Fintype.card (Fin 5) : ℝ) * n06AngularMultiplierCost b * (5 * δ) ^ 2) *
        ∑ i : Fin 5, ∑ k : Fin (b + 1),
          ‖(hGLp i k).toLp (mixedDerivative 0 k.val (G i))‖ ^ 2 := hQbound
    _ = _ := by
      simp_rw [hGnorm]
      rw [Finset.sum_comm]
      norm_num only [Fintype.card_fin, Nat.cast_ofNat]
      ring

end ContinuousFlexibility.Analysis
