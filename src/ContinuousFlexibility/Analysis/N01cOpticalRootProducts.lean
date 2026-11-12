import ContinuousFlexibility.Analysis.N01cOpticalMixedJets
import ContinuousFlexibility.Analysis.N01cProfileMajorantWeights

/-!
# Weighted Leibniz products of the actual optical-root jets

Every term keeps its own spatial derivative allocation. The k linear
parameter factors restore the k endpoint powers reserved in the outer
real-power estimate. A nonempty parameter product retains exactly one
height weight; the remaining height factors use their scalar bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem weighted_radialLeibniz_bound
    (k n : ℕ) (f : Fin (k + 1) → ℝ → ℝ) (r : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) r)
    (M : Fin (k + 1) → ℕ → ℝ)
    (hM : ∀ i j, j ≤ n → δ ^ j * |iteratedDeriv j (f i) r| ≤ M i j) :
    δ ^ n * |iteratedDeriv n (fun s => ∏ i, f i s) r| ≤
      ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) *
        ∏ i, M i (radialLeibnizOrders k n d i) := by
  rw [iteratedDeriv_finProduct_eq_radialLeibniz k n f r hf]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hδ n)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), Finset.abs_prod]
  have he : δ ^ n * ∏ i, |iteratedDeriv (radialLeibnizOrders k n d i) (f i) r| =
      ∏ i, δ ^ radialLeibnizOrders k n d i *
        |iteratedDeriv (radialLeibnizOrders k n d i) (f i) r| := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, radialLeibnizOrders_sum]
  calc
    _ = (radialLeibnizCoefficient k n d : ℝ) *
        (δ ^ n * ∏ i, |iteratedDeriv (radialLeibnizOrders k n d i) (f i) r|) := by ring
    _ = _ := congrArg (fun a : ℝ => (radialLeibnizCoefficient k n d : ℝ) * a) he
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀
        (fun i _ => mul_nonneg (pow_nonneg hδ _) (abs_nonneg _))
        (fun i _ => hM i _ (radialLeibnizOrders_le k n d i))) (Nat.cast_nonneg _)

def endpointRootProductMajorant (c M : ℝ) (A B : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) *
    endpointPowerCompositionMajorant c M A k (radialLeibnizOrders k n d 0) *
      ∏ i : Fin k, B (radialLeibnizOrders k n d i.succ)

theorem endpointRootProductMajorant_nonneg {c M : ℝ} (hc : 0 ≤ c)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (k n : ℕ) :
    0 ≤ endpointRootProductMajorant c M A B k n :=
  Finset.sum_nonneg (fun d _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (endpointPowerCompositionMajorant_nonneg hc A hA k _))
      (Finset.prod_nonneg (fun i _ => hB _)))

/-- The full spatial product behind a positive parameter jet. The
direction factors pᵢ stay multilinear and a single height factor survives. -/
theorem endpoint_opticalProduct_bound
    {q : ℝ → ℝ} {r δ c M H R : ℝ}
    (hq : ContDiffAt ℝ ∞ q r) (hδ : 0 < δ) (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : c * δ ≤ q r) (hupper : q r ≤ M * δ)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (k n : ℕ) (hk : 0 < k) (f : Fin k → ℝ → ℝ)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) r)
    (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (hH : 0 ≤ H) (hHR : H ≤ R)
    (hjetq : ∀ j, j ≤ n → δ ^ j * |iteratedDeriv j q r| ≤ δ * A j)
    (hjetf : ∀ i j, j ≤ n → δ ^ j * |iteratedDeriv j (f i) r| ≤
      δ * B j * H * p i) :
    δ ^ n * |iteratedDeriv n
        (fun s => q s ^ ((1 / 2 : ℝ) - (k : ℝ)) * ∏ i, f i s) r| ≤
      (Real.sqrt δ * endpointRootProductMajorant c M A B k n) *
        (H * R ^ (k - 1)) * ∏ i, p i := by
  have hqpos : 0 < q r := (mul_pos hc hδ).trans_le hlower
  let F : Fin (k + 1) → ℝ → ℝ :=
    Fin.cons (fun s => q s ^ ((1 / 2 : ℝ) - (k : ℝ))) f
  let W : Fin (k + 1) → ℕ → ℝ :=
    Fin.cons (fun j => (Real.sqrt δ / δ ^ k) * endpointPowerCompositionMajorant c M A k j)
      (fun i j => δ * B j * H * p i)
  have hF : ∀ i, ContDiffAt ℝ ∞ (F i) r := by
    intro i
    refine Fin.cases ?_ (fun j => hf j) i
    exact (Real.contDiffAt_rpow_const_of_ne hqpos.ne').comp r hq
  have hW : ∀ i j, j ≤ n → δ ^ j * |iteratedDeriv j (F i) r| ≤ W i j := by
    intro i
    refine Fin.cases ?_ (fun l j hj => hjetf l j hj) i
    intro j hj
    have hb := endpoint_rpowComposition_radial_bound hq hδ hc hM hlower hupper A hA k j
      (fun a ha => hjetq a (ha.trans hj))
    change δ ^ j * |iteratedDeriv j (fun s => q s ^ ((1 / 2 : ℝ) - (k : ℝ))) r| ≤
      (Real.sqrt δ / δ ^ k) * endpointPowerCompositionMajorant c M A k j
    have hcanc : (δ ^ j * |iteratedDeriv j
        (fun s => q s ^ ((1 / 2 : ℝ) - (k : ℝ))) r|) * δ ^ k ≤
        Real.sqrt δ * endpointPowerCompositionMajorant c M A k j := by
      simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hb
    have he : Real.sqrt δ * endpointPowerCompositionMajorant c M A k j =
        ((Real.sqrt δ / δ ^ k) * endpointPowerCompositionMajorant c M A k j) * δ ^ k := by
      field_simp [pow_ne_zero k hδ.ne']
    exact le_of_mul_le_mul_right (hcanc.trans_eq he) (pow_pos hδ k)
  have hraw := weighted_radialLeibniz_bound k n F r hδ.le hF W hW
  have hfun : (fun s => ∏ i, F i s) =
      (fun s => q s ^ ((1 / 2 : ℝ) - (k : ℝ)) * ∏ i, f i s) := by
    funext s
    simp only [F, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [hfun] at hraw
  have hpow : H ^ k ≤ H * R ^ (k - 1) := by
    cases k with
    | zero => omega
    | succ k =>
        simp only [pow_succ, Nat.succ_sub_one]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH hHR k) hH
  have hp₀ : 0 ≤ ∏ i, p i := Finset.prod_nonneg (fun i _ => hp i)
  have hprod (d : RadialLeibnizIndex k n) :
      ∏ i, W i (radialLeibnizOrders k n d i) =
        Real.sqrt δ * endpointPowerCompositionMajorant c M A k (radialLeibnizOrders k n d 0) *
          (∏ i : Fin k, B (radialLeibnizOrders k n d i.succ)) * H ^ k * ∏ i, p i := by
    rw [Fin.prod_univ_succ]
    simp only [W, Fin.cons_zero, Fin.cons_succ, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp [pow_ne_zero k hδ.ne']
    <;> ring
  apply hraw.trans
  simp_rw [hprod]
  have he : (∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) *
      (Real.sqrt δ * endpointPowerCompositionMajorant c M A k (radialLeibnizOrders k n d 0) *
        (∏ i : Fin k, B (radialLeibnizOrders k n d i.succ)) * H ^ k * ∏ i, p i)) =
      (Real.sqrt δ * endpointRootProductMajorant c M A B k n) * H ^ k * ∏ i, p i := by
    rw [endpointRootProductMajorant, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg (Real.sqrt_nonneg _)
      (endpointRootProductMajorant_nonneg hc.le A B hA hB k n))) hp₀

/-- The weighted product bound applies to the actual radial/parameter
tower, with the actual spatial directions of the affine optical square. -/
theorem affineOpticalRadialJetSmoothDirections_endpoint_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (L : E →L[ℝ] ℝ) {I : Set ℝ} (hI : IsOpen I) {q₀ g : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q₀ I) (hg : ContDiffOn ℝ ∞ g I)
    (n k : ℕ) (hk : 0 < k) (r : ℝ) (hr : r ∈ I) {U : Set E} (hU : IsOpen U)
    (hpos : ∀ x ∈ U, 0 < q₀ r + L x * g r) {x : E} (hx : x ∈ U)
    (v : Fin k → E) {δ c M H R : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : c * δ ≤ q₀ r + L x * g r)
    (hupper : q₀ r + L x * g r ≤ M * δ)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (hH : 0 ≤ H) (hHR : H ≤ R)
    (hjetq : ∀ j, j ≤ n → δ ^ j *
      |iteratedDeriv j (fun s => q₀ s + L x * g s) r| ≤ δ * A j)
    (hjetf : ∀ i j, j ≤ n → δ ^ j *
      |iteratedDeriv j (fun s => L (v i) * g s) r| ≤ δ * B j * H * p i) :
    δ ^ n * |(affineOpticalRadialJetSmoothDirections L hI hq hg n r hr hU hpos).D k x v| ≤
      (|rpowJetCoefficient (1 / 2) k| * Real.sqrt δ *
        endpointRootProductMajorant c M A B k n) * (H * R ^ (k - 1)) * ∏ i, p i := by
  rw [affineOpticalRadialJetSmoothDirections_D_apply L hI hq hg n k r hr hU hpos hx v,
    abs_mul]
  have hQ : ContDiffAt ℝ ∞ (fun s => q₀ s + L x * g s) r :=
    (hq.contDiffAt (hI.mem_nhds hr)).add
      (contDiffAt_const.mul (hg.contDiffAt (hI.mem_nhds hr)))
  have hf : ∀ i : Fin k, ContDiffAt ℝ ∞ (fun s => L (v i) * g s) r :=
    fun _ => contDiffAt_const.mul (hg.contDiffAt (hI.mem_nhds hr))
  have hb := endpoint_opticalProduct_bound hQ hδ hc hM hlower hupper A B hA hB k n hk
    (fun i s => L (v i) * g s) hf p hp hH hHR hjetq hjetf
  calc
    _ = |rpowJetCoefficient (1 / 2) k| *
        (δ ^ n * |iteratedDeriv n
          (fun s => (q₀ s + L x * g s) ^ ((1 / 2 : ℝ) - (k : ℝ)) *
            ∏ i, L (v i) * g s) r|) := by ring
    _ ≤ |rpowJetCoefficient (1 / 2) k| *
        ((Real.sqrt δ * endpointRootProductMajorant c M A B k n) *
          (H * R ^ (k - 1)) * ∏ i, p i) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
