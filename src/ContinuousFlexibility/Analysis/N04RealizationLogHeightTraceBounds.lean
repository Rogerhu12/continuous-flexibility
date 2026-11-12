import ContinuousFlexibility.Analysis.N04RealizationAngularTraceBounds
import ContinuousFlexibility.Analysis.N04RealizationLogCompositionBounds
import ContinuousFlexibility.Analysis.N04RealizationFiniteProductScale

/-!
# Quantitative parameter jets of the actual finite logarithmic traces

The genuine raw height-axis towers through the fixed radial degree are
the only derivative inputs. The existing radial logarithm formula is
estimated term by term, with every angular order distributed before
products are formed. Thus the fixed radial degree never multiplies the
angular interpolation cost, and the same parameter domain is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_logHeightTrace_parameter_bound (n k b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (U : Set X), IsOpen U → ∀ (f : X → PolarPoint → ℝ) (c : ℝ),
      (∀ y ∈ U, ∀ θ, ContDiffAt ℝ ∞ (f y) (c, θ)) →
      (∀ y ∈ U, ∀ θ, 0 < f y (c, θ)) →
      ∀ J : ∀ j : ℕ, j ≤ n → ∀ a θ,
        SmoothDirections U (fun y => iteratedDeriv a (radialBoundaryJet (f y) c j) θ),
      ∀ θ, ∀ JL : SmoothDirections U (fun y => iteratedDeriv b
        (radialBoundaryJet (fun p => Real.log (f y p)) c n) θ),
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ H M t : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ t → (f x (c, θ))⁻¹ ≤ M →
      (∀ j : ℕ, ∀ hj : j ≤ n, ∀ l : ℕ, l ≤ k → ∀ a : ℕ, a ≤ b →
        ∀ z : Fin l → X, (∀ i, P (z i)) →
        ‖(J j hj a θ).D l x z‖ ≤ M * parameterHeightWeight H l * t ^ a) →
      ‖JL.D k x v‖ ≤ B * M ^ d * parameterHeightWeight H k * t ^ b := by
  classical
  obtain ⟨C0, d0, hC0, hd0, hb0⟩ := n04Realization_logComposition_prefix_bound
    (X := X) n k b RH
  choose cp hcp hcpb using fun π : OrderedFinpartition n =>
    n04Realization_finiteProduct_scale_bound (X := X) (π.length + 1) k 0 b RH
  let Cp : ℝ := 1 + ∑ π : OrderedFinpartition n, cp π
  have hCp : 1 ≤ Cp := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun π _ => (hcp π).le))
  have hcpCp (π : OrderedFinpartition n) : cp π ≤ Cp :=
    (Finset.single_le_sum (fun σ _ => (hcp σ).le) (Finset.mem_univ π)).trans
      (le_add_of_nonneg_left zero_le_one)
  let Q : ℝ := 1 + (Fintype.card (OrderedFinpartition n) : ℝ)
  have hQ : 1 ≤ Q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  refine ⟨Q * Cp * C0 ^ (n + 1), d0 * (n + 1),
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hQ hCp)
      (one_le_pow₀ hC0),
    by simpa only [Nat.one_mul] using Nat.mul_le_mul hd0 (Nat.succ_pos n), ?_⟩
  intro U hU f c hroot hpos J θ JL x hx P v hv H M t hH hHR hM ht hinv hraw
  let q : PolarPoint := (0, θ)
  let F : Fin (n + 1) → X → PolarPoint → ℝ :=
    fun j y p => radialBoundaryJet (f y) c j.val p.2
  let RF : ∀ j, MixedJetRegularity U univ (F j) := fun j =>
    n04Realization_angularField_mixedJetRegularity hU
      (fun y hy => contDiff_radialBoundaryJet_of_contDiffAt c (hroot y hy) j.val)
      (J j.val (Nat.le_of_lt_succ j.isLt))
  have hsource (i : Fin (n + 1)) (l : ℕ) (hl : l ≤ k) (u w : ℕ) (huw : u + w ≤ b)
      (z : Fin l → X) (hz : ∀ j, P (z j)) :
      ‖((RF i).parameter u w q (mem_univ _)).D l x z‖ ≤
        M * parameterHeightWeight H l * t ^ (u + w) :=
    n04Realization_angularTrace_jet_bound ((RF i).parameter u w q (mem_univ _))
      (J i.val (Nat.le_of_lt_succ i.isLt) w θ) hx z
      (zero_le_one.trans hM) hH (zero_le_one.trans ht)
      (hraw i.val (Nat.le_of_lt_succ i.isLt) l hl w (by omega) z hz)
  have hpos0 (y : X) (hy : y ∈ U) (p : PolarPoint) (_hp : p ∈ (univ : Set PolarPoint)) :
      0 < F 0 y p := by
    simpa only [F, Fin.val_zero, radialBoundaryJet, iteratedDeriv_zero] using hpos y hy p.2
  have hinv0 : (F 0 x q)⁻¹ ≤ M := by
    simpa only [F, Fin.val_zero, radialBoundaryJet, iteratedDeriv_zero, q] using hinv
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    fun y hy => (Real.contDiffAt_log.mpr hy.ne').contDiffWithinAt
  let RO (m : ℕ) := (RF 0).scalarComp hU isOpen_univ isOpen_Ioi
    (contDiffOn_iteratedDeriv_open isOpen_Ioi hlog m) hpos0
  let index (π : OrderedFinpartition n) (i : Fin π.length) : Fin (n + 1) :=
    ⟨π.partSize i, Nat.lt_succ_of_le (π.partSize_le i)⟩
  let FF (π : OrderedFinpartition n) : Fin (π.length + 1) → X → PolarPoint → ℝ :=
    Fin.cons (fun y p => iteratedDeriv π.length Real.log (F 0 y p))
      (fun i => F (index π i))
  let RFF (π : OrderedFinpartition n) : ∀ i, MixedJetRegularity U univ (FF π i) :=
    Fin.cases (RO π.length) (fun i => RF (index π i))
  let RP (π : OrderedFinpartition n) :
      MixedJetRegularity U univ (fun y p => ∏ i, FF π i y p) :=
    MixedJetRegularity.finiteComp (RFF π) hU isOpen_univ isOpen_univ
      (G := fun a : Fin (π.length + 1) → ℝ => ∏ i, a i)
      (contDiffOn_prod (fun i _ => (contDiff_apply ℝ ℝ i).contDiffOn))
      (fun _ _ _ _ => mem_univ _)
  let JT (π : OrderedFinpartition n) := (RP π).parameter 0 b q (mem_univ _)
  let M1 : ℝ := C0 * M ^ d0
  have hM1 : 1 ≤ M1 := one_le_mul_of_one_le_of_one_le hC0 (one_le_pow₀ hM)
  have hMpow : M ≤ M ^ d0 := by
    simpa only [pow_one] using pow_le_pow_right₀ hM hd0
  have hMM1 : M ≤ M1 := hMpow.trans
    (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hM) _) hC0)
  let W : ℝ := parameterHeightWeight H k * t ^ b
  have hW : 0 ≤ W := mul_nonneg (parameterHeightWeight_nonneg hH k)
    (pow_nonneg (zero_le_one.trans ht) _)
  have hterm (π : OrderedFinpartition n) :
      ‖(JT π).D k x v‖ ≤ Cp * M1 ^ (n + 1) * W := by
    have hinputs : ∀ i : Fin (π.length + 1), ∀ l : ℕ, l ≤ k →
        ∀ u w : ℕ, u + w ≤ 0 + b → ∀ z : Fin l → X, (∀ j, P (z j)) →
        ‖((RFF π i).parameter u w q (mem_univ _)).D l x z‖ ≤
          M1 * parameterHeightWeight H l * t ^ (u + w) := by
      refine Fin.cases ?_ (fun i => ?_)
      · intro l hl u w huw z hz
        exact hb0 U hU univ isOpen_univ (F 0) (RF 0) hpos0 q (mem_univ _) x hx P
          H M t hH hHR hM ht hinv0 (hsource 0) π.length π.length_le l hl
          u w (by omega) ((RO π.length).parameter u w q (mem_univ _)) z hz
      · intro l hl u w huw z hz
        exact (hsource (index π i) l hl u w (by omega) z hz).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hMM1 (parameterHeightWeight_nonneg hH l))
            (pow_nonneg (zero_le_one.trans ht) _))
    have h := hcpb π U hU univ isOpen_univ (FF π) (RFF π) q (mem_univ _)
      (JT π) x hx P v hv H M1 t hH hHR hM1 ht hinputs
    have hcoef : cp π * M1 ^ (π.length + 1) ≤ Cp * M1 ^ (n + 1) :=
      mul_le_mul (hcpCp π) (pow_le_pow_right₀ hM1 (by have hh := π.length_le; omega))
        (pow_nonneg (zero_le_one.trans hM1) _) (zero_le_one.trans hCp)
    have h' : ‖(JT π).D k x v‖ ≤ cp π * M1 ^ (π.length + 1) * W := by
      simpa only [W, Nat.zero_add, mul_assoc] using h
    exact h'.trans (mul_le_mul_of_nonneg_right hcoef hW)
  have hformula (y : X) (hy : y ∈ U) :
      iteratedDeriv b (radialBoundaryJet (fun p => Real.log (f y p)) c n) θ =
        ∑ π : OrderedFinpartition n, mixedDerivative 0 b (fun p => ∏ i, FF π i y p) q := by
    have heq : radialBoundaryJet (fun p => Real.log (f y p)) c n =
        (fun η => ∑ π : OrderedFinpartition n, ∏ i, FF π i y (0, η)) := by
      funext η
      simpa only [FF, F, index, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.val_zero, radialBoundaryJet, iteratedDeriv_zero] using
        n04Realization_log_radialBoundaryJet (hroot y hy η) (hpos y hy η) n
    have hreg (π : OrderedFinpartition n) :
        ContDiffAt ℝ (b : ℕ∞ω) (fun η => ∏ i, FF π i y (0, η)) θ :=
      (((RP π).spatial y hy).contDiffAt (isOpen_univ.mem_nhds (mem_univ q))).comp θ
        (contDiffAt_const.prodMk contDiffAt_id) |>.of_le (by simp)
    rw [heq, iteratedDeriv_fun_sum (fun π _ => hreg π)]
    simp only [mixedDerivative, iteratedDeriv_zero, q]
  have hd := smoothDirections_D_eq_linearCombination JL JT (fun _ => 1)
    (fun y hy => by simpa only [one_mul] using hformula y hy) k hx v
  calc
    _ ≤ ∑ π : OrderedFinpartition n, ‖(JT π).D k x v‖ := by
      rw [hd]
      simpa only [one_mul] using norm_sum_le (Finset.univ : Finset (OrderedFinpartition n))
        (fun π => (1 : ℝ) * (JT π).D k x v)
    _ ≤ ∑ _π : OrderedFinpartition n, Cp * M1 ^ (n + 1) * W :=
      Finset.sum_le_sum (fun π _ => hterm π)
    _ ≤ Q * (Cp * M1 ^ (n + 1) * W) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
        (mul_nonneg (mul_nonneg (zero_le_one.trans hCp)
          (pow_nonneg (zero_le_one.trans hM1) _)) hW)
    _ = _ := by
      dsimp only [M1, W]
      rw [mul_pow, ← pow_mul]
      ring

end ContinuousFlexibility.Analysis
