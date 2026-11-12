import ContinuousFlexibility.Analysis.N01cPhysicalLieParameterJets
import ContinuousFlexibility.Analysis.N01cPhysicalLieProducts
import ContinuousFlexibility.Analysis.N01cEndpointMixedPowerAlgebra

/-!
# Distributed endpoint bounds for the actual physical Lie jets

The finite word formula is evaluated with genuine parameter towers.
Each speed factor keeps its own radial endpoint power and total spatial
order. Their product retains one height factor at positive parameter
order; the remaining endpoint power uses only the fixed component width.
The outer angle is unrestricted throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Every actual angular Lie jet has the exact distributed spatial power
before composition with the flow graph and before multilinear normalization. -/
theorem endpointMixedPowerBounds_physicalLieAngular
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
    {f : I → X → PolarPoint → ℝ}
    (hU : IsOpen U) (hΩ : ∀ m, IsOpen (Ω m))
    (F : ∀ m, MixedJetRegularity U (Ω m) (f m))
    (hf : EndpointMixedPowerBounds p center base loss U Ω δ H E f)
    (hδ : ∀ m q, q ∈ Ω m → 0 ≤ δ m q)
    {width : ℝ} (hwidth : ∀ m q, q ∈ Ω m → δ m q ≤ width)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q)
    {RH : ℝ} (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q ∧ H m q ≤ RH)
    (n b k s : ℕ) (hns : n + b ≤ s) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ m q, q ∈ Ω m →
      ∀ J : SmoothDirections U
        (fun x => mixedDerivative 0 b (physicalFlowLieJet (f m x) n) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 →
      ∀ v : Fin k → X, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (s + loss) (x - center) ≤ R →
        (∀ i, p (s + loss) (v i) ≤ R) →
        δ m q ^ (n + 1) * ‖J.D k x v‖ ≤
          C * E m q ^ A * parameterHeightWeight (H m q) k *
            R ^ (((n + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  classical
  obtain ⟨Cf, Af, hCf, hAf, hfb⟩ := hf k s
  let e := physicalLieAngularExpansion n b
  choose Cp hCp hproduct using
    (fun t : e.Index => exists_n01c_scaled_finiteProduct_parameterJet_bound
      (X := X) (e.arity t) k RH)
  let C0 : ℝ := (∑ t : e.Index, Cp t) * Cf ^ (n + 1) * (max 1 width) ^ (n + 1)
  have hC0 : 0 ≤ C0 :=
    mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun t _ => (hCp t).le))
      (pow_nonneg (zero_le_one.trans hCf) _))
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  refine ⟨1 + C0, Af * ((n + 1 : ℕ) : ℝ), by linarith,
    mul_nonneg hAf (Nat.cast_nonneg _), ?_⟩
  intro m q hq J x hx hlow v hv R hR hhigh hvhigh
  have hEpos : 0 < E m q := zero_lt_one.trans_le (hE m q hq)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let terms : e.Index → X → ℝ := fun t y =>
    ∏ i, mixedDerivative (e.words t i).radialOrder (e.words t i).angularOrder (f m y) q
  let JT : ∀ t, SmoothDirections U (terms t) := fun t =>
    smoothDirections_finiteProduct hU (fun i =>
      (F m).parameter (e.words t i).radialOrder (e.words t i).angularOrder q hq)
  let W : ℝ := E m q ^ (Af * ((n + 1 : ℕ) : ℝ)) * parameterHeightWeight (H m q) k *
    R ^ (((n + b : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hW : 0 ≤ W := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hEpos.le _)
      (parameterHeightWeight_nonneg (hH m q hq).1 k))
    (Real.rpow_nonneg hRpos.le _)
  have hterm (t : e.Index) :
      δ m q ^ (n + 1) * ‖(JT t).D k x v‖ ≤
        (Cp t * Cf ^ (n + 1) * (max 1 width) ^ (n + 1)) * W := by
    let α : Fin (e.arity t) → ℕ := fun i => (e.words t i).radialOrder
    let β : Fin (e.arity t) → ℕ := fun i => (e.words t i).angularOrder
    let fi : Fin (e.arity t) → X → ℝ :=
      fun i y => mixedDerivative (α i) (β i) (f m y) q
    let Ji : ∀ i, SmoothDirections U (fi i) :=
      fun i => (F m).parameter (α i) (β i) q hq
    let ci : Fin (e.arity t) → ℝ := fun i => δ m q ^ α i
    let Bi : Fin (e.arity t) → ℝ := fun i =>
      Cf * E m q ^ Af * R ^ (((e.words t i).order : ℝ) / ((s : ℝ) + 1))
    have hci (i : Fin (e.arity t)) : 0 ≤ ci i := pow_nonneg (hδ m q hq) _
    have hBi (i : Fin (e.arity t)) : 0 < Bi i :=
      mul_pos (mul_pos (zero_lt_one.trans_le hCf) (Real.rpow_pos_of_pos hEpos _))
        (Real.rpow_pos_of_pos hRpos _)
    have horder (i : Fin (e.arity t)) : α i + β i ≤ s := by
      change (e.words t i).radialOrder + (e.words t i).angularOrder ≤ s
      rw [PhysicalLieWord.radialOrder_add_angularOrder]
      exact (Finset.single_le_sum (f := fun j => (e.words t j).order)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
          ((e.total_order t).le.trans hns)
    have hbase (i : Fin (e.arity t)) : ci i * ‖fi i x‖ ≤ Bi i := by
      have hh := hfb m 0 (Nat.zero_le k) (α i) (β i) (horder i) q hq (Ji i)
        x hx hlow Fin.elim0 (fun j => j.elim0) R hR hhigh (fun j => j.elim0)
      simpa only [smoothDirections_D_zero_apply (Ji i) hx, parameterHeightWeight,
        ite_true, mul_one, ci, Bi, fi, α, β, PhysicalLieWord.radialOrder_add_angularOrder] using hh
    have hjet (i : Fin (e.arity t)) (d : OrderedFinpartition k) (j : Fin d.length) :
        ci i * ‖(Ji i).D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H m q * Bi i := by
      have hh := hfb m (d.partSize j) (d.partSize_le j) (α i) (β i) (horder i)
        q hq (Ji i) x hx hlow (v ∘ d.emb j) (fun l => hv _)
        R hR hhigh (fun l => hvhigh _)
      have he : α i + β i = (e.words t i).order :=
        PhysicalLieWord.radialOrder_add_angularOrder _
      calc
        _ ≤ Cf * E m q ^ Af * H m q *
            R ^ (((e.words t i).order : ℝ) / ((s : ℝ) + 1)) := by
          simpa only [ci, parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos j)),
            he] using hh
        _ = H m q * Bi i := by dsimp only [Bi]; ring
    have hscaled :
        δ m q ^ (∑ i, α i) * ‖(JT t).D k x v‖ ≤
          Cp t * parameterHeightWeight (H m q) k * ∏ i, Bi i := by
      simpa only [ci, Finset.prod_pow_eq_pow_sum] using
        hproduct t Ji (JT t) x hx (H m q) (hH m q hq).1 (hH m q hq).2
          ci hci Bi hBi hbase v hjet
    have hprod :
        (∏ i, Bi i) ≤ Cf ^ (n + 1) * E m q ^ (Af * ((n + 1 : ℕ) : ℝ)) *
          R ^ (((n + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      simpa only [Bi, e.total_order t] using
        n01c_finiteProduct_spatialEnvelope (e.arity_le t)
          (fun i => (e.words t i).order) s hCf (hE m q hq) hAf hR
    have hrad : (∑ i, α i) ≤ n + 1 :=
      (e.radial_order_le t).trans (Nat.le_succ n)
    calc
      _ ≤ (max 1 width) ^ (n + 1) * (δ m q ^ (∑ i, α i) * ‖(JT t).D k x v‖) :=
        n01c_endpoint_power_raise (hδ m q hq) (hwidth m q hq) (norm_nonneg _) hrad
      _ ≤ (max 1 width) ^ (n + 1) *
          (Cp t * parameterHeightWeight (H m q) k * ∏ i, Bi i) :=
        mul_le_mul_of_nonneg_left hscaled (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
      _ ≤ (max 1 width) ^ (n + 1) *
          (Cp t * parameterHeightWeight (H m q) k *
            (Cf ^ (n + 1) * E m q ^ (Af * ((n + 1 : ℕ) : ℝ)) *
              R ^ (((n + b : ℕ) : ℝ) / ((s : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hprod
            (mul_nonneg (hCp t).le (parameterHeightWeight_nonneg (hH m q hq).1 k)))
          (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
      _ = _ := by dsimp only [W]; ring
  have hd : J.D k x v = ∑ t : e.Index, (JT t).D k x v := by
    simpa only [one_mul] using
      smoothDirections_D_eq_linearCombination J JT (fun _ => 1)
        (fun y hy => by
          simpa only [one_mul] using
            angularPhysicalFlowLieJet_eq_sum_mixedDerivative
              (hΩ m) ((F m).spatial y hy) n b hq) k hx v
  calc
    _ ≤ δ m q ^ (n + 1) * ∑ t : e.Index, ‖(JT t).D k x v‖ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (hδ m q hq) _)
      rw [hd]
      exact norm_sum_le (Finset.univ : Finset e.Index) (fun t => (JT t).D k x v)
    _ = ∑ t : e.Index, δ m q ^ (n + 1) * ‖(JT t).D k x v‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ t : e.Index,
        (Cp t * Cf ^ (n + 1) * (max 1 width) ^ (n + 1)) * W :=
      Finset.sum_le_sum (fun t _ => hterm t)
    _ = C0 * W := by simp only [C0, Finset.sum_mul]
    _ ≤ (1 + C0) * E m q ^ (Af * ((n + 1 : ℕ) : ℝ)) * parameterHeightWeight (H m q) k *
        R ^ (((n + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      simpa only [W, mul_assoc] using
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one : C0 ≤ 1 + C0) hW

end ContinuousFlexibility.Analysis
