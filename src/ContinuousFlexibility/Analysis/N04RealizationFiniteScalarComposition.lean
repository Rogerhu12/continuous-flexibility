module

public import ContinuousFlexibility.Analysis.N01cMixedPowerComposition

/-!
# Finite scalar composition with the original spatial order

The existing mixed partition formula and genuine parameter product
rule are used at one finite prefix. A scalar outer kernel is charged
only through its derivatives at the actual value. The spatial scale
keeps its exact total order, and one positive parameter height factor
survives. No common parameter-order loss is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- All constants are selected before the domain, scalar fields,
admissible directions, point, or numerical envelopes. Only the source
jets which occur in the finite spatial and parameter partitions enter. -/
theorem n04Realization_finiteScalarComposition_bound (k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ (V : Set ℝ), IsOpen V → ∀ (f : X → PolarPoint → ℝ) (g : ℝ → ℝ),
      ∀ F : MixedJetRegularity U Ω f, ContDiffOn ℝ ∞ g V →
      (∀ y ∈ U, MapsTo (f y) Ω V) →
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun y => mixedDerivative a b (fun p => g (f y p)) q),
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ H M t : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ t →
      (∀ m : ℕ, m ≤ a + b → ∀ j : ℕ, j ≤ k →
        ‖iteratedFDeriv ℝ j (iteratedDeriv m g) (f x q)‖ ≤ M) →
      (∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ a + b →
        ∀ z : Fin j → X, (∀ i, P (z i)) →
        ‖((F.parameter u w q hq).D j x z)‖ ≤
          M * parameterHeightWeight H j * t ^ (u + w)) →
      ‖J.D k x v‖ ≤ B * M ^ (k + a + b + 1) *
        parameterHeightWeight H k * t ^ (a + b) := by
  classical
  let PP : ℝ := 1 + ∑ j : Fin (k + 1),
    (Fintype.card (OrderedFinpartition j.val) : ℝ)
  have hPP : 1 ≤ PP := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg (α := ℝ) _))
  have hcard (j : ℕ) (hj : j ≤ k) :
      (Fintype.card (OrderedFinpartition j) : ℝ) ≤ PP := by
    have hh : (Fintype.card (OrderedFinpartition j) : ℝ) ≤
        ∑ i : Fin (k + 1), (Fintype.card (OrderedFinpartition i.val) : ℝ) :=
      Finset.single_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin (k + 1)))) =>
          Nat.cast_nonneg (α := ℝ) (Fintype.card (OrderedFinpartition i.val)))
        (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1)))
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  choose cp hcp hcpb using fun i : Fin (a + b + 2) =>
    exists_finiteProduct_allParameterJet_bound (X := X) i.val k RH
  let Cp : ℝ := 1 + ∑ i : Fin (a + b + 2), cp i
  have hCp : 1 ≤ Cp := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => (hcp i).le))
  have hcpCp (i : Fin (a + b + 2)) : cp i ≤ Cp :=
    (Finset.single_le_sum (fun j _ => (hcp j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  let C0 : ℝ := PP * (max 1 RH) ^ k
  have hC0 : 1 ≤ C0 := one_le_mul_of_one_le_of_one_le hPP
    (one_le_pow₀ (le_max_left _ _))
  let Q : ℝ := 1 + (Fintype.card (OrderedFinpartition (a + b)) : ℝ)
  have hQ : 1 ≤ Q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  refine ⟨Q * Cp * C0, one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hQ hCp) hC0, ?_⟩
  intro U hU Ω hΩ V hV f g F hg hmap q hq J x hx P v hv H M t hH hHR hM ht
    houter hsource
  let J0 : SmoothDirections U (fun y => f y q) :=
    (F.parameter 0 0 q hq).congr
      (fun y _ => by simp only [mixedDerivative, iteratedDeriv_zero])
  let JO (m : ℕ) : SmoothDirections U (fun y => iteratedDeriv m g (f y q)) :=
    smoothDirections_contDiff_comp J0 hV (contDiffOn_iteratedDeriv_open hV hg m)
      (fun y hy => hmap y hy hq)
  let B0 : ℝ := C0 * M ^ (k + 1)
  have hB0 : 0 < B0 := mul_pos (zero_lt_one.trans_le hC0)
    (pow_pos (zero_lt_one.trans_le hM) _)
  have hOJ (m : ℕ) (hm : m ≤ a + b) (j : ℕ) (hj : j ≤ k)
      (w : Fin j → X) (hw : ∀ i, P (w i)) :
      ‖(JO m).D j x w‖ ≤ B0 * parameterHeightWeight H j := by
    have hb := scalarComposition_parameterJet_power_bound
      (f := fun y => f y q) (g := iteratedDeriv m g)
      J0 (JO m) hV (contDiffOn_iteratedDeriv_open hV hg m)
      (fun y hy => hmap y hy hq) hj hx hM hPP (hcard j hj) hM hH hHR
      (fun l hl => houter m hm l (hl.trans hj)) w (fun d i => by
        have hh := hsource (d.partSize i) ((d.partSize_le i).trans hj)
          0 0 (Nat.zero_le _) (w ∘ d.emb i) (fun l => hw _)
        simpa only [J0, SmoothDirections.congr, Nat.add_zero, pow_zero, mul_one,
          parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos i)),
          mul_comm] using hh)
    calc
      _ ≤ M * PP * (max 1 RH) ^ k * M ^ k * parameterHeightWeight H j := hb
      _ = _ := by dsimp only [B0, C0]; rw [pow_succ]; ring
  let ra (c : OrderedFinpartition (a + b)) (i : Fin c.length) : ℕ :=
    coordinateRadialOrder (cylinderMixedWord a b ∘ c.emb i)
  let an (c : OrderedFinpartition (a + b)) (i : Fin c.length) : ℕ :=
    coordinateAngularOrder (cylinderMixedWord a b ∘ c.emb i)
  have horder (c : OrderedFinpartition (a + b)) (i : Fin c.length) :
      ra c i + an c i = c.partSize i := coordinateOrders_sum _
  let ff (c : OrderedFinpartition (a + b)) : Fin (c.length + 1) → X → ℝ :=
    Fin.cons (fun y => iteratedDeriv c.length g (f y q))
      (fun i y => mixedDerivative (ra c i) (an c i) (f y) q)
  let JJ (c : OrderedFinpartition (a + b)) :
      ∀ i, SmoothDirections U (ff c i) :=
    Fin.cases (JO c.length) (fun i => F.parameter (ra c i) (an c i) q hq)
  let JT (c : OrderedFinpartition (a + b)) :=
    smoothDirections_finiteProduct hU (JJ c)
  let W : ℝ := M ^ (k + a + b + 1) * parameterHeightWeight H k * t ^ (a + b)
  have hW : 0 ≤ W := mul_nonneg
    (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _)
      (parameterHeightWeight_nonneg hH k)) (pow_nonneg (zero_le_one.trans ht) _)
  have hterm (c : OrderedFinpartition (a + b)) :
      ‖(JT c).D k x v‖ ≤ Cp * C0 * W := by
    let B : Fin (c.length + 1) → ℝ :=
      Fin.cons B0 (fun i => M * t ^ c.partSize i)
    have hB : ∀ i, 0 < B i := Fin.cases hB0 (fun i =>
      mul_pos (zero_lt_one.trans_le hM) (pow_pos (zero_lt_one.trans_le ht) _))
    have hbase : ∀ i, ‖ff c i x‖ ≤ B i := by
      refine Fin.cases ?_ (fun i => ?_)
      · have hh := hOJ c.length c.length_le 0 (Nat.zero_le k)
          Fin.elim0 (fun i => i.elim0)
        simpa only [ff, B, Fin.cons_zero, smoothDirections_D_zero_apply (JO c.length) hx,
          parameterHeightWeight, ite_true, mul_one] using hh
      · have hh := hsource 0 (Nat.zero_le k) (ra c i) (an c i)
          ((horder c i).le.trans (c.partSize_le i)) Fin.elim0 (fun j => j.elim0)
        simpa only [ff, B, Fin.cons_succ, horder,
          smoothDirections_D_zero_apply (F.parameter (ra c i) (an c i) q hq) hx,
          parameterHeightWeight, ite_true, mul_one] using hh
    have hjet : ∀ i (d : OrderedFinpartition k) (j : Fin d.length),
        ‖(JJ c i).D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H * B i := by
      refine Fin.cases ?_ (fun i => ?_)
      · intro d j
        change ‖(JO c.length).D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H * B0
        have hh := hOJ c.length c.length_le (d.partSize j) (d.partSize_le j)
          (v ∘ d.emb j) (fun l => hv _)
        simpa only [parameterHeightWeight,
          if_neg (Nat.ne_of_gt (d.partSize_pos j)), mul_comm] using hh
      · intro d j
        change ‖(F.parameter (ra c i) (an c i) q hq).D
          (d.partSize j) x (v ∘ d.emb j)‖ ≤ H * (M * t ^ c.partSize i)
        have hh := hsource (d.partSize j) (d.partSize_le j) (ra c i) (an c i)
          ((horder c i).le.trans (c.partSize_le i)) (v ∘ d.emb j) (fun l => hv _)
        simpa only [horder, parameterHeightWeight,
          if_neg (Nat.ne_of_gt (d.partSize_pos j)), mul_assoc, mul_comm, mul_left_comm]
          using hh
    have hprodEq : (∏ i, B i) = C0 * M ^ (k + 1 + c.length) * t ^ (a + b) := by
      rw [Fin.prod_univ_succ]
      simp only [B, Fin.cons_zero, Fin.cons_succ]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        orderedFinpartition_sum_partSize]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      dsimp only [B0]
      rw [pow_add]
      ring
    have hprod : (∏ i, B i) ≤ C0 * M ^ (k + a + b + 1) * t ^ (a + b) := by
      rw [hprodEq]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hM (by have hh := c.length_le; omega))
          (zero_le_one.trans hC0)) (pow_nonneg (zero_le_one.trans ht) _)
    let idx : Fin (a + b + 2) := ⟨c.length + 1, by have hh := c.length_le; omega⟩
    have hb := hcpb idx (JJ c) (JT c) x hx H hH hHR B hB hbase v hjet
    calc
      _ ≤ cp idx * parameterHeightWeight H k * ∏ i, B i := hb
      _ ≤ Cp * parameterHeightWeight H k *
          (C0 * M ^ (k + a + b + 1) * t ^ (a + b)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (hcpCp idx) (parameterHeightWeight_nonneg hH k))
          hprod (Finset.prod_nonneg (fun i _ => (hB i).le))
          (mul_nonneg (zero_le_one.trans hCp) (parameterHeightWeight_nonneg hH k))
      _ = _ := by dsimp only [W]; ring
  have hd := smoothDirections_D_eq_linearCombination J JT (fun _ => 1)
    (fun y hy => by
      simp only [one_mul, ff, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      exact mixedDerivative_scalarComp_ordered hΩ hV (F.spatial y hy) hg
        (hmap y hy) a b hq) k hx v
  calc
    _ ≤ ∑ c : OrderedFinpartition (a + b), ‖(JT c).D k x v‖ := by
      rw [hd]
      simpa only [one_mul] using norm_sum_le
        (Finset.univ : Finset (OrderedFinpartition (a + b)))
        (fun c : OrderedFinpartition (a + b) => (1 : ℝ) * (JT c).D k x v)
    _ ≤ ∑ _c : OrderedFinpartition (a + b), Cp * C0 * W :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ ≤ Q * (Cp * C0 * W) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
        (mul_nonneg (mul_nonneg (zero_le_one.trans hCp) (zero_le_one.trans hC0)) hW)
    _ = _ := by dsimp only [W]; ring

end ContinuousFlexibility.Analysis
