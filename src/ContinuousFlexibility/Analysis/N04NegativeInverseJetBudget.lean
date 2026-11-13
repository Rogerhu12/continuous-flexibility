import ContinuousFlexibility.Analysis.N04NegativeInverseJetRecurrence
import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# Sharp mixed bounds for actual inverse and pulled-height jets

The original forward pure-slot bounds and the first spatial inverse
bound imply every positive actual inverse jet. The recurrence has a
finite polynomial majorant independent of the interpolation scale.
The exact degree and one positive-parameter height factor survive both
the inverse induction and composition with the physical height.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

namespace N04NegativeInverseJet

section Residual

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {U : Set E} {V W : Set Y} {F G : E × Y → Y}

/-- One step of the sharp mixed inverse estimate. The forward estimate
uses at most the original parameter prefix. The only inverse estimates
assumed here have strictly smaller total order. -/
theorem higher_norm_le (J : SmoothDirections (U ×ˢ V) F)
    (K : SmoothDirections (U ×ˢ W) G)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hmap : MapsTo G (U ×ˢ W) V)
    (A : (E × Y) → Y →L[ℝ] Y) (hA : ContinuousOn A (U ×ˢ W))
    (hleft : ∀ p ∈ U ×ˢ W, ∀ y : Y,
      A p (J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y))) = y)
    (hright : ∀ p ∈ U ×ˢ W, F (p.1, G p) = p.2)
    (low high : Seminorm ℝ E) (n prefix shift : ℕ) (hshift : 1 ≤ shift)
    (p : E × Y) (hp : p ∈ U ×ˢ W)
    {C M H L R t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hforward : ∀ j : ℕ, 0 < j → j ≤ n + 2 → ∀ w : StateAngleWord j,
      w.stateArity ≤ prefix → ∀ b : Fin j → E, ∀ y : Fin j → Y,
      (∀ i, low (b i) ≤ 1) → (∀ i, high (b i) ≤ R) →
      ‖J.D j (p.1, G p) (fun i => if w.isState i then (b i, 0) else (0, y i))‖ ≤
        C * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) *
            w.selectedProduct (fun i => ‖y i‖))
    (hlower : ∀ j : ℕ, 0 < j → j < n + 2 → ∀ w : StateAngleWord j,
      w.stateArity ≤ prefix → ∀ v : Fin j → E × Y,
      (∀ i, low (v i).1 ≤ 1) → (∀ i, high (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
      ‖K.D j p v‖ ≤ M * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1))
    (w : StateAngleWord (n + 2)) (hw : w.stateArity ≤ prefix)
    (v : Fin (n + 2) → E × Y)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖K.D (n + 2) p v‖ ≤
      (‖A p‖ * ∑ c : OrderedFinpartition (n + 2),
        (Fintype.card (Finset (Fin c.length)) : ℝ) * (C * M ^ c.length * L ^ c.length)) *
          parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + shift * w.stateArity - 1) := by
  classical
  let κ (c : OrderedFinpartition (n + 2)) (i : Fin c.length) :=
    (w.restrict (c.emb i)).stateArity
  let β (c : OrderedFinpartition (n + 2)) (i : Fin c.length) :=
    (w.restrict (c.emb i)).angleArity
  let b (c : OrderedFinpartition (n + 2)) (i : Fin c.length) :=
    continuousLinearJets (ContinuousLinearMap.fst ℝ E Y) (c.partSize i) p (v ∘ c.emb i)
  let y (c : OrderedFinpartition (n + 2)) (i : Fin c.length) :=
    lowerJet K (n + 2) p (c.partSize i) (v ∘ c.emb i)
  have hterm (c : OrderedFinpartition (n + 2)) :
      ‖J.D c.length (p.1, G p) (fun i => (b c i, y c i))‖ ≤
        ((Fintype.card (Finset (Fin c.length)) : ℝ) *
          (C * M ^ c.length * L ^ c.length)) * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + shift * w.stateArity - 1) := by
    have hpart (i : Fin c.length) : 0 < κ c i + β c i := by
      rw [show κ c i + β c i = c.partSize i from (w.restrict (c.emb i)).arity_sum]
      exact c.partSize_pos i
    have hid (i : Fin c.length) (hi : ¬ (κ c i = 1 ∧ β c i = 0)) : b c i = 0 :=
      stateIdentity_eq_zero (c.partSize_pos i) (w.restrict (c.emb i)) p (v ∘ c.emb i)
        (fun j hj => hstate _ (by simpa only [StateAngleWord.isState_restrict] using hj)) hi
    have hl (i : Fin c.length) : ‖y c i‖ ≤ M * parameterHeightWeight H (κ c i) *
        t ^ (β c i + shift * κ c i - 1) := by
      by_cases hi : c.partSize i < n + 2
      · have hk : κ c i ≤ prefix :=
          (Finset.single_le_sum (fun j _ => Nat.zero_le (κ c j)) (Finset.mem_univ i)).trans
            ((w.sum_restrict_stateArity c).le.trans hw)
        dsimp only [y]
        rw [lowerJet_of_lt K hi]
        exact hlower (c.partSize i) (c.partSize_pos i) hi (w.restrict (c.emb i)) hk _
          (fun j => hlow _) (fun j => hhigh _) (fun j => hphysical _)
          (fun j hj => hstate _ (by simpa only [StateAngleWord.isState_restrict] using hj))
          (fun j hj => hspatial _ (by simpa only [StateAngleWord.isState_restrict] using hj))
      · simp only [y, lowerJet, if_neg hi, ContinuousMultilinearMap.zero_apply, norm_zero]
        exact mul_nonneg (mul_nonneg (zero_le_one.trans hM)
          (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _)
    have ho (output : StateAngleWord c.length)
        (hs : output.InverseIdentitySelection (κ c) (β c)) :
        ‖J.D c.length (p.1, G p)
          (fun i => if output.isState i then (b c i, 0) else (0, y c i))‖ ≤
          C * parameterHeightWeight H output.stateArity *
            t ^ (output.angleArity + shift * output.stateArity - 1) *
              output.selectedProduct (fun i => ‖y c i‖) := by
      have hk : output.stateArity ≤ prefix := by
        have hle : output.stateArity ≤ output.flowParameterOrder (κ c) := by
          unfold StateAngleWord.flowParameterOrder
          omega
        rw [output.inverseParameterOrder_eq (κ c) (β c) hs] at hle
        exact (hle.trans (w.sum_restrict_stateArity c).le).trans hw
      exact hforward c.length (c.length_pos (by omega)) c.length_le output hk (b c) (y c)
        (fun i => stateIdentity_seminorm_le low (c.partSize_pos i) p (v ∘ c.emb i)
          zero_le_one (fun j => hlow _))
        (fun i => stateIdentity_seminorm_le high (c.partSize_pos i) p (v ∘ c.emb i)
          hR (fun j => hhigh _))
    have hh := n04NegativeInverse_graph_norm_le (J.D c.length (p.1, G p))
      (c.length_pos (by omega)) (κ c) (β c) shift hshift hpart (b c) (y c) hid
      hC hM hH hHL hL ht ho hl
    simpa only [κ, β, w.sum_restrict_stateArity c, w.sum_restrict_angleArity c,
      mul_assoc] using hh
  rw [higher_apply J K hU hV hW hmap A hA hleft hright n p hp v, norm_neg]
  refine ((A p).le_opNorm _).trans ?_
  calc
    _ ≤ ‖A p‖ * ∑ c : OrderedFinpartition (n + 2),
        (((Fintype.card (Finset (Fin c.length)) : ℝ) *
          (C * M ^ c.length * L ^ c.length)) * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + shift * w.stateArity - 1)) :=
      mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => hterm c))) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

/-- The first inverse order starts the induction with a height factor
exactly in parameter slots and with degree zero in spatial slots. -/
theorem first_norm_le (J : SmoothDirections (U ×ˢ V) F)
    (K : SmoothDirections (U ×ˢ W) G)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hmap : MapsTo G (U ×ˢ W) V)
    (A : (E × Y) → Y →L[ℝ] Y) (hA : ContinuousOn A (U ×ˢ W))
    (hleft : ∀ p ∈ U ×ˢ W, ∀ y : Y,
      A p (J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y))) = y)
    (hright : ∀ p ∈ U ×ˢ W, F (p.1, G p) = p.2)
    (low high : Seminorm ℝ E) (prefix shift : ℕ)
    (p : E × Y) (hp : p ∈ U ×ˢ W)
    {a C H R t : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hApoint : ‖A p‖ ≤ a)
    (hparameter : 1 ≤ prefix → ∀ b : E, low b ≤ 1 → high b ≤ R →
      ‖J.D 1 (p.1, G p) (fun _ : Fin 1 => (b, 0))‖ ≤ C * H * t ^ (shift - 1))
    (w : StateAngleWord 1) (hw : w.stateArity ≤ prefix)
    (v : Fin 1 → E × Y)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖K.D 1 p v‖ ≤ (a * (C + 1)) * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1) := by
  cases w with
  | state w =>
    cases w
    have hk : 1 ≤ prefix := hw
    have hf := hparameter hk (v 0).1 (hlow 0) (hhigh 0)
    have he : K.D 1 p v = -A p (J.D 1 (p.1, G p)
        (fun _ : Fin 1 => ((v 0).1, 0))) := by
      rw [first_apply J K hU hV hW hmap A hA hleft hright p hp v,
        hspatial 0 rfl, zero_sub, map_neg]
    rw [he, norm_neg]
    have hn := ((A p).le_opNorm _).trans (mul_le_mul hApoint hf (norm_nonneg _) ha)
    have hfactor : a * C ≤ a * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) ha
    have hext := mul_le_mul_of_nonneg_right hfactor
      (mul_nonneg hH (pow_nonneg ht (shift - 1)))
    simpa only [StateAngleWord.stateArity, StateAngleWord.angleArity,
      parameterHeightWeight, Nat.zero_add, Nat.mul_one, ite_false, Nat.one_ne_zero,
      mul_assoc] using hn.trans (by simpa only [mul_assoc] using hext)
  | angle w =>
    cases w
    have hz : J.D 1 (p.1, G p) (fun _ : Fin 1 => ((v 0).1, (0 : Y))) = 0 := by
      apply (J.D 1 (p.1, G p)).map_coord_zero (0 : Fin 1)
      rw [hstate 0 rfl]
      rfl
    rw [first_apply J K hU hV hW hmap A hA hleft hright p hp v, hz, sub_zero]
    have hn : ‖A p (v 0).2‖ ≤ a := by
      simpa only [mul_one] using ((A p).le_opNorm _).trans
        (mul_le_mul hApoint (hphysical 0) (norm_nonneg _) ha)
    have hext : a ≤ a * (C + 1) := by nlinarith
    simpa only [StateAngleWord.stateArity, StateAngleWord.angleArity,
      parameterHeightWeight, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.sub_self,
      ite_true, pow_zero, mul_one] using hn.trans hext

end Residual
end N04NegativeInverseJet

section Majorant

def n04NegativeInverse_partitionMajorant (C M L : ℝ) (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, (Fintype.card (Finset (Fin c.length)) : ℝ) *
    (C * M ^ c.length * L ^ c.length)

theorem n04NegativeInverse_partitionMajorant_nonneg {C M L : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ n04NegativeInverse_partitionMajorant C M L n := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (mul_nonneg hC (pow_nonneg hM _)) (pow_nonneg hL _))

/-- A finite algebraic majorant for all inverse orders up to `N`.
It depends only on the spatial inverse bound, the forward bound, and
the height envelope. In particular it is independent of the scale `t`. -/
def n04NegativeInverse_prefixMajorant (a C L : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => n04NegativeInverse_prefixMajorant a C L n + a * (C + 1) +
      a * n04NegativeInverse_partitionMajorant C
        (n04NegativeInverse_prefixMajorant a C L n) L (n + 1)

theorem n04NegativeInverse_prefixMajorant_one_le {a C L : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hL : 0 ≤ L) (n : ℕ) :
    1 ≤ n04NegativeInverse_prefixMajorant a C L n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hM : 0 ≤ n04NegativeInverse_prefixMajorant a C L n := zero_le_one.trans ih
    have hc : 0 ≤ a * (C + 1) := mul_nonneg ha (by linarith)
    have hs := mul_nonneg ha
      (n04NegativeInverse_partitionMajorant_nonneg hC hM hL (n + 1))
    change 1 ≤ n04NegativeInverse_prefixMajorant a C L n + _ + _
    linarith

theorem n04NegativeInverse_prefixMajorant_le_succ {a C L : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hL : 0 ≤ L) (n : ℕ) :
    n04NegativeInverse_prefixMajorant a C L n ≤
      n04NegativeInverse_prefixMajorant a C L (n + 1) := by
  have hM : 0 ≤ n04NegativeInverse_prefixMajorant a C L n :=
    zero_le_one.trans (n04NegativeInverse_prefixMajorant_one_le ha hC hL n)
  have hs := mul_nonneg ha
    (n04NegativeInverse_partitionMajorant_nonneg hC hM hL (n + 1))
  change _ ≤ n04NegativeInverse_prefixMajorant a C L n + a * (C + 1) + _
  have hc : 0 ≤ a * (C + 1) := mul_nonneg ha (by linarith)
  linarith

theorem n04NegativeInverse_prefixMajorant_first_le {a C L : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hL : 0 ≤ L) (n : ℕ) :
    a * (C + 1) ≤ n04NegativeInverse_prefixMajorant a C L (n + 1) := by
  have hM : 0 ≤ n04NegativeInverse_prefixMajorant a C L n :=
    zero_le_one.trans (n04NegativeInverse_prefixMajorant_one_le ha hC hL n)
  have hs := mul_nonneg ha (n04NegativeInverse_partitionMajorant_nonneg hC hM hL (n + 1))
  change _ ≤ n04NegativeInverse_prefixMajorant a C L n + a * (C + 1) + _
  linarith

theorem n04NegativeInverse_prefixMajorant_step_le {a C L : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hL : 0 ≤ L) (n : ℕ) :
    a * n04NegativeInverse_partitionMajorant C
        (n04NegativeInverse_prefixMajorant a C L n) L (n + 1) ≤
      n04NegativeInverse_prefixMajorant a C L (n + 1) := by
  have hM : 0 ≤ n04NegativeInverse_prefixMajorant a C L n :=
    zero_le_one.trans (n04NegativeInverse_prefixMajorant_one_le ha hC hL n)
  have hc : 0 ≤ a * (C + 1) := mul_nonneg ha (by linarith)
  change _ ≤ n04NegativeInverse_prefixMajorant a C L n + a * (C + 1) + _
  linarith

end Majorant

namespace N04NegativeInverseJet

section Prefix

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {U : Set E} {V W : Set Y} {F G : E × Y → Y}

/-- Forward bounds and the first spatial inverse bound control every
actual mixed inverse jet in a finite prefix. No inverse derivative
bound is an input. The common constant is an explicit finite polynomial
majorant, while the spatial degree and positive-parameter height factor
remain exactly those of the original tagged input tuple. -/
theorem prefix_norm_le (J : SmoothDirections (U ×ˢ V) F)
    (K : SmoothDirections (U ×ˢ W) G)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hmap : MapsTo G (U ×ˢ W) V)
    (A : (E × Y) → Y →L[ℝ] Y) (hA : ContinuousOn A (U ×ˢ W))
    (hleft : ∀ p ∈ U ×ˢ W, ∀ y : Y,
      A p (J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y))) = y)
    (hright : ∀ p ∈ U ×ˢ W, F (p.1, G p) = p.2)
    (low high : Seminorm ℝ E) (N prefix shift : ℕ) (hshift : 1 ≤ shift)
    (p : E × Y) (hp : p ∈ U ×ˢ W)
    {a C H L R t : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hApoint : ‖A p‖ ≤ a)
    (hforward : ∀ j : ℕ, 0 < j → j ≤ N → ∀ w : StateAngleWord j,
      w.stateArity ≤ prefix → ∀ b : Fin j → E, ∀ y : Fin j → Y,
      (∀ i, low (b i) ≤ 1) → (∀ i, high (b i) ≤ R) →
      ‖J.D j (p.1, G p) (fun i => if w.isState i then (b i, 0) else (0, y i))‖ ≤
        C * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) *
            w.selectedProduct (fun i => ‖y i‖))
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N)
    (w : StateAngleWord n) (hw : w.stateArity ≤ prefix) (v : Fin n → E × Y)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖K.D n p v‖ ≤ n04NegativeInverse_prefixMajorant a C L N *
      parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hall : ∀ m : ℕ, m ≤ N → ∀ j : ℕ, 0 < j → j ≤ m →
      ∀ word : StateAngleWord j, word.stateArity ≤ prefix → ∀ u : Fin j → E × Y,
      (∀ i, low (u i).1 ≤ 1) → (∀ i, high (u i).1 ≤ R) →
      (∀ i, ‖(u i).2‖ ≤ 1) →
      (∀ i, word.isState i = false → (u i).1 = 0) →
      (∀ i, word.isState i = true → (u i).2 = 0) →
      ‖K.D j p u‖ ≤ n04NegativeInverse_prefixMajorant a C L m *
        parameterHeightWeight H word.stateArity *
          t ^ (word.angleArity + shift * word.stateArity - 1) := by
    intro m
    induction m with
    | zero =>
      intro _ j hj hjm
      omega
    | succ m ih =>
      intro hm j hj hjm word hword u hul huh hup hus hua
      by_cases hjprev : j ≤ m
      · have hh := ih (by omega) j hj hjprev word hword u hul huh hup hus hua
        exact hh.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (n04NegativeInverse_prefixMajorant_le_succ ha hC hL0 m)
            (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _))
      · have heq : j = m + 1 := by omega
        subst j
        cases m with
        | zero =>
          have hparameter : 1 ≤ prefix → ∀ b : E, low b ≤ 1 → high b ≤ R →
              ‖J.D 1 (p.1, G p) (fun _ : Fin 1 => (b, 0))‖ ≤
                C * H * t ^ (shift - 1) := by
            intro hprefix b hb hbh
            let word₁ : StateAngleWord 1 := .state .nil
            have h := hforward 1 (by omega) hm word₁ hprefix
              (fun _ => b) (fun _ => 0) (fun _ => hb) (fun _ => hbh)
            have he : (fun i : Fin 1 => if word₁.isState i then (b, (0 : Y)) else (0, 0)) =
                fun _ : Fin 1 => (b, (0 : Y)) := by
              funext i
              rw [Fin.eq_zero i]
              rfl
            rw [he] at h
            simpa only [word₁, StateAngleWord.stateArity, StateAngleWord.angleArity,
              StateAngleWord.selectedProduct, parameterHeightWeight, Nat.zero_add,
              Nat.mul_one, Nat.one_ne_zero, ite_false, mul_one] using h
          have hh := first_norm_le J K hU hV hW hmap A hA hleft hright low high
            prefix shift p hp ha hC hH ht hApoint hparameter word hword u hul huh hup hus hua
          exact hh.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (n04NegativeInverse_prefixMajorant_first_le ha hC hL0 0)
              (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _))
        | succ m =>
          have hM := n04NegativeInverse_prefixMajorant_one_le ha hC hL0 (m + 1)
          have hh := higher_norm_le J K hU hV hW hmap A hA hleft hright low high
            m prefix shift hshift p hp hC hM hH hHL hL hR ht
            (fun j hj hjN => hforward j hj (hjN.trans hm))
            (fun j hj hjN word hword u hul huh hup hus hua =>
              ih (by omega) j hj (by omega) word hword u hul huh hup hus hua)
            word hword u hul huh hup hus hua
          have hs := n04NegativeInverse_partitionMajorant_nonneg hC
            (zero_le_one.trans hM) hL0 (m + 2)
          have hc : ‖A p‖ * n04NegativeInverse_partitionMajorant C
                (n04NegativeInverse_prefixMajorant a C L (m + 1)) L (m + 2) ≤
              n04NegativeInverse_prefixMajorant a C L (m + 2) :=
            (mul_le_mul_of_nonneg_right hApoint hs).trans
              (n04NegativeInverse_prefixMajorant_step_le ha hC hL0 (m + 1))
          exact hh.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc (parameterHeightWeight_nonneg hH _))
            (pow_nonneg ht _))
  exact hall N le_rfl n hn hnN w hw v hlow hhigh hphysical hstate hspatial

end Prefix

section ScalarComposition

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {U : Set E} {V W : Set Y} {f : E × Y → ℝ} {G : E × Y → Y}

/-- Applying an actual scalar field at the inverse point uses the same
sharp graph budget. All positive inverse orders through the requested
order may be used here; no estimate of the composition is assumed.
This is the final raw estimate for the pulled physical height. -/
theorem scalar_graph_norm_le (J : SmoothDirections (U ×ˢ V) f)
    (K : SmoothDirections (U ×ˢ W) G) (hmap : MapsTo G (U ×ˢ W) V)
    (Q : SmoothDirections (U ×ˢ W) (fun p => f (p.1, G p)))
    (low high : Seminorm ℝ E) (n prefix shift : ℕ) (hn : 0 < n)
    (hshift : 1 ≤ shift) (p : E × Y) (hp : p ∈ U ×ˢ W)
    {C M H L R t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hforward : ∀ j : ℕ, 0 < j → j ≤ n → ∀ w : StateAngleWord j,
      w.stateArity ≤ prefix → ∀ b : Fin j → E, ∀ y : Fin j → Y,
      (∀ i, low (b i) ≤ 1) → (∀ i, high (b i) ≤ R) →
      ‖J.D j (p.1, G p) (fun i => if w.isState i then (b i, 0) else (0, y i))‖ ≤
        C * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) *
            w.selectedProduct (fun i => ‖y i‖))
    (hinverse : ∀ j : ℕ, 0 < j → j ≤ n → ∀ w : StateAngleWord j,
      w.stateArity ≤ prefix → ∀ v : Fin j → E × Y,
      (∀ i, low (v i).1 ≤ 1) → (∀ i, high (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
      ‖K.D j p v‖ ≤ M * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1))
    (w : StateAngleWord n) (hw : w.stateArity ≤ prefix) (v : Fin n → E × Y)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖Q.D n p v‖ ≤ n04NegativeInverse_partitionMajorant C M L n *
      parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) := by
  classical
  let π : (E × Y) →L[ℝ] E := ContinuousLinearMap.fst ℝ E Y
  let P := smoothDirectionsUniformProd
    ((smoothDirectionsLinear π).restrict K.open_domain (subset_univ (U ×ˢ W))) K
  have hgraph : MapsTo (fun z => (π z, G z)) (U ×ˢ W) (U ×ˢ V) :=
    fun z hz => ⟨hz.1, hmap hz⟩
  let Q' : SmoothDirections (U ×ˢ W) (fun z => f (z.1, G z)) :=
    (smoothDirections_realCompTVS P J hgraph).congrOn (fun _ _ => rfl)
  have hformula : Q.D n p v = ∑ c : OrderedFinpartition n,
      J.D c.length (p.1, G p) (fun i =>
        (continuousLinearJets π (c.partSize i) p (v ∘ c.emb i),
          K.D (c.partSize i) p (v ∘ c.emb i))) := by
    rw [Q.unique Q' n p hp]
    change (smoothDirections_realCompTVS P J hgraph).D n p v = _
    rw [smoothDirections_realCompTVS_D_apply]
    rfl
  let κ (c : OrderedFinpartition n) (i : Fin c.length) :=
    (w.restrict (c.emb i)).stateArity
  let β (c : OrderedFinpartition n) (i : Fin c.length) :=
    (w.restrict (c.emb i)).angleArity
  let b (c : OrderedFinpartition n) (i : Fin c.length) :=
    continuousLinearJets π (c.partSize i) p (v ∘ c.emb i)
  let y (c : OrderedFinpartition n) (i : Fin c.length) :=
    K.D (c.partSize i) p (v ∘ c.emb i)
  have hterm (c : OrderedFinpartition n) :
      ‖J.D c.length (p.1, G p) (fun i => (b c i, y c i))‖ ≤
        ((Fintype.card (Finset (Fin c.length)) : ℝ) *
          (C * M ^ c.length * L ^ c.length)) * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + shift * w.stateArity - 1) := by
    have hpart (i : Fin c.length) : 0 < κ c i + β c i := by
      rw [show κ c i + β c i = c.partSize i from (w.restrict (c.emb i)).arity_sum]
      exact c.partSize_pos i
    have hid (i : Fin c.length) (hi : ¬ (κ c i = 1 ∧ β c i = 0)) : b c i = 0 :=
      stateIdentity_eq_zero (c.partSize_pos i) (w.restrict (c.emb i)) p (v ∘ c.emb i)
        (fun j hj => hstate _ (by simpa only [StateAngleWord.isState_restrict] using hj)) hi
    have hl (i : Fin c.length) : ‖y c i‖ ≤ M * parameterHeightWeight H (κ c i) *
        t ^ (β c i + shift * κ c i - 1) := by
      have hk : κ c i ≤ prefix :=
        (Finset.single_le_sum (fun j _ => Nat.zero_le (κ c j)) (Finset.mem_univ i)).trans
          ((w.sum_restrict_stateArity c).le.trans hw)
      exact hinverse (c.partSize i) (c.partSize_pos i) (c.partSize_le i)
        (w.restrict (c.emb i)) hk _ (fun j => hlow _) (fun j => hhigh _) (fun j => hphysical _)
        (fun j hj => hstate _ (by simpa only [StateAngleWord.isState_restrict] using hj))
        (fun j hj => hspatial _ (by simpa only [StateAngleWord.isState_restrict] using hj))
    have ho (output : StateAngleWord c.length)
        (hs : output.InverseIdentitySelection (κ c) (β c)) :
        ‖J.D c.length (p.1, G p)
          (fun i => if output.isState i then (b c i, 0) else (0, y c i))‖ ≤
          C * parameterHeightWeight H output.stateArity *
            t ^ (output.angleArity + shift * output.stateArity - 1) *
              output.selectedProduct (fun i => ‖y c i‖) := by
      have hk : output.stateArity ≤ prefix := by
        have hle : output.stateArity ≤ output.flowParameterOrder (κ c) := by
          unfold StateAngleWord.flowParameterOrder
          omega
        rw [output.inverseParameterOrder_eq (κ c) (β c) hs] at hle
        exact (hle.trans (w.sum_restrict_stateArity c).le).trans hw
      exact hforward c.length (c.length_pos hn) c.length_le output hk (b c) (y c)
        (fun i => stateIdentity_seminorm_le low (c.partSize_pos i) p (v ∘ c.emb i)
          zero_le_one (fun j => hlow _))
        (fun i => stateIdentity_seminorm_le high (c.partSize_pos i) p (v ∘ c.emb i)
          hR (fun j => hhigh _))
    have hh := n04NegativeInverse_graph_norm_le (J.D c.length (p.1, G p))
      (c.length_pos hn) (κ c) (β c) shift hshift hpart (b c) (y c) hid
      hC hM hH hHL hL ht ho hl
    simpa only [κ, β, w.sum_restrict_stateArity c, w.sum_restrict_angleArity c,
      mul_assoc] using hh
  rw [hformula]
  calc
    _ ≤ ∑ c : OrderedFinpartition n, ‖J.D c.length (p.1, G p)
        (fun i => (b c i, y c i))‖ := norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition n,
        (((Fintype.card (Finset (Fin c.length)) : ℝ) *
          (C * M ^ c.length * L ^ c.length)) * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + shift * w.stateArity - 1)) :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

end ScalarComposition
end N04NegativeInverseJet

end ContinuousFlexibility.Analysis
