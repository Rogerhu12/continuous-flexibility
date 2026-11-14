module

public import ContinuousFlexibility.Analysis.N04NegativeInverseImplicitIdentification
public import ContinuousFlexibility.Analysis.N04NegativeInverseSlotBudget

/-!
# Exact recurrences of the genuine parameterized inverse

The continuous implicit candidates agree with every actual solution
tower. At first order the target direction remains explicit. At higher
orders the affine target disappears, leaving only original forward jets
and strictly lower inverse jets in the ordered-partition formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

namespace N04NegativeGeometryImplicitJet

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {U : Set E} {V : Set Y} {H : E × Y → Y} {g : E → Y}

/-- The inverse tower's first derivative has no lower inverse jet.
This is the exact source of the positive-parameter height factor. -/
theorem tower_one_apply (J : SmoothDirections (U ×ˢ V) H)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (x : E) (v : Fin 1 → E) :
    (tower J hg hmap A hA 1).value x v =
      -A x (J.D 1 (x, g x) (fun _ : Fin 1 => (v 0, 0))) := by
  classical
  rw [tower_succ_apply, forcing_apply]
  let c₀ := OrderedFinpartition.singleBlock 1 (by omega)
  let T : OrderedFinpartition 1 → Y := fun c => J.D c.length (x, g x)
    (fun i => graph (c.partSize i)
      ((lower (fun k (_ : k < 1) => tower J hg hmap A hA k) (c.partSize i)).value x)
      (v ∘ c.emb i))
  have hc (c : OrderedFinpartition 1) : c = c₀ :=
    OrderedFinpartition.eq_singleBlock_of_length_eq_one c (by omega)
      (Nat.le_antisymm c.length_le (c.length_pos (by omega)))
  have hs : (∑ c : OrderedFinpartition 1, T c) = T c₀ := by
    apply Finset.sum_eq_single c₀
    · intro c _ hne
      exact False.elim (hne (hc c))
    · intro hne
      exact False.elim (hne (Finset.mem_univ _))
  change -A x (∑ c : OrderedFinpartition 1, T c) = _
  rw [hs]
  change -A x (J.D 1 (x, g x) (fun _ : Fin 1 => graph 1
    ((lower (fun k (_ : k < 1) => tower J hg hmap A hA k) 1).value x) v)) = _
  rw [lower_self]
  apply congrArg (fun y : Y => -A x y)
  apply congrArg (J.D 1 (x, g x))
  funext i
  rw [graph_apply]
  change (v 0, (0 : Y)) + (0, 0) = (v 0, 0)
  simp only [Prod.mk_add_mk, add_zero]

/-- A finite majorant for the actual recursively constructed forcing.
Only strictly lower solution jets enter the summands. -/
theorem tower_succ_norm_le (J : SmoothDirections (U ×ˢ V) H)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (n : ℕ) (x : E) (v : Fin (n + 1) → E)
    (B : OrderedFinpartition (n + 1) → ℝ)
    (hB : ∀ c : OrderedFinpartition (n + 1),
      ‖J.D c.length (x, g x)
        (fun i => graph (c.partSize i)
          ((lower (fun k (_ : k < n + 1) => tower J hg hmap A hA k)
            (c.partSize i)).value x) (v ∘ c.emb i))‖ ≤ B c) :
    ‖(tower J hg hmap A hA (n + 1)).value x v‖ ≤
      ‖A x‖ * ∑ c : OrderedFinpartition (n + 1), B c := by
  rw [tower_succ_apply, norm_neg]
  refine ((A x).le_opNorm _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [forcing_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => hB c))

variable [FiniteDimensional ℝ Y]

/-- Any genuine solution tower agrees with the constructed implicit
candidate, so quantitative estimates of the candidate apply to the
actual map supplied by the geometric inverse theorem. -/
theorem tower_eq_genuine (J : SmoothDirections (U ×ˢ V) H)
    (K : SmoothDirections U g) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (hleft : ∀ x ∈ U, ∀ y : Y,
      A x (J.D 1 (x, g x) (fun _ : Fin 1 => (0, y))) = y)
    (hzero : ∀ x ∈ U, H (x, g x) = 0)
    (n : ℕ) (x : E) (hx : x ∈ U) :
    (tower J K.hasProjectiveJetsOn.continuousOn hmap A hA n).value x = K.D n x := by
  have hs : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffAt ℝ ∞ (fun q => g (x + L q)) 0 := by
    intro m x hx L
    apply (smoothDirections_contDiffOn_finiteAffine K x L).contDiffAt
    apply (K.open_domain.preimage (continuous_const.add L.continuous)).mem_nhds
    change x + L 0 ∈ U
    simpa only [map_zero, add_zero] using hx
  exact (smoothDirections J K.open_domain K.hasProjectiveJetsOn.continuousOn hmap
    A hA hleft hzero hs).unique K n x hx

end N04NegativeGeometryImplicitJet

namespace N04NegativeInverseJet

section StateIdentity

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]

/-- The positive graph jet of the unchanged state coordinate vanishes
unless its block consists of one original parameter direction. -/
theorem stateIdentity_eq_zero {n : ℕ} (hn : 0 < n)
    (w : StateAngleWord n) (p : E × Y) (v : Fin n → E × Y)
    (hpure : ∀ i, w.isState i = false → (v i).1 = 0)
    (h : ¬ (w.stateArity = 1 ∧ w.angleArity = 0)) :
    continuousLinearJets (ContinuousLinearMap.fst ℝ E Y) n p v = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      change (v 0).1 = 0
      cases w with
      | state w =>
          cases w
          exact False.elim (h ⟨rfl, rfl⟩)
      | angle w =>
          cases w
          exact hpure 0 rfl
    | succ n => rfl

theorem stateIdentity_seminorm_le (q : Seminorm ℝ E) {n : ℕ} (hn : 0 < n)
    (p : E × Y) (v : Fin n → E × Y) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∀ i, q (v i).1 ≤ R) :
    q (continuousLinearJets (ContinuousLinearMap.fst ℝ E Y) n p v) ≤ R := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => exact hv 0
    | succ n => simpa only [continuousLinearJets, ContinuousMultilinearMap.zero_apply,
        map_zero] using hR

end StateIdentity

section Residual

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {U : Set E} {V W : Set Y} {F G : E × Y → Y}

def forwardInput : ((E × Y) × Y) →L[ℝ] E × Y :=
  ((ContinuousLinearMap.fst ℝ E Y).comp
    (ContinuousLinearMap.fst ℝ (E × Y) Y)).prod
      (ContinuousLinearMap.snd ℝ (E × Y) Y)

def targetInput : ((E × Y) × Y) →L[ℝ] Y :=
  (ContinuousLinearMap.snd ℝ E Y).comp (ContinuousLinearMap.fst ℝ (E × Y) Y)

/-- The residual uses the original forward tower and an exact linear
target coordinate.  Its higher target derivatives are genuinely zero. -/
def residualTower (J : SmoothDirections (U ×ˢ V) F)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) :
    SmoothDirections ((U ×ˢ W) ×ˢ V)
      (fun p : (E × Y) × Y => F (p.1.1, p.2) - p.1.2) := by
  let P := J.compLinear (forwardInput (E := E) (Y := Y)) ((hU.prod hW).prod hV)
    (fun p hp => ⟨hp.1.1, hp.2⟩)
  let Q := smoothDirectionsOfJets ((hU.prod hW).prod hV)
    (continuousLinearJets (targetInput (E := E) (Y := Y)))
    (hasProjectiveJetsOn_continuousLinear (targetInput (E := E) (Y := Y)) _)
  let S : (Y × Y) →L[ℝ] Y :=
    ContinuousLinearMap.fst ℝ Y Y - ContinuousLinearMap.snd ℝ Y Y
  exact (smoothDirections_postcompCLM (smoothDirectionsProd P Q) S).congrOn
    (fun p _ => rfl)

theorem residualTower_D_apply (J : SmoothDirections (U ×ˢ V) F)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (n : ℕ) (p : (E × Y) × Y) (v : Fin n → (E × Y) × Y) :
    (residualTower J hU hV hW).D n p v =
      J.D n (p.1.1, p.2) (fun i => ((v i).1.1, (v i).2)) -
        continuousLinearJets (targetInput (E := E) (Y := Y)) n p v := by
  change J.D n (0 + forwardInput p) (fun i => forwardInput (v i)) -
    continuousLinearJets targetInput n p v = _
  rw [zero_add]
  rfl

/-- Projecting the implicit graph forgets only the target identity;
the original state coordinate remains an exact linear jet. -/
theorem forwardInput_graph {n : ℕ} (hn : 0 < n)
    (B : (E × Y) [×n]→L[ℝ] Y) (p : E × Y) (v : Fin n → E × Y) :
    forwardInput (N04NegativeGeometryImplicitJet.graph n B v) =
      (continuousLinearJets (ContinuousLinearMap.fst ℝ E Y) n p v, B v) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      change ((v 0).1 + 0, (0 : Y) + B v) = ((v 0).1, B v)
      simp only [add_zero, zero_add]
    | succ n =>
      change ((0 : E) + 0, (0 : Y) + B v) = (0, B v)
      simp only [zero_add]

theorem targetInput_graph_eq_zero {n : ℕ} (hn : 2 ≤ n)
    (B : (E × Y) [×n]→L[ℝ] Y) (v : Fin n → E × Y) :
    targetInput (N04NegativeGeometryImplicitJet.graph n B v) = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      change (0 : Y) + 0 = 0
      exact zero_add 0

theorem continuousLinearJets_eq_zero {X Z : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    (L : X →L[ℝ] Z) {n : ℕ} (hn : 2 ≤ n) (x : X) :
    continuousLinearJets L n x = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n => rfl

def lowerJet (K : SmoothDirections (U ×ˢ W) G) (N : ℕ) (p : E × Y) (k : ℕ) :
    (E × Y) [×k]→L[ℝ] Y :=
  if k < N then K.D k p else 0

theorem lowerJet_of_lt (K : SmoothDirections (U ×ˢ W) G)
    {N k : ℕ} (hk : k < N) (p : E × Y) :
    lowerJet K N p k = K.D k p := by simp only [lowerJet, if_pos hk]

@[simp] theorem lowerJet_self (K : SmoothDirections (U ×ˢ W) G) (N : ℕ) (p : E × Y) :
    lowerJet K N p N = 0 := by simp only [lowerJet, lt_self_iff_false, if_false]

/-- At order at least two, every residual partition is exactly the
corresponding original forward partition.  The affine target has no
contribution, including at the unique highest block. -/
theorem residual_partition_apply (J : SmoothDirections (U ×ˢ V) F)
    (K : SmoothDirections (U ×ˢ W) G)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    {N : ℕ} (hN : 2 ≤ N) (p : E × Y) (v : Fin N → E × Y)
    (c : OrderedFinpartition N) :
    (residualTower J hU hV hW).D c.length (p, G p)
        (fun i => N04NegativeGeometryImplicitJet.graph (c.partSize i)
          (lowerJet K N p (c.partSize i)) (v ∘ c.emb i)) =
      J.D c.length (p.1, G p)
        (fun i =>
          (continuousLinearJets (ContinuousLinearMap.fst ℝ E Y) (c.partSize i) p
            (v ∘ c.emb i), lowerJet K N p (c.partSize i) (v ∘ c.emb i))) := by
  have hn : 0 < N := by omega
  have ht : continuousLinearJets (targetInput (E := E) (Y := Y)) c.length (p, G p)
      (fun i => N04NegativeGeometryImplicitJet.graph (c.partSize i)
        (lowerJet K N p (c.partSize i)) (v ∘ c.emb i)) = 0 := by
    by_cases hl : c.length = 1
    · obtain rfl := OrderedFinpartition.eq_singleBlock_of_length_eq_one c hn hl
      change targetInput (N04NegativeGeometryImplicitJet.graph N
        (lowerJet K N p N) v) = 0
      exact targetInput_graph_eq_zero hN _ _
    · have hlen : 2 ≤ c.length := by have hp := c.length_pos hn; omega
      rw [continuousLinearJets_eq_zero _ hlen]
      rfl
  rw [residualTower_D_apply, ht, sub_zero]
  apply congrArg (J.D c.length (p.1, G p))
  funext i
  exact forwardInput_graph (c.partSize_pos i) _ p _

variable [FiniteDimensional ℝ Y]

/-- The residual construction uses precisely the given inverse of the
spatial differential of the original forward chart. -/
theorem residual_left (J : SmoothDirections (U ×ˢ V) F)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (A : (E × Y) → Y →L[ℝ] Y)
    (hleft : ∀ p ∈ U ×ˢ W, ∀ y : Y,
      A p (J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y))) = y) :
    ∀ p ∈ U ×ˢ W, ∀ y : Y,
      A p ((residualTower J hU hV hW).D 1 (p, G p)
        (fun _ : Fin 1 => (0, y))) = y := by
  intro p hp y
  rw [residualTower_D_apply]
  change A p (J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y)) - 0) = y
  rw [sub_zero]
  exact hleft p hp y

/-- Exact first-order inverse formula, including the target direction.
Its pure parameter specialization has the forward height factor. -/
theorem first_apply (J : SmoothDirections (U ×ˢ V) F)
    (K : SmoothDirections (U ×ˢ W) G)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hmap : MapsTo G (U ×ˢ W) V)
    (A : (E × Y) → Y →L[ℝ] Y) (hA : ContinuousOn A (U ×ˢ W))
    (hleft : ∀ p ∈ U ×ˢ W, ∀ y : Y,
      A p (J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y))) = y)
    (hright : ∀ p ∈ U ×ˢ W, F (p.1, G p) = p.2)
    (p : E × Y) (hp : p ∈ U ×ˢ W) (v : Fin 1 → E × Y) :
    K.D 1 p v = A p ((v 0).2 -
      J.D 1 (p.1, G p) (fun _ : Fin 1 => ((v 0).1, 0))) := by
  let H := residualTower J hU hV hW
  have hzero : ∀ p ∈ U ×ˢ W, F (p.1, G p) - p.2 = 0 :=
    fun p hp => sub_eq_zero.mpr (hright p hp)
  rw [← N04NegativeGeometryImplicitJet.tower_eq_genuine H K hmap A hA
    (residual_left J hU hV hW A hleft) hzero 1 p hp,
    N04NegativeGeometryImplicitJet.tower_one_apply]
  rw [residualTower_D_apply]
  change -A p (J.D 1 (p.1, G p) (fun _ : Fin 1 => ((v 0).1, 0)) - (v 0).2) = _
  rw [← map_neg, neg_sub]

/-- The actual inverse obeys the forward-chart recurrence at every
order at least two. Every selected inverse jet has strictly lower
order; the highest inverse block has been replaced by zero. -/
theorem higher_apply (J : SmoothDirections (U ×ˢ V) F)
    (K : SmoothDirections (U ×ˢ W) G)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hmap : MapsTo G (U ×ˢ W) V)
    (A : (E × Y) → Y →L[ℝ] Y) (hA : ContinuousOn A (U ×ˢ W))
    (hleft : ∀ p ∈ U ×ˢ W, ∀ y : Y,
      A p (J.D 1 (p.1, G p) (fun _ : Fin 1 => (0, y))) = y)
    (hright : ∀ p ∈ U ×ˢ W, F (p.1, G p) = p.2)
    (n : ℕ) (p : E × Y) (hp : p ∈ U ×ˢ W) (v : Fin (n + 2) → E × Y) :
    K.D (n + 2) p v = -A p (∑ c : OrderedFinpartition (n + 2),
      J.D c.length (p.1, G p)
        (fun i =>
          (continuousLinearJets (ContinuousLinearMap.fst ℝ E Y) (c.partSize i) p
            (v ∘ c.emb i), lowerJet K (n + 2) p (c.partSize i) (v ∘ c.emb i)))) := by
  let H := residualTower J hU hV hW
  let hg := K.hasProjectiveJetsOn.continuousOn
  have hzero : ∀ p ∈ U ×ˢ W, F (p.1, G p) - p.2 = 0 :=
    fun p hp => sub_eq_zero.mpr (hright p hp)
  have he (j : ℕ) :
      (N04NegativeGeometryImplicitJet.tower H hg hmap A hA j).value p = K.D j p :=
    N04NegativeGeometryImplicitJet.tower_eq_genuine H K hmap A hA
      (residual_left J hU hV hW A hleft) hzero j p hp
  have hlo (j : ℕ) :
      (N04NegativeGeometryImplicitJet.lower
        (fun k (_ : k < n + 2) => N04NegativeGeometryImplicitJet.tower H hg hmap A hA k)
          j).value p = lowerJet K (n + 2) p j := by
    by_cases hj : j < n + 2
    · rw [N04NegativeGeometryImplicitJet.lower_of_lt _ hj, lowerJet_of_lt K hj]
      exact he j
    · simp only [N04NegativeGeometryImplicitJet.lower, dif_neg hj,
        N04NegativeGeometryImplicitJet.zero, lowerJet, if_neg hj]
  rw [← he (n + 2), N04NegativeGeometryImplicitJet.tower_succ_apply,
    N04NegativeGeometryImplicitJet.forcing_apply]
  apply congrArg (fun y : Y => -A p y)
  apply Finset.sum_congr rfl
  intro c _
  simp_rw [hlo]
  exact residual_partition_apply J K hU hV hW (by omega) p v c

end Residual
end N04NegativeInverseJet
end ContinuousFlexibility.Analysis
