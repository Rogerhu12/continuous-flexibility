import ContinuousFlexibility.Analysis.N04NegativeInverseImplicitIdentification
import ContinuousFlexibility.Analysis.N01cStateAngleGraphBudget
import ContinuousFlexibility.Analysis.N04RealizationMixedSlotBudget

/-!
# Exact mixed-slot budgets for the actual implicit inverse

A nonzero state identity in a graph slot comes from a singleton state
block.  Keeping that restriction saves exactly one spatial derivative
in each nonzero inverse order.  The outer forward derivative and all
selected lower inverse factors have total degree
`angleArity + shift * stateArity - 1`, independently of the number of
partition blocks.  Positive parameter orders retain one height factor.

The estimates below are for the actual finite multilinear partition
formula.  In particular the first-order formula and the forcing norm
bound apply directly to the genuine implicit tower constructed in
`N04NegativeInverseImplicitIdentification`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

namespace StateAngleWord

/-- A selected state identity is a singleton parameter block. -/
def InverseIdentitySelection {n : ℕ} (w : StateAngleWord n)
    (κ β : Fin n → ℕ) : Prop :=
  ∀ i, w.isState i = true → κ i = 1 ∧ β i = 0

theorem inverseIdentitySelection_tail_state {n : ℕ} {w : StateAngleWord n}
    {κ β : Fin (n + 1) → ℕ}
    (h : (state w).InverseIdentitySelection κ β) :
    w.InverseIdentitySelection (Fin.tail κ) (Fin.tail β) :=
  fun i hi => h i.succ hi

theorem inverseIdentitySelection_tail_angle {n : ℕ} {w : StateAngleWord n}
    {κ β : Fin (n + 1) → ℕ}
    (h : (angle w).InverseIdentitySelection κ β) :
    w.InverseIdentitySelection (Fin.tail κ) (Fin.tail β) :=
  fun i hi => h i.succ hi

/-- All parameter slots are counted once, either by the outer state
derivative or by one selected inverse factor. -/
theorem inverseParameterOrder_eq {n : ℕ} (w : StateAngleWord n)
    (κ β : Fin n → ℕ) (h : w.InverseIdentitySelection κ β) :
    w.flowParameterOrder κ = ∑ i, κ i := by
  induction w with
  | nil =>
      simp only [flowParameterOrder, stateArity, selectedSum, Fin.sum_univ_zero,
        Nat.add_zero]
  | state w ih =>
      have hhead := (h 0 rfl).1
      have ht := ih (Fin.tail κ) (Fin.tail β) h.inverseIdentitySelection_tail_state
      simp only [flowParameterOrder, stateArity, selectedSum] at ht ⊢
      rw [Fin.sum_univ_succ, hhead]
      omega
  | angle w ih =>
      have ht := ih (Fin.tail κ) (Fin.tail β) h.inverseIdentitySelection_tail_angle
      simp only [flowParameterOrder, stateArity, selectedSum] at ht ⊢
      rw [Fin.sum_univ_succ]
      omega

/-- The unsubtracted degree is additive before the one outer inverse
derivative is removed.  This also covers an empty outer word. -/
theorem inverseDegree_add_one {n : ℕ} (w : StateAngleWord n)
    (κ β : Fin n → ℕ) (shift : ℕ) (hshift : 1 ≤ shift)
    (hpart : ∀ i, 0 < κ i + β i)
    (h : w.InverseIdentitySelection κ β) :
    w.angleArity + shift * w.stateArity +
        w.selectedSum (fun i => β i + shift * κ i - 1) =
      (∑ i, β i) + shift * ∑ i, κ i := by
  induction w with
  | nil =>
      simp only [angleArity, stateArity, selectedSum, Fin.sum_univ_zero,
        Nat.mul_zero, Nat.add_zero]
  | state w ih =>
      obtain ⟨hk, hb⟩ := h 0 rfl
      have ht := ih (Fin.tail κ) (Fin.tail β) (fun i => hpart i.succ)
        h.inverseIdentitySelection_tail_state
      simp only [angleArity, stateArity, selectedSum, Fin.tail_def] at ht ⊢
      simp only [Fin.sum_univ_succ, hk, hb, Nat.zero_add, Nat.mul_add,
        Nat.mul_one, Fin.tail_def]
      omega
  | angle w ih =>
      have ht := ih (Fin.tail κ) (Fin.tail β) (fun i => hpart i.succ)
        h.inverseIdentitySelection_tail_angle
      have hk : κ 0 ≤ shift * κ 0 := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (κ 0) hshift
      have hp := hpart 0
      simp only [angleArity, stateArity, selectedSum, Fin.tail_def] at ht ⊢
      simp only [Fin.sum_univ_succ, Nat.mul_add, Fin.tail_def]
      omega

/-- The outer forward derivative and selected lower inverse factors
have exactly the desired degree, with no loss per spatial block. -/
theorem inverseDegree_eq {n : ℕ} (w : StateAngleWord n) (hn : 0 < n)
    (κ β : Fin n → ℕ) (shift : ℕ) (hshift : 1 ≤ shift)
    (hpart : ∀ i, 0 < κ i + β i)
    (h : w.InverseIdentitySelection κ β) :
    (w.angleArity + shift * w.stateArity - 1) +
        w.selectedSum (fun i => β i + shift * κ i - 1) =
      (∑ i, β i) + shift * (∑ i, κ i) - 1 := by
  have he := w.inverseDegree_add_one κ β shift hshift hpart h
  have hm : w.stateArity ≤ shift * w.stateArity := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right w.stateArity hshift
  have ha := w.arity_sum
  omega

theorem selectedProduct_natPower {n : ℕ} (w : StateAngleWord n)
    (d : Fin n → ℕ) (t : ℝ) :
    w.selectedProduct (fun i => t ^ d i) = t ^ w.selectedSum d := by
  induction w with
  | nil => simp only [selectedProduct, selectedSum, pow_zero]
  | state w ih => exact ih (Fin.tail d)
  | angle w ih =>
      simp only [selectedProduct, selectedSum, Fin.tail_def, ih, pow_add]

/-- Exact degree and exact parameter count survive a genuine ordered
partition of the original mixed tuple. -/
theorem partition_inverseDegree_eq {n : ℕ} (input : StateAngleWord n)
    (hn : 0 < n) (c : _root_.OrderedFinpartition n)
    (output : StateAngleWord c.length) (shift : ℕ) (hshift : 1 ≤ shift)
    (h : output.InverseIdentitySelection
      (fun i => (input.restrict (c.emb i)).stateArity)
      (fun i => (input.restrict (c.emb i)).angleArity)) :
    (output.angleArity + shift * output.stateArity - 1) +
        output.selectedSum (fun i => (input.restrict (c.emb i)).angleArity +
          shift * (input.restrict (c.emb i)).stateArity - 1) =
      input.angleArity + shift * input.stateArity - 1 := by
  have he := output.inverseDegree_eq (c.length_pos hn)
    (fun i => (input.restrict (c.emb i)).stateArity)
    (fun i => (input.restrict (c.emb i)).angleArity) shift hshift
    (fun i => by rw [(input.restrict (c.emb i)).arity_sum]; exact c.partSize_pos i) h
  simpa only [input.sum_restrict_angleArity c, input.sum_restrict_stateArity c] using he

/-- Extra height factors are absorbed by `L`, but the first positive
parameter factor remains visible at the exact total parameter order. -/
theorem inverseHeightPower_le {n : ℕ} (w : StateAngleWord n) (hn : 0 < n)
    (κ β : Fin n → ℕ) (shift : ℕ) (hshift : 1 ≤ shift)
    (hpart : ∀ i, 0 < κ i + β i)
    (h : w.InverseIdentitySelection κ β)
    {H L t : ℝ} (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 0 ≤ t) :
    (parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1)) *
      w.selectedProduct (fun i => parameterHeightWeight H (κ i) *
        t ^ (β i + shift * κ i - 1)) ≤
      L ^ n * parameterHeightWeight H (∑ i, κ i) *
        t ^ ((∑ i, β i) + shift * (∑ i, κ i) - 1) := by
  have hh := w.selected_heightProduct_le κ hH hHL hL 0
  simp only [Nat.zero_add, w.inverseParameterOrder_eq κ β h] at hh
  rw [w.selectedProduct_mul, w.selectedProduct_natPower]
  calc
    _ = (parameterHeightWeight H w.stateArity *
          w.selectedProduct (fun i => parameterHeightWeight H (κ i))) *
        (t ^ (w.angleArity + shift * w.stateArity - 1) *
          t ^ w.selectedSum (fun i => β i + shift * κ i - 1)) := by ring
    _ ≤ (L ^ n * parameterHeightWeight H (∑ i, κ i)) *
        (t ^ (w.angleArity + shift * w.stateArity - 1) *
          t ^ w.selectedSum (fun i => β i + shift * κ i - 1)) :=
      mul_le_mul_of_nonneg_right hh (mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _))
    _ = _ := by rw [← pow_add, w.inverseDegree_eq hn κ β shift hshift hpart h]

end StateAngleWord

section GraphBounds

variable {E Y Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Binary multilinearity separates the state identity from the
vector-valued inverse factor, preserving the original slot order. -/
theorem n04NegativeInverse_graph_expansion {n : ℕ}
    (A : (E × Y) [×n]→L[ℝ] Z) (b : Fin n → E) (y : Fin n → Y) :
    A (fun i => (b i, y i)) = ∑ s : Finset (Fin n),
      A (fun i => if i ∈ s then (b i, 0) else (0, y i)) := by
  classical
  have he := A.map_add_univ
    (fun i => (b i, (0 : Y))) (fun i => ((0 : E), y i))
  have hp : (fun i => (b i, (0 : Y))) + (fun i => ((0 : E), y i)) =
      fun i => (b i, y i) := by
    funext i
    simp only [Pi.add_apply, Prod.mk_add_mk, add_zero, zero_add]
  rw [hp] at he
  simpa only [Finset.piecewise] using he

end GraphBounds

section NormedGraphBounds

variable {E Y Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The estimate for one selected term uses only the forward pure-slot
estimate and the lower inverse factors.  The first height factor and
the exact saved spatial degree are retained. -/
theorem n04NegativeInverse_selected_norm_le {n : ℕ}
    (A : (E × Y) [×n]→L[ℝ] Z) (hn : 0 < n)
    (w : StateAngleWord n) (κ β : Fin n → ℕ)
    (shift : ℕ) (hshift : 1 ≤ shift) (hpart : ∀ i, 0 < κ i + β i)
    (hselect : w.InverseIdentitySelection κ β)
    (b : Fin n → E) (y : Fin n → Y)
    {C M H L t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (houter : ‖A (fun i => if w.isState i then (b i, 0) else (0, y i))‖ ≤
      C * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) *
          w.selectedProduct (fun i => ‖y i‖))
    (hlower : ∀ i, ‖y i‖ ≤ M * parameterHeightWeight H (κ i) *
      t ^ (β i + shift * κ i - 1)) :
    ‖A (fun i => if w.isState i then (b i, 0) else (0, y i))‖ ≤
      C * M ^ n * L ^ n * parameterHeightWeight H (∑ i, κ i) *
        t ^ ((∑ i, β i) + shift * (∑ i, κ i) - 1) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hp := w.selectedProduct_mono (fun i => norm_nonneg (y i)) hlower
  have hh := w.inverseHeightPower_le hn κ β shift hshift hpart hselect hH hHL hL ht
  have hm : M ^ w.angleArity ≤ M ^ n :=
    pow_le_pow_right₀ hM (by have ha := w.arity_sum; omega)
  have hweight : 0 ≤ parameterHeightWeight H (∑ i, κ i) *
      t ^ ((∑ i, β i) + shift * (∑ i, κ i) - 1) :=
    mul_nonneg (parameterHeightWeight_nonneg hH _) (pow_nonneg ht _)
  calc
    _ ≤ (C * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1)) *
      w.selectedProduct (fun i => M * parameterHeightWeight H (κ i) *
        t ^ (β i + shift * κ i - 1)) :=
      houter.trans (mul_le_mul_of_nonneg_left hp
        (mul_nonneg (mul_nonneg hC (parameterHeightWeight_nonneg hH _))
          (pow_nonneg ht _)))
    _ = (C * M ^ w.angleArity) *
        ((parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1)) *
          w.selectedProduct (fun i => parameterHeightWeight H (κ i) *
            t ^ (β i + shift * κ i - 1))) := by
      simp only [mul_assoc, w.selectedProduct_mul, w.selectedProduct_const]
      ring
    _ ≤ (C * M ^ w.angleArity) * (L ^ n *
        parameterHeightWeight H (∑ i, κ i) *
          t ^ ((∑ i, β i) + shift * (∑ i, κ i) - 1)) :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg hC (pow_nonneg hM0 _))
    _ ≤ (C * M ^ n) * (L ^ n * parameterHeightWeight H (∑ i, κ i) *
        t ^ ((∑ i, β i) + shift * (∑ i, κ i) - 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hC)
        (by simpa only [mul_assoc] using mul_nonneg (pow_nonneg hL0 n) hweight)
    _ = _ := by ring

/-- A genuine graph partition is controlled by the forward pure-slot
estimate.  Choices using a nonsingleton state identity vanish exactly;
all remaining choices satisfy the sharp inverse degree budget. -/
theorem n04NegativeInverse_graph_norm_le {n : ℕ}
    (A : (E × Y) [×n]→L[ℝ] Z) (hn : 0 < n)
    (κ β : Fin n → ℕ) (shift : ℕ) (hshift : 1 ≤ shift)
    (hpart : ∀ i, 0 < κ i + β i)
    (b : Fin n → E) (y : Fin n → Y)
    (hidentity : ∀ i, ¬ (κ i = 1 ∧ β i = 0) → b i = 0)
    {C M H L t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (houter : ∀ w : StateAngleWord n, w.InverseIdentitySelection κ β →
      ‖A (fun i => if w.isState i then (b i, 0) else (0, y i))‖ ≤
        C * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) *
            w.selectedProduct (fun i => ‖y i‖))
    (hlower : ∀ i, ‖y i‖ ≤ M * parameterHeightWeight H (κ i) *
      t ^ (β i + shift * κ i - 1)) :
    ‖A (fun i => (b i, y i))‖ ≤
      (Fintype.card (Finset (Fin n)) : ℝ) *
        (C * M ^ n * L ^ n * parameterHeightWeight H (∑ i, κ i) *
          t ^ ((∑ i, β i) + shift * (∑ i, κ i) - 1)) := by
  classical
  let B : ℝ := C * M ^ n * L ^ n * parameterHeightWeight H (∑ i, κ i) *
    t ^ ((∑ i, β i) + shift * (∑ i, κ i) - 1)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC
      (pow_nonneg (zero_le_one.trans hM) _)) (pow_nonneg (zero_le_one.trans hL) _))
      (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _)
  have hterm (s : Finset (Fin n)) :
      ‖A (fun i => if i ∈ s then (b i, 0) else (0, y i))‖ ≤ B := by
    let w : StateAngleWord n := StateAngleWord.ofBool (fun i => decide (i ∈ s))
    have hw (i : Fin n) : w.isState i = decide (i ∈ s) := by
      simp only [w, StateAngleWord.isState_ofBool]
    have he : (fun i => if i ∈ s then (b i, (0 : Y)) else (0, y i)) =
        fun i => if w.isState i then (b i, 0) else (0, y i) := by
      funext i
      simp only [hw, decide_eq_true_eq]
    rw [he]
    by_cases hs : w.InverseIdentitySelection κ β
    · exact n04NegativeInverse_selected_norm_le A hn w κ β shift hshift hpart hs b y
        hC hM hH hHL hL ht (houter w hs) hlower
    · obtain ⟨i, hi⟩ := not_forall.mp hs
      have his : w.isState i = true := by
        by_contra his
        exact hi (fun h => False.elim (his h))
      have hbad : ¬ (κ i = 1 ∧ β i = 0) := fun hb => hi (fun _ => hb)
      have hz := A.map_coord_zero i
        (show (if w.isState i then (b i, (0 : Y)) else (0, y i)) = 0 by
          rw [his, if_true, hidentity i hbad]
          rfl)
      rw [hz, norm_zero]
      exact hB
  rw [n04NegativeInverse_graph_expansion]
  calc
    _ ≤ ∑ s : Finset (Fin n), ‖A (fun i => if i ∈ s then (b i, 0) else (0, y i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _s : Finset (Fin n), B := Finset.sum_le_sum (fun s _ => hterm s)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, B]

end NormedGraphBounds

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
  rw [tower_succ_apply, forcing_apply]
  rw [Fintype.sum_unique]
  congr 2
  change J.D 1 (x, g x)
    (fun i : Fin 1 => graph 1
      ((lower (fun k (_ : k < 1) => tower J hg hmap A hA k) 1).value x)
      (v ∘ (default : OrderedFinpartition 1).emb i)) = _
  rw [lower_self]
  congr 1
  funext i
  change (v ((default : OrderedFinpartition 1).emb i 0), (0 : Y)) = _
  congr 1
  exact congrArg v (Subsingleton.elim _ _)

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
      apply hpure 0
      cases hi : w.isState 0 with
      | false => rfl
      | true =>
          apply False.elim
          apply h
          constructor <;>
            simp only [StateAngleWord.stateArity_eq_sum, StateAngleWord.angleArity_eq_sum,
              Fin.sum_univ_one, hi, if_true]
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
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm]
  change (0 : Y) + 0 = 0
  exact zero_add 0

theorem continuousLinearJets_eq_zero {X Z : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    (L : X →L[ℝ] Z) {n : ℕ} (hn : 2 ≤ n) (x : X) :
    continuousLinearJets L n x = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm]
  rfl

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
