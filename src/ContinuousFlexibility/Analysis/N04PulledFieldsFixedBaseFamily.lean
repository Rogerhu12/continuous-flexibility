module

public import ContinuousFlexibility.Analysis.TameUniformSmoothFamily
public import ContinuousFlexibility.Analysis.TameFixedBaseCompositionBounds

/-!
# Genuine families with one low base at every parameter order

This certificate retains the actual directional towers and puts one low
base before all parameter orders. Each high loss is selected before the
spatial order and low-box radius. The elementary closure lemmas preserve
these quantifiers; they do not infer bounds from qualitative smoothness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {I E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

/-- A family of genuine towers whose low base is independent of the
parameter order. The high loss may depend on that order. -/
def N04PulledFieldsFixedBaseFamily
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (U : Set E) (f : I → E → F) : Prop :=
  ∃ J : ∀ i, SmoothDirections U (f i), ∃ B : ℕ, ∃ d : ℕ → ℕ,
    ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ v : Fin n → E,
        q s ((J i).D n x v) ≤ C * tameJetSize p n s (d n) B x v

theorem N04PulledFieldsFixedBaseFamily.congr
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (heq : ∀ i x, x ∈ U → f i x = g i x) :
    N04PulledFieldsFixedBaseFamily p q U g := by
  obtain ⟨J, B, d, h⟩ := hf
  exact ⟨fun i => (J i).congr (heq i), B, d, h⟩

theorem N04PulledFieldsFixedBaseFamily.reindex
    {K : Type*} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f) (a : K → I) :
    N04PulledFieldsFixedBaseFamily p q U (fun k => f (a k)) := by
  obtain ⟨J, B, d, h⟩ := hf
  refine ⟨fun k => J (a k), B, d, fun n R hR s => ?_⟩
  let data := h n R hR s
  exact ⟨data.choose, data.choose_spec.1, fun k => data.choose_spec.2 (a k)⟩

theorem N04PulledFieldsFixedBaseFamily.restrict
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U V : Set E}
    {f : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (hV : IsOpen V) (hVU : V ⊆ U) :
    N04PulledFieldsFixedBaseFamily p q V f := by
  obtain ⟨J, B, d, h⟩ := hf
  refine ⟨fun i => smoothDirectionsRestrict (J i) hV hVU, B, d, fun n R hR s => ?_⟩
  let data := h n R hR s
  exact ⟨data.choose, data.choose_spec.1, fun i x hx => data.choose_spec.2 i x (hVU hx)⟩

/-- Uniqueness transfers the same bound to every supplied genuine tower. -/
theorem N04PulledFieldsFixedBaseFamily.oneHigh
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f) :
    ∃ B : ℕ, ∃ d : ℕ → ℕ, ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (K : SmoothDirections U (f i)) x, x ∈ U → p B x ≤ R →
      ∀ v : Fin n → E, q s (K.D n x v) ≤ C * tameJetSize p n s (d n) B x v := by
  obtain ⟨J, B, d, h⟩ := hf
  refine ⟨B, d, fun n R hR s => ?_⟩
  let data := h n R hR s
  refine ⟨data.choose, data.choose_spec.1, fun i K x hx hbx v => ?_⟩
  rw [K.unique (J i) n x hx]
  exact data.choose_spec.2 i x hx hbx v

theorem N04PulledFieldsFixedBaseFamily.postContinuousLinear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (L : I → F →L[ℝ] G) (loss : ℕ)
    (hL : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i y, r s (L i y) ≤ C * q (s + loss) y) :
    N04PulledFieldsFixedBaseFamily p r U (fun i x => L i (f i x)) := by
  obtain ⟨J, B, d, h⟩ := hf
  refine ⟨fun i => smoothDirectionsPostContinuousLinear (J i) (L i), B,
    fun n => loss + d n, fun n R hR s => ?_⟩
  let lin := hL s
  let data := h n R hR (s + loss)
  refine ⟨lin.choose * data.choose, mul_nonneg lin.choose_spec.1 data.choose_spec.1,
    fun i x hx hbx v => ?_⟩
  change r s (L i ((J i).D n x v)) ≤ _
  calc
    _ ≤ lin.choose * q (s + loss) ((J i).D n x v) := lin.choose_spec.2 i _
    _ ≤ lin.choose * (data.choose * tameJetSize p n (s + loss) (d n) B x v) :=
      mul_le_mul_of_nonneg_left (data.choose_spec.2 i x hx hbx v) lin.choose_spec.1
    _ = _ := by simp only [tameJetSize, Nat.add_assoc]; ring

theorem N04PulledFieldsFixedBaseFamily.postTameContinuousLinear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (L : F →L[ℝ] G) {loss : ℕ} (hL : IsTameLinear q r L.toLinearMap loss 0) :
    N04PulledFieldsFixedBaseFamily p r U (fun i x => L (f i x)) := by
  apply hf.postContinuousLinear (fun _ => L) loss
  intro s
  let data := hL s (Nat.zero_le s)
  exact ⟨data.choose, data.choose.coe_nonneg, fun _ y => data.choose_spec y⟩

theorem N04PulledFieldsFixedBaseFamily.add
    [IsTopologicalAddGroup F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (hp : Monotone p) (hg : N04PulledFieldsFixedBaseFamily p q U g) :
    N04PulledFieldsFixedBaseFamily p q U (fun i x => f i x + g i x) := by
  obtain ⟨J, BJ, d, hJ⟩ := hf
  obtain ⟨K, BK, e, hK⟩ := hg
  refine ⟨fun i => smoothDirectionsAdd (J i) (K i), max BJ BK,
    fun n => max (d n) (e n), fun n R hR s => ?_⟩
  let left := hJ n R hR s
  let right := hK n R hR s
  refine ⟨left.choose + right.choose, add_nonneg left.choose_spec.1 right.choose_spec.1,
    fun i x hx hbx v => ?_⟩
  have hleft := (left.choose_spec.2 i x hx ((hp (le_max_left _ _) x).trans hbx) v).trans
    (mul_le_mul_of_nonneg_left
      (tameJetSize_mono hp (loss' := max (d n) (e n)) (base' := max BJ BK)
        (le_max_left _ _) (le_max_left _ _) n s x v) left.choose_spec.1)
  have hright := (right.choose_spec.2 i x hx ((hp (le_max_right _ _) x).trans hbx) v).trans
    (mul_le_mul_of_nonneg_left
      (tameJetSize_mono hp (loss' := max (d n) (e n)) (base' := max BJ BK)
        (le_max_right _ _) (le_max_right _ _) n s x v) right.choose_spec.1)
  change q s ((J i).D n x v + (K i).D n x v) ≤ _
  exact ((map_add_le_add (q s) _ _).trans (add_le_add hleft hright)).trans_eq
    (by ring)

theorem N04PulledFieldsFixedBaseFamily.neg
    [ContinuousNeg F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f) :
    N04PulledFieldsFixedBaseFamily p q U (fun i x => -f i x) := by
  let L : F →L[ℝ] F := { toLinearMap := -LinearMap.id, cont := continuous_neg }
  exact hf.postContinuousLinear (fun _ => L) 0
    (fun s => ⟨1, zero_le_one, fun _ y => by
      change q s (-y) ≤ 1 * q (s + 0) y
      simp only [map_neg_eq_map, Nat.add_zero, one_mul, le_refl]⟩)

theorem N04PulledFieldsFixedBaseFamily.sub
    [IsTopologicalAddGroup F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (hp : Monotone p) (hg : N04PulledFieldsFixedBaseFamily p q U g) :
    N04PulledFieldsFixedBaseFamily p q U (fun i x => f i x - g i x) :=
  (hf.add hp hg.neg).congr (fun _ _ _ => (sub_eq_add_neg _ _).symm)

theorem N04PulledFieldsFixedBaseFamily.prodMk
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} {g : I → E → G}
    (hf : N04PulledFieldsFixedBaseFamily p q U f) (hp : Monotone p)
    (hg : N04PulledFieldsFixedBaseFamily p r U g) :
    N04PulledFieldsFixedBaseFamily p (pairGrading q r) U (fun i x => (f i x, g i x)) := by
  obtain ⟨J, BJ, d, hJ⟩ := hf
  obtain ⟨K, BK, e, hK⟩ := hg
  refine ⟨fun i => smoothDirectionsProd (J i) (K i), max BJ BK,
    fun n => max (d n) (e n), fun n R hR s => ?_⟩
  let left := hJ n R hR s
  let right := hK n R hR s
  refine ⟨left.choose + right.choose, add_nonneg left.choose_spec.1 right.choose_spec.1,
    fun i x hx hbx v => ?_⟩
  have hleft := (left.choose_spec.2 i x hx ((hp (le_max_left _ _) x).trans hbx) v).trans
    (mul_le_mul_of_nonneg_left
      (tameJetSize_mono hp (loss' := max (d n) (e n)) (base' := max BJ BK)
        (le_max_left _ _) (le_max_left _ _) n s x v) left.choose_spec.1)
  have hright := (right.choose_spec.2 i x hx ((hp (le_max_right _ _) x).trans hbx) v).trans
    (mul_le_mul_of_nonneg_left
      (tameJetSize_mono hp (loss' := max (d n) (e n)) (base' := max BJ BK)
        (le_max_right _ _) (le_max_right _ _) n s x v) right.choose_spec.1)
  change pairGrading q r s ((J i).D n x v, (K i).D n x v) ≤ _
  rw [pairGrading_apply]
  exact (add_le_add hleft hright).trans_eq (by ring)

/-- Continuous linear families have a common low base because all jets
above order one vanish exactly. -/
theorem n04PulledFields_fixedBaseFamily_linear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    (hU : IsOpen U) (L : I → E →L[ℝ] F) (loss : ℕ)
    (hL : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, q s (L i x) ≤ C * p (s + loss) x) :
    N04PulledFieldsFixedBaseFamily p q U (fun i x => L i x) := by
  refine ⟨fun i => smoothDirectionsOfJets hU (continuousLinearJets (L i))
    (hasProjectiveJetsOn_continuousLinear (L i) U), 0, fun _ => loss, fun n R hR s => ?_⟩
  let data := hL s
  refine ⟨data.choose, data.choose_spec.1, fun i x hx hbx v => ?_⟩
  change q s (continuousLinearJets (L i) n x v) ≤ _
  cases n with
  | zero =>
      rw [tameJetSize_zero]
      exact (data.choose_spec.2 i x).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) data.choose_spec.1)
  | succ n =>
      cases n with
      | zero =>
          rw [tameJetSize_one]
          exact (data.choose_spec.2 i (v 0)).trans
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) data.choose_spec.1)
      | succ n =>
          change q s 0 ≤ _
          rw [map_zero]
          exact mul_nonneg data.choose_spec.1 (tameJetSize_nonneg _ _ _ _ _ _ _)

end ContinuousFlexibility.Analysis
