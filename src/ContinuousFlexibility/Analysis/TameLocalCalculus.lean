import ContinuousFlexibility.Statements.Analysis
import ContinuousFlexibility.Analysis.TameLinear

/-!
# Local tame bounds for values

This auxiliary predicate records an actual continuous map and its
order-uniform local tame bound. The neighborhood is kept as a neighborhood
in the given topology. This makes finite sums, products and composition
transparent, before a generating grading is used to choose one low-order
seminorm ball. It does not assume any differentiability or inverse theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators NNReal
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section Definition

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

/-- Local tame growth, with one neighborhood and one fixed loss at all orders. -/
def LocallyTameOn (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (U : Set E) (f : E → F) : Prop :=
  ContinuousOn f U ∧ ∀ x0 ∈ U, ∃ loss base : ℕ, ∃ W : Set E,
    W ∈ 𝓝[U] x0 ∧ ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ W, q s (f x) ≤ C * (1 + p (s + loss) x)

theorem LocallyTameOn.continuousOn {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f : E → F} (h : LocallyTameOn p q U f) : ContinuousOn f U := h.1

theorem LocallyTameOn.mono {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U V : Set E} {f : E → F} (h : LocallyTameOn p q U f) (hVU : V ⊆ U) :
    LocallyTameOn p q V f := by
  refine ⟨h.1.mono hVU, ?_⟩
  intro x0 hx0
  obtain ⟨loss, base, W, hW, hb⟩ := h.2 x0 (hVU hx0)
  exact ⟨loss, base, W, nhdsWithin_mono _ hVU hW, hb⟩

theorem LocallyTameOn.congr {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f g : E → F} (h : LocallyTameOn p q U f)
    (hfg : ∀ x ∈ U, g x = f x) : LocallyTameOn p q U g := by
  refine ⟨h.1.congr hfg, ?_⟩
  intro x0 hx0
  obtain ⟨loss, base, W, hW, hb⟩ := h.2 x0 hx0
  refine ⟨loss, base, W ∩ U, inter_mem hW self_mem_nhdsWithin, ?_⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hb s hs
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [hfg x hx.2]
  exact hbound x hx.1

theorem locallyTameOn_of_isTameLinear {p : ℕ → Seminorm ℝ E}
    {q : ℕ → Seminorm ℝ F} (L : E →L[ℝ] F) {loss base : ℕ}
    (hL : IsTameLinear p q L.toLinearMap loss base) (U : Set E) :
    LocallyTameOn p q U L := by
  refine ⟨L.continuous.continuousOn, fun x0 _ => ⟨loss, base, univ, univ_mem, ?_⟩⟩
  intro s hs
  obtain ⟨C, hC⟩ := hL s hs
  refine ⟨C, C.coe_nonneg, fun x _ => (hC x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) C.coe_nonneg

theorem locallyTameOn_const (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (U : Set E) (y : F) : LocallyTameOn p q U (fun _ => y) := by
  refine ⟨continuousOn_const, fun _ _ => ⟨0, 0, univ, univ_mem, ?_⟩⟩
  intro s _
  refine ⟨q s y, apply_nonneg _ _, fun x _ => ?_⟩
  have hp : 1 ≤ 1 + p (s + 0) x := le_add_of_nonneg_right (apply_nonneg _ _)
  exact le_mul_of_one_le_right (apply_nonneg _ _) hp

/-- Composition of value estimates needs continuity and fixed losses, without
interpolation or smoothness assumptions. -/
theorem LocallyTameOn.comp {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {r : ℕ → Seminorm ℝ G} {U : Set E} {V : Set F} {f : E → F} {g : F → G}
    (hg : LocallyTameOn q r V g) (hf : LocallyTameOn p q U f)
    (hmap : MapsTo f U V) : LocallyTameOn p r U (g ∘ f) := by
  refine ⟨hg.1.comp hf.1 hmap, ?_⟩
  intro x0 hx0
  obtain ⟨lf, bf, Wf, hWf, hbf⟩ := hf.2 x0 hx0
  obtain ⟨lg, bg, Wg, hWg, hbg⟩ := hg.2 (f x0) (hmap hx0)
  refine ⟨lf + lg, max bf bg, Wf ∩ f ⁻¹' Wg,
    inter_mem hWf ((hf.1 x0 hx0).tendsto_nhdsWithin hmap hWg), ?_⟩
  intro s hs
  obtain ⟨Cg, hCg, hgb⟩ := hbg s ((le_max_right bf bg).trans hs)
  obtain ⟨Cf, hCf, hfb⟩ := hbf (s + lg)
    (((le_max_left bf bg).trans hs).trans (Nat.le_add_right _ _))
  refine ⟨Cg * (1 + Cf), mul_nonneg hCg (by positivity), fun x hx => ?_⟩
  have ht : 0 ≤ p (s + (lf + lg)) x := apply_nonneg _ _
  have hinner : q (s + lg) (f x) ≤ Cf * (1 + p (s + (lf + lg)) x) := by
    simpa only [Nat.add_assoc, Nat.add_comm lg lf] using hfb x hx.1
  calc
    r s ((g ∘ f) x) ≤ Cg * (1 + q (s + lg) (f x)) := hgb (f x) hx.2
    _ ≤ Cg * (1 + Cf * (1 + p (s + (lf + lg)) x)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hinner) hCg
    _ ≤ Cg * (1 + Cf) * (1 + p (s + (lf + lg)) x) := by nlinarith

variable [IsTopologicalAddGroup F]

theorem LocallyTameOn.add {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) {U : Set E} {f g : E → F}
    (hf : LocallyTameOn p q U f) (hg : LocallyTameOn p q U g) :
    LocallyTameOn p q U (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro x0 hx0
  obtain ⟨lf, bf, Wf, hWf, hbf⟩ := hf.2 x0 hx0
  obtain ⟨lg, bg, Wg, hWg, hbg⟩ := hg.2 x0 hx0
  refine ⟨max lf lg, max bf bg, Wf ∩ Wg, inter_mem hWf hWg, ?_⟩
  intro s hs
  obtain ⟨Cf, hCf, hfb⟩ := hbf s ((le_max_left bf bg).trans hs)
  obtain ⟨Cg, hCg, hgb⟩ := hbg s ((le_max_right bf bg).trans hs)
  refine ⟨Cf + Cg, add_nonneg hCf hCg, fun x hx => ?_⟩
  have hf' : q s (f x) ≤ Cf * (1 + p (s + max lf lg) x) :=
    (hfb x hx.1).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hp (Nat.add_le_add_left (le_max_left lf lg) s) x)) hCf)
  have hg' : q s (g x) ≤ Cg * (1 + p (s + max lf lg) x) :=
    (hgb x hx.2).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hp (Nat.add_le_add_left (le_max_right lf lg) s) x)) hCg)
  exact (map_add_le_add (q s) (f x) (g x)).trans
    ((add_le_add hf' hg').trans_eq (by ring))

theorem LocallyTameOn.neg {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f : E → F} (hf : LocallyTameOn p q U f) :
    LocallyTameOn p q U (fun x => -f x) := by
  refine ⟨hf.1.neg, ?_⟩
  intro x0 hx0
  obtain ⟨loss, base, W, hW, hb⟩ := hf.2 x0 hx0
  refine ⟨loss, base, W, hW, fun s hs => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hb s hs
  exact ⟨C, hC, fun x hx => by simpa only [map_neg_eq_map] using hbound x hx⟩

theorem LocallyTameOn.sub {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) {U : Set E} {f g : E → F}
    (hf : LocallyTameOn p q U f) (hg : LocallyTameOn p q U g) :
    LocallyTameOn p q U (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hp hg.neg

theorem LocallyTameOn.finset_sum {ι : Type*} {p : ℕ → Seminorm ℝ E}
    {q : ℕ → Seminorm ℝ F} (hp : Monotone p) (S : Finset ι)
    {U : Set E} {f : ι → E → F} (hf : ∀ i ∈ S, LocallyTameOn p q U (f i)) :
    LocallyTameOn p q U (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using locallyTameOn_const p q U (0 : F)
  | @insert i S hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i S)).add hp
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end Definition

section Products

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

theorem pairGrading_apply (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (n : ℕ) (x : E × F) : pairGrading p q n x = p n x.1 + q n x.2 := by
  simp only [pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]

theorem pairGrading_monotone {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) (hq : Monotone q) : Monotone (pairGrading p q) := by
  intro m n hmn x
  simp only [pairGrading_apply]
  exact add_le_add (hp hmn x.1) (hq hmn x.2)

theorem LocallyTameOn.prodMk {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {r : ℕ → Seminorm ℝ G} (hp : Monotone p) {U : Set E}
    {f : E → F} {g : E → G} (hf : LocallyTameOn p q U f)
    (hg : LocallyTameOn p r U g) :
    LocallyTameOn p (pairGrading q r) U (fun x => (f x, g x)) := by
  refine ⟨hf.1.prodMk hg.1, ?_⟩
  intro x0 hx0
  obtain ⟨lf, bf, Wf, hWf, hbf⟩ := hf.2 x0 hx0
  obtain ⟨lg, bg, Wg, hWg, hbg⟩ := hg.2 x0 hx0
  refine ⟨max lf lg, max bf bg, Wf ∩ Wg, inter_mem hWf hWg, ?_⟩
  intro s hs
  obtain ⟨Cf, hCf, hfb⟩ := hbf s ((le_max_left bf bg).trans hs)
  obtain ⟨Cg, hCg, hgb⟩ := hbg s ((le_max_right bf bg).trans hs)
  refine ⟨Cf + Cg, add_nonneg hCf hCg, fun x hx => ?_⟩
  rw [pairGrading_apply]
  have hf' : q s (f x) ≤ Cf * (1 + p (s + max lf lg) x) :=
    (hfb x hx.1).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hp (Nat.add_le_add_left (le_max_left lf lg) s) x)) hCf)
  have hg' : r s (g x) ≤ Cg * (1 + p (s + max lf lg) x) :=
    (hgb x hx.2).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hp (Nat.add_le_add_left (le_max_right lf lg) s) x)) hCg)
  exact (add_le_add hf' hg').trans_eq (by ring)

variable {ι : Type*} [Fintype ι] {Y : ι → Type*}
  [∀ i, TopologicalSpace (Y i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℝ (Y i)]

/-- Finite tuples use the sum of the component seminorms. -/
def tupleGrading (q : ∀ i, ℕ → Seminorm ℝ (Y i)) (n : ℕ) : Seminorm ℝ (∀ i, Y i) :=
  ∑ i, (q i n).comp (LinearMap.proj i)

theorem tupleGrading_apply (q : ∀ i, ℕ → Seminorm ℝ (Y i)) (n : ℕ) (x : ∀ i, Y i) :
    tupleGrading q n x = ∑ i, q i n (x i) := by
  classical
  have hsum (S : Finset ι) :
      (∑ i ∈ S, (q i n).comp (LinearMap.proj i)) x = ∑ i ∈ S, q i n (x i) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, zero_apply]
    | @insert i S hi ih =>
        simp only [Finset.sum_insert hi, add_apply, Seminorm.comp_apply,
          LinearMap.proj_apply, ih]
  exact hsum Finset.univ

theorem tupleGrading_monotone (q : ∀ i, ℕ → Seminorm ℝ (Y i))
    (hq : ∀ i, Monotone (q i)) : Monotone (tupleGrading q) := by
  intro m n hmn x
  simp only [tupleGrading_apply]
  exact Finset.sum_le_sum (fun i _ => hq i hmn (x i))

theorem LocallyTameOn.pi {p : ℕ → Seminorm ℝ E}
    {q : ∀ i, ℕ → Seminorm ℝ (Y i)} (hp : Monotone p) {U : Set E}
    {f : ∀ i, E → Y i} (hf : ∀ i, LocallyTameOn p (q i) U (f i)) :
    LocallyTameOn p (tupleGrading q) U (fun x i => f i x) := by
  classical
  refine ⟨continuousOn_pi.mpr (fun i => (hf i).1), ?_⟩
  intro x0 hx0
  choose loss base W hW hb using fun i => (hf i).2 x0 hx0
  refine ⟨Finset.univ.sup loss, Finset.univ.sup base, ⋂ i, W i,
    Filter.iInter_mem.mpr hW, ?_⟩
  intro s hs
  have hbase (i : ι) : base i ≤ s := (Finset.le_sup (Finset.mem_univ i)).trans hs
  choose C hC hbound using fun i => hb i s (hbase i)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun x hx => ?_⟩
  rw [tupleGrading_apply, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact (hbound i x (mem_iInter.mp hx i)).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1)
        (hp (Nat.add_le_add_left (Finset.le_sup (Finset.mem_univ i)) s) x)) (hC i))

end Products

end ContinuousFlexibility.Analysis
