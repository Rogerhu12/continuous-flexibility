import ContinuousFlexibility.Scalar.WeightedTowerCompositionGeneric
import ContinuousFlexibility.Analysis.TameJetLocalBounds

/-!
# Uniform tame germs on one actual low-seminorm ball

A germ records one base and one loss for the entire genuine directional
tower.  Composition selects one smaller source ball using the actual source
topology; it never chooses a different ball or loss for each derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Function ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section Definition

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- One fixed low-seminorm neighborhood and one fixed loss for all orders of
the actual directional tower at the specified center. -/
def UniformTameGerm (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (x0 : E) (f : E → F) : Prop :=
  ∃ base loss : ℕ, ∃ ε : ℝ, 0 < ε ∧
    FixedNeighborhoodSmoothTame p q {x | p base (x - x0) < ε} base loss f

theorem UniformTameGerm.continuousAt
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {x0 : E} {f : E → F} (hf : UniformTameGerm p q x0 f) :
    ContinuousAt f x0 := by
  obtain ⟨base, loss, ε, hε, hbound⟩ := hf
  obtain ⟨J, _⟩ := hbound.2
  have hx0 : x0 ∈ {x | p base (x - x0) < ε} := by
    simpa only [Set.mem_setOf_eq, sub_self, map_zero] using hε
  exact J.continuousOn.continuousAt (J.open_domain.mem_nhds hx0)

end Definition

section Balls

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {p : ℕ → Seminorm ℝ E}

theorem isOpen_uniformTameBall (ht : WithSeminorms p) (base : ℕ) (x0 : E) (ε : ℝ) :
    IsOpen {x | p base (x - x0) < ε} := by
  letI : IsTopologicalAddGroup E := ht.isTopologicalAddGroup
  exact isOpen_lt ((ht.continuous_seminorm base).comp
    (continuous_id.sub continuous_const)) continuous_const

theorem uniformTameBall_subset (hp : Monotone p)
    {base base' : ℕ} (hb : base ≤ base') {ε δ : ℝ} (hε : ε ≤ δ) (x0 : E) :
    {x | p base' (x - x0) < ε} ⊆ {x | p base (x - x0) < δ} := by
  intro x hx
  exact (hp hb (x - x0)).trans_lt (hx.trans_le hε)

/-- The actual seminorm topology provides a ball inside a prescribed
neighborhood, with any required lower bound on its base and radius at most one. -/
theorem exists_small_uniformTameBall
    (hp : Monotone p) (ht : WithSeminorms p)
    {x0 : E} {W : Set E} (hW : W ∈ 𝓝 x0) (required : ℕ) :
    ∃ base : ℕ, ∃ ε : ℝ, required ≤ base ∧ 0 < ε ∧ ε ≤ 1 ∧
      {x | p base (x - x0) < ε} ⊆ W := by
  obtain ⟨b, δ, hδ, hmem⟩ := exists_seminormBall_subset_nhds hp ht hW
  refine ⟨max b required, min δ 1, le_max_right _ _, lt_min hδ zero_lt_one,
    min_le_right _ _, ?_⟩
  intro x hx
  exact hmem x ((hp (le_max_left b required) (x - x0)).trans_lt
    (hx.trans_le (min_le_left δ 1)))

/-- A ball with radius at most one uniformly bounds every seminorm below
its base, with an explicit bound depending only on its center. -/
theorem seminorm_le_on_uniformTameBall (hp : Monotone p)
    {required base : ℕ} (hb : required ≤ base)
    {x0 x : E} {ε : ℝ} (hε : ε ≤ 1) (hx : p base (x - x0) < ε) :
    p required x ≤ 1 + p required x0 := by
  calc
    p required x = p required ((x - x0) + x0) := by rw [sub_add_cancel]
    _ ≤ p required (x - x0) + p required x0 := map_add_le_add _ _ _
    _ ≤ 1 + p required x0 :=
      add_le_add (((hp hb (x - x0)).trans hx.le).trans hε) (le_refl _)

end Balls

section Composition

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)]
  {fbond : ∀ n, F (n + 1) →L[ℝ] F n}
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit F fbond)}
  {x0 : X} {f : X → Y} {g : Y → ProjectiveLimit F fbond}

/-- Genuine uniform tame germs compose on arbitrary scalar state domains.
The selected common ball works simultaneously for all directional orders. -/
theorem UniformTameGerm.comp
    (hf : UniformTameGerm p q x0 f) (hg : UniformTameGerm q r (f x0) g)
    (hp : Monotone p) (ht : WithSeminorms p) (hq : Monotone q) :
    UniformTameGerm p r x0 (g ∘ f) := by
  have hfcont := hf.continuousAt
  obtain ⟨b, ell, ε, hε, hfu⟩ := hf
  obtain ⟨c, m, δ, hδ, hgv⟩ := hg
  let U : Set X := {x | p b (x - x0) < ε}
  let V : Set Y := {y | q c (y - f x0) < δ}
  obtain ⟨J, _⟩ := hfu.2
  obtain ⟨K, _⟩ := hgv.2
  have hx0 : x0 ∈ U := by simpa only [U, Set.mem_setOf_eq, sub_self, map_zero] using hε
  have hy0 : f x0 ∈ V := by simpa only [V, Set.mem_setOf_eq, sub_self, map_zero] using hδ
  have hW : U ∩ f ⁻¹' V ∈ 𝓝 x0 :=
    inter_mem (J.open_domain.mem_nhds hx0)
      (hfcont.preimage_mem_nhds (K.open_domain.mem_nhds hy0))
  obtain ⟨base, η, hbase, hη, hη1, hsub⟩ :=
    exists_small_uniformTameBall hp ht hW (max b c + ell)
  let W : Set X := {x | p base (x - x0) < η}
  have hWo : IsOpen W := isOpen_uniformTameBall ht base x0 η
  have hinner : FixedNeighborhoodSmoothTame p q W b ell f :=
    hfu.restrict hWo (fun x hx => (hsub hx).1)
  have hmap : MapsTo f W V := fun x hx => (hsub hx).2
  have hlow : ∀ x ∈ W, p (max b c + ell) x ≤ 1 + p (max b c + ell) x0 :=
    fun x hx => seminorm_le_on_uniformTameBall hp hbase hη1 hx
  have hcomp := hinner.comp_generic hgv hp hq hmap
    (by positivity : 0 ≤ 1 + p (max b c + ell) x0) hlow
  exact ⟨base, ell + m, η, hη, hcomp.weaken hp hbase le_rfl⟩

end Composition

end ContinuousFlexibility.Statements
