import ContinuousFlexibility.Analysis.N01cFlowHighestVariation

/-!
# Continuous multilinear candidates for an actual implicit family

The positive jets of a solution to `H (x, g x) = 0` are determined by
the inverse spatial differential and strictly lower solution jets.
The ordered-partition forcing below sets the current unknown jet to
zero. Strong recursion therefore constructs every order without an
assumed parameter derivative of the solution.

This module proves joint continuity and the exact algebraic highest-term
identity. Identification with actual derivatives is a separate step.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology BigOperators

section HighestTerm

variable {E Y Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z]

/-- The unique single-block partition contains the entire highest jet.
The identity holds for vector outputs as well as scalar outputs. -/
theorem n04NegativeGeometry_partition_highest_difference {n : ℕ} (hn : 0 < n)
    (O : ∀ k : ℕ, Y [×k]→L[ℝ] Z)
    (A B : ∀ k : ℕ, E [×k]→L[ℝ] Y)
    (hAB : ∀ k, k < n → A k = B k) (v : Fin n → E) :
    (∑ c : _root_.OrderedFinpartition n,
      O c.length (fun i => A (c.partSize i) (v ∘ c.emb i))) -
      (∑ c : _root_.OrderedFinpartition n,
        O c.length (fun i => B (c.partSize i) (v ∘ c.emb i))) =
      O 1 (fun _ : Fin 1 => A n v - B n v) := by
  classical
  let c₀ := OrderedFinpartition.singleBlock n hn
  rw [← Finset.sum_sub_distrib]
  have hs : (∑ c : _root_.OrderedFinpartition n,
      (O c.length (fun i => A (c.partSize i) (v ∘ c.emb i)) -
        O c.length (fun i => B (c.partSize i) (v ∘ c.emb i)))) =
      O c₀.length (fun i => A (c₀.partSize i) (v ∘ c₀.emb i)) -
        O c₀.length (fun i => B (c₀.partSize i) (v ∘ c₀.emb i)) := by
    apply Finset.sum_eq_single c₀
    · intro c _ hc
      apply sub_eq_zero.mpr
      congr 1
      funext i
      rw [hAB _ (OrderedFinpartition.partSize_lt_of_ne_singleBlock c hn hc i)]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [hs]
  change O 1 (fun _ : Fin 1 => A n v) - O 1 (fun _ : Fin 1 => B n v) = _
  let L : Y →L[ℝ] Z :=
    (ContinuousMultilinearMap.ofSubsingleton ℝ Y Z (0 : Fin 1)).symm (O 1)
  exact (map_sub L (A n v) (B n v)).symm

end HighestTerm

section Candidates

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- One candidate order, with the precise joint evaluation continuity
required by a genuine directional tower. -/
structure N04NegativeGeometryImplicitJet (U : Set E) (Y : Type*)
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (n : ℕ) where
  value : E → E [×n]→L[ℝ] Y
  continuous : ContinuousOn
    (fun p : E × (Fin n → E) => value p.1 p.2) (U ×ˢ univ)

namespace N04NegativeGeometryImplicitJet

def parameter : (n : ℕ) → E [×n]→L[ℝ] (E × Y)
  | 0 => 0
  | 1 => ContinuousMultilinearMap.ofSubsingleton ℝ E (E × Y) (0 : Fin 1)
      (ContinuousLinearMap.inl ℝ E Y)
  | _ + 2 => 0

def graph (n : ℕ) (A : E [×n]→L[ℝ] Y) : E [×n]→L[ℝ] (E × Y) :=
  parameter n + (ContinuousLinearMap.inr ℝ E Y).compContinuousMultilinearMap A

@[simp] theorem graph_apply (n : ℕ) (A : E [×n]→L[ℝ] Y) (v : Fin n → E) :
    graph n A v = parameter n v + (0, A v) := rfl

theorem graph_natural
    {P : Type*} [TopologicalSpace P] [AddCommGroup P] [Module ℝ P]
    [IsTopologicalAddGroup P] [ContinuousSMul ℝ P]
    (L : P →L[ℝ] E) (n : ℕ)
    (A : P [×n]→L[ℝ] Y) (B : E [×n]→L[ℝ] Y) (v : Fin n → P)
    (h : A v = B (fun i => L (v i))) :
    (L.prodMap (ContinuousLinearMap.id ℝ Y)) (graph n A v) =
      graph n B (fun i => L (v i)) := by
  have hi : (L.prodMap (ContinuousLinearMap.id ℝ Y))
      (parameter n v) = parameter n (fun i => L (v i)) := by
    cases n with
    | zero => exact map_zero _
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => exact map_zero _
  rw [graph_apply, map_add, hi, graph_apply]
  have hy : (L.prodMap (ContinuousLinearMap.id ℝ Y)) (0, A v) =
      (0, B (fun i => L (v i))) := by
    change (L 0, A v) = _
    rw [map_zero, h]
  rw [hy]

def zero (U : Set E) (n : ℕ) : N04NegativeGeometryImplicitJet U Y n where
  value := fun _ => 0
  continuous := continuousOn_const

def ofContinuous {U : Set E} {g : E → Y} (hg : ContinuousOn g U) :
    N04NegativeGeometryImplicitJet U Y 0 where
  value := fun x => ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (g x)
  continuous := hg.comp continuous_fst.continuousOn (fun _ hp => hp.1)

def lower {U : Set E} {N : ℕ}
    (B : ∀ k : ℕ, k < N → N04NegativeGeometryImplicitJet U Y k) (k : ℕ) :
    N04NegativeGeometryImplicitJet U Y k :=
  if hk : k < N then B k hk else zero U k

theorem lower_of_lt {U : Set E} {N k : ℕ}
    (B : ∀ j : ℕ, j < N → N04NegativeGeometryImplicitJet U Y j) (hk : k < N) :
    lower B k = B k hk := by simp only [lower, dif_pos hk]

@[simp] theorem lower_self {U : Set E} {N : ℕ}
    (B : ∀ k : ℕ, k < N → N04NegativeGeometryImplicitJet U Y k) :
    lower B N = zero U N := by
  simp only [lower, lt_self_iff_false, dite_false]

theorem continuous_graph_reindex {U : Set E} {n N : ℕ}
    (B : N04NegativeGeometryImplicitJet U Y n) (σ : Fin n → Fin N) :
    ContinuousOn (fun p : E × (Fin N → E) =>
      graph n (B.value p.1) (p.2 ∘ σ)) (U ×ˢ univ) := by
  have hr : Continuous (fun p : E × (Fin N → E) => p.2 ∘ σ) :=
    continuous_pi (fun i => (continuous_apply (σ i)).comp continuous_snd)
  have hv : ContinuousOn (fun p : E × (Fin N → E) => B.value p.1 (p.2 ∘ σ))
      (U ×ˢ univ) :=
    B.continuous.comp (continuous_fst.prodMk hr).continuousOn
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hp : ContinuousOn (fun p : E × (Fin N → E) => parameter n (p.2 ∘ σ))
      (U ×ˢ univ) := ((parameter n).cont.comp hr).continuousOn
  have he : (fun p : E × (Fin N → E) => graph n (B.value p.1) (p.2 ∘ σ)) =
      (fun p => parameter n (p.2 ∘ σ) + ((0 : E), B.value p.1 (p.2 ∘ σ))) :=
    funext (fun p => graph_apply n (B.value p.1) (p.2 ∘ σ))
  rw [he]
  exact hp.add (continuousOn_const.prodMk hv)

def forcing {U : Set E} {V : Set Y} {H : E × Y → Y} {N : ℕ}
    (J : SmoothDirections (U ×ˢ V) H) (g : E → Y)
    (B : ∀ k : ℕ, k < N → N04NegativeGeometryImplicitJet U Y k)
    (x : E) : E [×N]→L[ℝ] Y :=
  ∑ c : _root_.OrderedFinpartition N,
    projectivePartitionMultilinear c (J.D c.length (x, g x))
      (fun i => graph (c.partSize i) ((lower B (c.partSize i)).value x))

theorem forcing_apply {U : Set E} {V : Set Y} {H : E × Y → Y} {N : ℕ}
    (J : SmoothDirections (U ×ˢ V) H) (g : E → Y)
    (B : ∀ k : ℕ, k < N → N04NegativeGeometryImplicitJet U Y k)
    (x : E) (v : Fin N → E) :
    forcing J g B x v = ∑ c : _root_.OrderedFinpartition N,
      J.D c.length (x, g x)
        (fun i => graph (c.partSize i) ((lower B (c.partSize i)).value x)
          (v ∘ c.emb i)) := by
  simp only [forcing, ContinuousMultilinearMap.sum_apply,
    projectivePartitionMultilinear_apply]

theorem continuous_forcing {U : Set E} {V : Set Y} {H : E × Y → Y}
    {g : E → Y} {N : ℕ} (J : SmoothDirections (U ×ˢ V) H)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (B : ∀ k : ℕ, k < N → N04NegativeGeometryImplicitJet U Y k) :
    ContinuousOn (fun p : E × (Fin N → E) => forcing J g B p.1 p.2)
      (U ×ˢ univ) := by
  simp only [forcing_apply]
  apply continuousOn_finsetSum Finset.univ
  intro c _
  have hb : ContinuousOn (fun p : E × (Fin N → E) => (p.1, g p.1))
      (U ×ˢ univ) :=
    continuous_fst.continuousOn.prodMk
      (hg.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  have hv : ContinuousOn (fun p : E × (Fin N → E) =>
      fun i => graph (c.partSize i) ((lower B (c.partSize i)).value p.1)
        (p.2 ∘ c.emb i)) (U ×ˢ univ) :=
    continuousOn_pi.mpr (fun i =>
      continuous_graph_reindex (lower B (c.partSize i)) (c.emb i))
  exact (J.continuous c.length).comp (hb.prodMk hv)
    (fun _ hp => ⟨⟨hp.1, hmap hp.1⟩, mem_univ _⟩)

def next {U : Set E} {V : Set Y} {H : E × Y → Y} {g : E → Y}
    (J : SmoothDirections (U ×ˢ V) H)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U) (N : ℕ)
    (B : ∀ k : ℕ, k < N → N04NegativeGeometryImplicitJet U Y k) :
    N04NegativeGeometryImplicitJet U Y N where
  value x := -(A x).compContinuousMultilinearMap (forcing J g B x)
  continuous := ((hA.comp continuous_fst.continuousOn (fun _ hp => hp.1)).clm_apply
    (continuous_forcing J hg hmap B)).neg

/-- Each positive candidate is obtained from strictly lower orders;
the inverse spatial differential is an actual continuous linear map. -/
def tower {U : Set E} {V : Set Y} {H : E × Y → Y} {g : E → Y}
    (J : SmoothDirections (U ×ˢ V) H)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U) (n : ℕ) :
    N04NegativeGeometryImplicitJet U Y n :=
  match n with
  | 0 => ofContinuous hg
  | n + 1 => next J hg hmap A hA (n + 1)
      (fun k hk => tower J hg hmap A hA k)
termination_by n
decreasing_by exact hk

theorem tower_zero_apply {U : Set E} {V : Set Y} {H : E × Y → Y} {g : E → Y}
    (J : SmoothDirections (U ×ˢ V) H)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (x : E) (v : Fin 0 → E) : (tower J hg hmap A hA 0).value x v = g x := by
  rw [tower]
  rfl

theorem tower_succ_apply {U : Set E} {V : Set Y} {H : E × Y → Y} {g : E → Y}
    (J : SmoothDirections (U ×ˢ V) H)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (n : ℕ) (x : E) (v : Fin (n + 1) → E) :
    (tower J hg hmap A hA (n + 1)).value x v =
      -A x (forcing J g (fun k (_ : k < n + 1) => tower J hg hmap A hA k) x v) := by
  rw [tower]
  rfl

end N04NegativeGeometryImplicitJet

end Candidates

end ContinuousFlexibility.Analysis
