module

public import ContinuousFlexibility.Scalar.WeightedUniformTameGerm
public import ContinuousFlexibility.Scalar.WeightedTowerOperations
public import ContinuousFlexibility.Scalar.WeightedStateTopology

/-!
# Finite algebra of uniform tame germs

Every operation chooses one source ball and keeps one base and loss for its
whole actual directional tower.  The source can be the prescribed nested
scalar state space.  Bilinear operations use genuine continuous multilinear
maps together with their proved fixed two-factor estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Function ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section Basic

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
  {x0 : E} {f g : E → F} {h : E → G}

/-- A fixed tower on any open neighborhood gives a germ with its fixed loss. -/
theorem FixedNeighborhoodSmoothTame.uniformTameGerm
    {U : Set E} {base loss : ℕ}
    (hf : FixedNeighborhoodSmoothTame p q U base loss f)
    (hp : Monotone p) (ht : WithSeminorms p) (hx0 : x0 ∈ U) :
    UniformTameGerm p q x0 f := by
  obtain ⟨J, _⟩ := hf.2
  obtain ⟨b, ε, hb, hε, _, hsub⟩ :=
    exists_small_uniformTameBall hp ht (J.open_domain.mem_nhds hx0) base
  exact ⟨b, loss, ε, hε,
    (hf.restrict (isOpen_uniformTameBall ht b x0 ε) hsub).weaken hp hb le_rfl⟩

theorem UniformTameGerm.congr (hf : UniformTameGerm p q x0 f)
    (hfg : ∀ x, f x = g x) : UniformTameGerm p q x0 g := by
  obtain ⟨base, loss, ε, hε, hfu⟩ := hf
  exact ⟨base, loss, ε, hε, hfu.congr (fun x _ => hfg x)⟩

theorem UniformTameGerm.congr_on (hf : UniformTameGerm p q x0 f)
    (hp : Monotone p) (ht : WithSeminorms p)
    {W : Set E} (hW : W ∈ 𝓝 x0) (hfg : ∀ x ∈ W, f x = g x) :
    UniformTameGerm p q x0 g := by
  obtain ⟨base, loss, ε, hε, hfu⟩ := hf
  obtain ⟨J, _⟩ := hfu.2
  have hx0 : x0 ∈ {x | p base (x - x0) < ε} := by
    simpa only [Set.mem_setOf_eq, sub_self, map_zero] using hε
  obtain ⟨b, δ, hb, hδ, _, hsub⟩ := exists_small_uniformTameBall hp ht
    (inter_mem (J.open_domain.mem_nhds hx0) hW) base
  refine ⟨b, loss, δ, hδ, ?_⟩
  exact ((hfu.restrict (isOpen_uniformTameBall ht b x0 δ)
    (fun x hx => (hsub hx).1)).weaken hp hb le_rfl).congr
    (fun x hx => hfg x (hsub hx).2)

theorem uniformTameGerm_const (ht : WithSeminorms p) (x0 : E) (a : F) :
    UniformTameGerm p q x0 (fun _ => a) :=
  ⟨0, 0, 1, zero_lt_one,
    fixedNeighborhoodSmoothTame_const a (isOpen_uniformTameBall ht 0 x0 1)⟩

theorem uniformTameGerm_continuousLinear
    (ht : WithSeminorms p) (x0 : E) (L : E →L[ℝ] F)
    {base loss : ℕ} (hL : IsTameLinear p q L.toLinearMap loss base) :
    UniformTameGerm p q x0 L :=
  ⟨base, loss, 1, zero_lt_one,
    (fixedNeighborhoodSmoothTame_continuousLinear L hL).restrict
      (isOpen_uniformTameBall ht base x0 1) (subset_univ _)⟩

theorem UniformTameGerm.postcompose
    (hf : UniformTameGerm p q x0 f) (hp : Monotone p) (ht : WithSeminorms p)
    (L : F →L[ℝ] G) {linearLoss linearBase : ℕ}
    (hL : IsTameLinear q r L.toLinearMap linearLoss linearBase) :
    UniformTameGerm p r x0 (fun x => L (f x)) := by
  obtain ⟨base, loss, ε, hε, hfu⟩ := hf
  refine ⟨max base linearBase, linearLoss + loss, ε, hε, ?_⟩
  exact (hfu.postcompose hp L hL).restrict
    (isOpen_uniformTameBall ht (max base linearBase) x0 ε)
    (uniformTameBall_subset hp (le_max_left _ _) le_rfl x0)

theorem UniformTameGerm.add [IsTopologicalAddGroup F]
    (hf : UniformTameGerm p q x0 f) (hg : UniformTameGerm p q x0 g)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p q x0 (fun x => f x + g x) := by
  obtain ⟨b, ell, ε, hε, hfu⟩ := hf
  obtain ⟨c, m, δ, hδ, hgv⟩ := hg
  let W : Set E := {x | p (max b c) (x - x0) < min ε δ}
  have hW : IsOpen W := isOpen_uniformTameBall ht (max b c) x0 (min ε δ)
  have hWf : W ⊆ {x | p b (x - x0) < ε} :=
    uniformTameBall_subset hp (le_max_left _ _) (min_le_left _ _) x0
  have hWg : W ⊆ {x | p c (x - x0) < δ} :=
    uniformTameBall_subset hp (le_max_right _ _) (min_le_right _ _) x0
  exact ⟨max b c, max ell m, min ε δ, lt_min hε hδ,
    (hfu.restrict hW hWf).add (hgv.restrict hW hWg) hp⟩

theorem UniformTameGerm.prodMk
    (hf : UniformTameGerm p q x0 f) (hh : UniformTameGerm p r x0 h)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (pairGrading q r) x0 (fun x => (f x, h x)) := by
  obtain ⟨b, ell, ε, hε, hfu⟩ := hf
  obtain ⟨c, m, δ, hδ, hhv⟩ := hh
  let W : Set E := {x | p (max b c) (x - x0) < min ε δ}
  have hW : IsOpen W := isOpen_uniformTameBall ht (max b c) x0 (min ε δ)
  have hWf : W ⊆ {x | p b (x - x0) < ε} :=
    uniformTameBall_subset hp (le_max_left _ _) (min_le_left _ _) x0
  have hWh : W ⊆ {x | p c (x - x0) < δ} :=
    uniformTameBall_subset hp (le_max_right _ _) (min_le_right _ _) x0
  exact ⟨max b c, max ell m, min ε δ, lt_min hε hδ,
    (hfu.restrict hW hWf).prodMk (hhv.restrict hW hWh) hp⟩

theorem UniformTameGerm.neg [IsTopologicalAddGroup F]
    (hf : UniformTameGerm p q x0 f) (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p q x0 (fun x => -f x) := by
  exact hf.postcompose hp ht (-ContinuousLinearMap.id ℝ F) (IsTameLinear.id q).neg

theorem UniformTameGerm.sub [IsTopologicalAddGroup F]
    (hf : UniformTameGerm p q x0 f) (hg : UniformTameGerm p q x0 g)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p q x0 (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add (hg.neg hp ht) hp ht

theorem UniformTameGerm.const_smul [ContinuousSMul ℝ F]
    (hf : UniformTameGerm p q x0 f) (hp : Monotone p) (ht : WithSeminorms p) (a : ℝ) :
    UniformTameGerm p q x0 (fun x => a • f x) := by
  exact hf.postcompose hp ht (a • ContinuousLinearMap.id ℝ F) ((IsTameLinear.id q).smul a)

end Basic

section OuterBilinear

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {base loss : ℕ}

/-- Convert an actual continuous bilinear map and its fixed two-factor
estimate into a germ at any pair of inputs. -/
theorem uniformTameGerm_bilinearMultilinear
    (B : E [×2]→L[ℝ] F)
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      q s (bilinearJetValue B x y) ≤
        C * (p (s + loss) x * p base y + p base x * p (s + loss) y))
    (ht : WithSeminorms p) (z0 : E × E) :
    UniformTameGerm (pairGrading p p) q z0
      (fun z : E × E => bilinearJetValue B z.1 z.2) := by
  let P := pairGrading p p
  let U : Set (E × E) := {z | P base (z - z0) < 1}
  have hU : IsOpen U := isOpen_uniformTameBall
    (withSeminorms_pairGrading ht ht) base z0 1
  have hbound : ∀ z ∈ U, P base z ≤ 1 + P base z0 := by
    intro z hz
    calc
      P base z = P base ((z - z0) + z0) := by rw [sub_add_cancel]
      _ ≤ P base (z - z0) + P base z0 := map_add_le_add _ _ _
      _ ≤ 1 + P base z0 := add_le_add hz.le (le_refl _)
  exact ⟨base, loss, 1, zero_lt_one,
    fixedNeighborhoodSmoothTame_bilinearMultilinear B hB hU (by positivity) hbound⟩

/-- The independent scalar parameter acts with a zero-loss actual tower
on one order-zero ball around any scalar-height pair. -/
theorem uniformTameGerm_scalarSMul
    (q : ℕ → Seminorm ℝ F) (ht : WithSeminorms q) (z0 : ℝ × F) :
    UniformTameGerm (pairGrading realGrading q) q z0 (fun z : ℝ × F => z.1 • z.2) := by
  let P := pairGrading realGrading q
  let U : Set (ℝ × F) := {z | P 0 (z - z0) < 1}
  have hU : IsOpen U := isOpen_uniformTameBall
    (withSeminorms_pairGrading weighted_realGrading_withSeminorms ht) 0 z0 1
  have hbound : ∀ z ∈ U, P 0 z ≤ 1 + P 0 z0 := by
    intro z hz
    calc
      P 0 z = P 0 ((z - z0) + z0) := by rw [sub_add_cancel]
      _ ≤ P 0 (z - z0) + P 0 z0 := map_add_le_add _ _ _
      _ ≤ 1 + P 0 z0 := add_le_add hz.le (le_refl _)
  exact ⟨0, 0, 1, zero_lt_one,
    fixedNeighborhoodSmoothTame_scalarSMul q hU (by positivity) hbound⟩

end OuterBilinear

section ComposedBilinear

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {fbond : ∀ n, F (n + 1) →L[ℝ] F n}
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit F fbond)}
  {x0 : X} {f g : X → Y} {base loss : ℕ}

/-- Apply a fixed-loss continuous bilinear operation to two actual state
germs.  No literal projective-limit representation of the source is needed. -/
theorem UniformTameGerm.bilinear
    (hf : UniformTameGerm p q x0 f) (hg : UniformTameGerm p q x0 g)
    (B : Y [×2]→L[ℝ] (ProjectiveLimit F fbond))
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      r s (bilinearJetValue B x y) ≤
        C * (q (s + loss) x * q base y + q base x * q (s + loss) y))
    (hp : Monotone p) (ht : WithSeminorms p)
    (hq : Monotone q) (hqt : WithSeminorms q) :
    UniformTameGerm p r x0 (fun x => bilinearJetValue B (f x) (g x)) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : IsTopologicalAddGroup Y := hqt.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := hqt.continuousSMul
  letI : LocallyConvexSpace ℝ Y := hqt.toLocallyConvexSpace
  have hpair := hf.prodMk hg hp ht
  have houter := uniformTameGerm_bilinearMultilinear B hB hqt (f x0, g x0)
  simpa only [Function.comp_def] using
    hpair.comp houter hp ht (tamePairGrading_monotone hq hq)

theorem UniformTameGerm.smul
    {a : X → ℝ} {h : X → ProjectiveLimit F fbond}
    (ha : UniformTameGerm p realGrading x0 a) (hh : UniformTameGerm p r x0 h)
    (hp : Monotone p) (ht : WithSeminorms p)
    (hr : Monotone r) (hrt : WithSeminorms r) :
    UniformTameGerm p r x0 (fun x => a x • h x) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  have hpair := ha.prodMk hh hp ht
  have houter := uniformTameGerm_scalarSMul r hrt (a x0, h x0)
  simpa only [Function.comp_def] using
    hpair.comp houter hp ht (tamePairGrading_monotone weighted_realGrading_monotone hr)

end ComposedBilinear

end ContinuousFlexibility.Statements
