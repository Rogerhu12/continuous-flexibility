import ContinuousFlexibility.Radial.DeepTailPhysicalCoefficients
import ContinuousFlexibility.Radial.DeepTailPhysicalDecay
import ContinuousFlexibility.Radial.DeepTailPhysicalSource
import ContinuousFlexibility.Radial.TailMassResistanceData
import ContinuousFlexibility.Radial.MorseChainFlatExtension
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Flatness in the original physical radius

The physical cells are the images of the actual outward tail edges.
Their inherited profile-distance bounds turn the cubic attenuation into
quadratic bounds independent of the cell index. Continuity fills the nodes
that are omitted from the open-cell localization convention.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The actual physical radial interval corresponding to one outward edge. -/
def tailPhysicalEdge (T : DeepTailData) (right : Bool) (n : ℕ) : Set ℝ :=
  tailPhysicalRadius right '' Ioo (T.node n) (T.node (n + 1))

theorem tailPhysicalEdge_true (T : DeepTailData) (n : ℕ) :
    tailPhysicalEdge T true n = Ioo (exp (T.node n)) (exp (T.node (n + 1))) := by
  exact image_exp_Ioo _ _

theorem tailPhysicalEdge_false (T : DeepTailData) (n : ℕ) :
    tailPhysicalEdge T false n = Ioo (exp (-T.node (n + 1))) (exp (-T.node n)) := by
  change (exp ∘ Neg.neg) '' Ioo (T.node n) (T.node (n + 1)) = _
  rw [Set.image_comp, Set.image_neg_Ioo, image_exp_Ioo]

theorem isOpen_tailPhysicalEdge (T : DeepTailData) (right : Bool) (n : ℕ) :
    IsOpen (tailPhysicalEdge T right n) := by
  cases right
  · rw [tailPhysicalEdge_false]
    exact isOpen_Ioo
  · rw [tailPhysicalEdge_true]
    exact isOpen_Ioo

theorem tailPhysicalEdge_subset_core {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hT : DeepTailHypotheses T)
    (hphysical : TailPhysicalRelation D T right j start) (n : ℕ) :
    tailPhysicalEdge T right n ⊆ radialCore D := by
  rintro r ⟨x, hx, rfl⟩
  exact (hphysical.2.2.1 x
    ⟨(deepTail_entrance_le_node hT n).trans_lt hx.1,
      hx.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩).1

/-- Both orientation conventions place an edge in its own physical label
or the next label. No localization assumption at the nodes is needed. -/
theorem tailPhysicalEdge_label {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ}
    (hphysical : TailPhysicalRelation D T right j start)
    (n : ℕ) {r : ℝ} (hr : r ∈ tailPhysicalEdge T right n) :
    ∃ m : ℕ, r ∈ D.cells m ∧ start + n ≤ D.cellIndex m ∧
      D.cellIndex m ≤ start + n + 1 := by
  obtain ⟨x, hx, rfl⟩ := hr
  have hloc := hphysical.2.2.2.1
  cases right
  · change (∀ n, ∃ capStart : ℝ, T.massEnd n < capStart ∧
      capStart < T.node (n + 1) ∧ ∀ x ∈ Ioo (T.node n) (T.node (n + 1)),
      TailPhysicalCellAt D false (if x < capStart then start + n else start + n + 1) x) ∧ _ at hloc
    obtain ⟨cap, hcap, hcap', hcell⟩ := hloc.1 n
    obtain ⟨m, hi, hm⟩ := hcell x hx
    refine ⟨m, hm, ?_, ?_⟩ <;> rw [hi] <;> split_ifs <;> omega
  · change T.entrance = T.node 0 ∧
      (∀ n x, x ∈ Ioo (T.node n) (T.node (n + 1)) →
        TailPhysicalCellAt D true (start + n) x) at hloc
    obtain ⟨m, hi, hm⟩ := hloc.2 n x hx
    exact ⟨m, hm, by omega, by omega⟩

/-- The cellwise attenuation gives a common bound by the square of the
actual distance to the two radial endpoints. -/
theorem physicalCellBound_quadratic {D : ReferenceData} {cells : ℕ → Set ℝ}
    {start : ℕ} {f : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hlabel : ∀ n r, r ∈ cells n → ∃ m : ℕ,
      r ∈ D.cells m ∧ D.cellIndex m ≤ start + n + 1)
    (hf : PhysicalCellBound cells (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n))) f) :
    ∃ K : ℝ, 0 < K ∧ ∀ n r, r ∈ cells n →
      |f r| ≤ K * (min (r - D.a) (D.b - r)) ^ 2 := by
  obtain ⟨A, hA, hbound⟩ := hf
  obtain ⟨C, hgeom, hpart, hC, hnonempty, hfinite, hlocal, hdist, hrest⟩ := hD
  have hd0 : 0 < (C 0)⁻¹ := inv_pos.mpr (hC 0)
  obtain ⟨K, hK, hweight⟩ := physicalEnvelope_le_distance_power A 2 2 hd0
  refine ⟨A * K, mul_pos hA hK, fun n r hr => ?_⟩
  obtain ⟨m, hm, hi⟩ := hlabel n r hr
  have hiR : (D.cellIndex m : ℝ) + 1 ≤ ((start + n : ℕ) : ℝ) + 2 := by
    exact_mod_cast (show D.cellIndex m + 1 ≤ start + n + 2 by omega)
  have hsq := pow_le_pow_left₀ (show 0 ≤ (D.cellIndex m : ℝ) + 1 by positivity) hiR 2
  have hd : (C 0)⁻¹ * exp (-(((start + n : ℕ) : ℝ) + 2) ^ 2) ≤
      min (r - D.a) (D.b - r) :=
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hsq)) hd0.le).trans
      (hdist m r hm).1
  calc
    _ ≤ A * radialE (start + n) ^ A * exp (-radialS (start + n)) := hbound n r hr
    _ = A * (radialE (start + n) ^ A * exp (-radialS (start + n))) := by ring
    _ ≤ A * (K * (min (r - D.a) (D.b - r)) ^ 2) :=
      mul_le_mul_of_nonneg_left (hweight (start + n) _ hd) hA.le
    _ = _ := by ring

/-- A bound on every open outward edge also holds at its left node by
continuity. This is the missing-node step for the physical localization. -/
theorem tail_bound_at_nodes {node : ℕ → ℝ} {f g : ℝ → ℝ}
    (hnode : StrictMono node) (hf : ∀ n, ContinuousAt f (node n))
    (hg : ∀ n, ContinuousAt g (node n))
    (hb : ∀ n x, x ∈ Ioo (node n) (node (n + 1)) → f x ≤ g x) :
    ∀ n, f (node n) ≤ g (node n) := by
  intro n
  have hf' : Tendsto f (𝓝[>] (node n)) (𝓝 (f (node n))) :=
    (hf n).tendsto.mono_left nhdsWithin_le_nhds
  have hg' : Tendsto g (𝓝[>] (node n)) (𝓝 (g (node n))) :=
    (hg n).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hf' hg'
    ((Ioo_mem_nhdsGT (hnode (Nat.lt_succ_self n))).mono (fun x hx => hb n x hx))

/-- Together the open edges and the continuity-filled nodes cover the
entire tail after its first mass entrance. -/
theorem tail_bound_on_Ico_of_edge_bound {node : ℕ → ℝ} {endpoint : ℝ}
    {f g : ℝ → ℝ} (hnode : StrictMono node)
    (hlim : Tendsto node atTop (𝓝 endpoint))
    (hf : ∀ n, ContinuousAt f (node n)) (hg : ∀ n, ContinuousAt g (node n))
    (hb : ∀ n x, x ∈ Ioo (node n) (node (n + 1)) → f x ≤ g x) :
    ∀ x ∈ Ico (node 0) endpoint, f x ≤ g x := by
  intro x hx
  obtain ⟨n, hn⟩ := morse_outward_block_exists hlim hx.1 hx.2
  rcases eq_or_lt_of_le hn.1 with heq | hlt
  · rw [← heq]
    exact tail_bound_at_nodes hnode hf hg hb n
  · exact hb n x ⟨hlt, hn.2⟩

end ContinuousFlexibility.Radial
