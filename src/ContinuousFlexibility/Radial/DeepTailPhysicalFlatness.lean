import ContinuousFlexibility.Radial.DeepTailPhysicalCoefficients
import ContinuousFlexibility.Radial.DeepTailPhysicalDecay
import ContinuousFlexibility.Radial.DeepTailPhysicalLift
import ContinuousFlexibility.Radial.DeepTailPhysicalExtension
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
    (Filter.mem_of_superset (Ioo_mem_nhdsGT (hnode (Nat.lt_succ_self n)))
      (fun x hx => hb n x hx))

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

/-- Repeated actual derivatives preserve smoothness at a point. -/
theorem physical_contDiffAt_iteratedDeriv {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (k : ℕ) : ContDiffAt ℝ ∞ (iteratedDeriv k f) x := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.derivWithin (by simp)

theorem tailNaturalLift_contDiffAt_node {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hu : TailNaturalEquation T u) (n : ℕ) :
    ContDiffAt ℝ ∞ (tailPhysicalLift D right j u) (tailPhysicalRadius right (T.node n)) := by
  apply contDiffAt_tailPhysicalLift (tailPhysicalEndpoint_pos hD right).ne'
    (tailPhysicalRadius_pos right (T.node n))
  rw [tailPhysicalLog_radius]
  rcases eq_or_lt_of_le (deepTail_entrance_le_node hT n) with heq | hlt
  · rw [← heq]
    exact hu.1
  · exact tailNatural_contDiffAt hu ⟨hlt, deepTail_node_lt_endpoint hT n⟩

/-- Once the height and flux have the node envelope on whole edges, the
actual physical flux system propagates it to every radial derivative. -/
theorem tailNaturalLift_jet_bounds {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hu : TailNaturalEquation T u)
    (hv : PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n))) (tailPhysicalLift D right j u))
    (hq : PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n))) (tailPhysicalFlux D right j u)) :
    ∀ k, PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n)))
        (iteratedDeriv k (tailPhysicalLift D right j u)) := by
  have hlabel : ∀ n r, r ∈ tailPhysicalEdge T right n → ∃ m : ℕ,
      r ∈ D.cells m ∧ D.cellIndex m ≤ start + n + 1 := by
    intro n r hr
    obtain ⟨m, hm, hlo, hhi⟩ := tailPhysicalEdge_label hphysical n hr
    exact ⟨m, hm, hhi⟩
  have hc := physical_flux_coefficient_jets hD hlabel ((j : ℝ) ^ 2)
  have hx (n : ℕ) {x : ℝ} (h : x ∈ Ioo (T.node n) (T.node (n + 1))) :
      x ∈ Ioo T.entrance T.endpoint :=
    ⟨(deepTail_entrance_le_node hT n).trans_lt h.1,
      h.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩
  obtain ⟨C, hC⟩ := hD
  have hw : ContDiff ℝ ∞ D.w := hC.1.2.2.1.1
  have hw' : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hjets := physicalJets_of_firstOrderSystem
    (isOpen_tailPhysicalEdge T right)
    (fun n => one_le_exp_iff.mpr (radialQ_nonneg (start + n)))
    (fun n => (exp_pos _).le)
    (f := tailPhysicalLift D right j u) (g := tailPhysicalFlux D right j u)
    (a := fun r => (D.w r)⁻¹)
    (b := fun r => (j : ℝ) ^ 2 * (deriv D.w r * r⁻¹))
    (fun n r hr => by
      obtain ⟨x, hxe, rfl⟩ := hr
      exact tailNaturalLift_contDiffAt ⟨C, hC⟩ hu (hx n hxe))
    (fun n r hr => by
      obtain ⟨x, hxe, rfl⟩ := hr
      exact tailNaturalFlux_contDiffAt ⟨C, hC⟩ hu (hx n hxe))
    (fun n r hr => hw.contDiffAt.inv
      (hC.1.2.2.2.2.1 r (tailPhysicalEdge_subset_core hT hphysical n hr)).ne')
    (fun n r hr => contDiffAt_const.mul (hw'.contDiffAt.mul
      (contDiffAt_id.inv (ne_of_gt (hC.1.1.trans
        (tailPhysicalEdge_subset_core hT hphysical n hr).1)))))
    hc.1 hc.2 hv hq
    (fun n r hr => by
      obtain ⟨x, hxe, rfl⟩ := hr
      exact (tailNaturalLift_firstOrder ⟨C, hC⟩ hT hphysical hu (hx n hxe)).1)
    (fun n r hr => by
      obtain ⟨x, hxe, rfl⟩ := hr
      exact (tailNaturalLift_firstOrder ⟨C, hC⟩ hT hphysical hu (hx n hxe)).2)
  exact fun k => (hjets k).1

theorem tailPhysicalRadius_endpoint {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hphysical : TailPhysicalRelation D T right j start) :
    tailPhysicalRadius right T.endpoint = tailPhysicalEndpoint D right := by
  have hp := tailPhysicalEndpoint_pos hD right
  rw [hphysical.2.1]
  cases right <;> simpa [tailPhysicalRadius, tailPhysicalEndpoint] using exp_log hp

/-- The decay estimate remains valid at every omitted node and therefore
forces every physical jet to tend to zero along the outward coordinate. -/
theorem tailNaturalLift_jet_log_limit {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hu : TailNaturalEquation T u) (k : ℕ)
    (hk : PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n)))
        (iteratedDeriv k (tailPhysicalLift D right j u))) :
    Tendsto (fun x => iteratedDeriv k (tailPhysicalLift D right j u)
      (tailPhysicalRadius right x)) (𝓝[<] T.endpoint) (𝓝 0) := by
  have hlabel : ∀ n r, r ∈ tailPhysicalEdge T right n → ∃ m : ℕ,
      r ∈ D.cells m ∧ D.cellIndex m ≤ start + n + 1 := by
    intro n r hr
    obtain ⟨m, hm, hlo, hhi⟩ := tailPhysicalEdge_label hphysical n hr
    exact ⟨m, hm, hhi⟩
  obtain ⟨K, hK, hbound⟩ := physicalCellBound_quadratic hD hlabel hk
  let B : ℝ → ℝ := fun x => K *
    min (tailPhysicalRadius right x - D.a) (D.b - tailPhysicalRadius right x) ^ 2
  have hB : Continuous B := continuous_const.mul
    ((((continuous_tailPhysicalRadius right).sub continuous_const).min
      (continuous_const.sub (continuous_tailPhysicalRadius right))).pow 2)
  have hnodes : ∀ n, ContinuousAt
      (fun x => |iteratedDeriv k (tailPhysicalLift D right j u)
        (tailPhysicalRadius right x)|) (T.node n) := by
    intro n
    exact ((physical_contDiffAt_iteratedDeriv
      (tailNaturalLift_contDiffAt_node hD hT hu n) k).continuousAt.comp
        (continuous_tailPhysicalRadius right).continuousAt).abs
  have hwhole := tail_bound_on_Ico_of_edge_bound (deepTail_node_strictMono hT)
    hT.2.2.2.2.2.2.2.2.2.1 hnodes (fun _ => hB.continuousAt)
    (fun n x hx => hbound n _ ⟨x, hx, rfl⟩)
  have hnear : ∀ᶠ x in 𝓝[<] T.endpoint, T.node 0 < x :=
    nhdsWithin_le_nhds (eventually_gt_nhds (deepTail_node_lt_endpoint hT 0))
  apply squeeze_zero_norm'
  · filter_upwards [hnear, self_mem_nhdsWithin] with x hx₁ hx₂
    simpa only [Real.norm_eq_abs] using hwhole x ⟨hx₁.le, hx₂⟩
  · have hBe : B T.endpoint = 0 := by
      dsimp only [B]
      rw [tailPhysicalRadius_endpoint hD hphysical]
      obtain ⟨C, hC⟩ := hD
      have hab : 0 ≤ D.b - D.a := (sub_pos.mpr hC.1.2.1).le
      cases right
      · simp [tailPhysicalEndpoint, min_eq_left hab]
      · simp [tailPhysicalEndpoint, min_eq_right hab]
    have ht : Tendsto B (𝓝[<] T.endpoint) (𝓝 (B T.endpoint)) :=
      (hB.continuousAt (x := T.endpoint)).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [hBe] using ht

/-- The preceding limit is a limit in the original physical radius,
with the orientation selecting the correct one-sided neighborhood. -/
theorem tailNaturalLift_jet_limit {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hu : TailNaturalEquation T u) (k : ℕ)
    (hk : PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n)))
        (iteratedDeriv k (tailPhysicalLift D right j u))) :
    Tendsto (iteratedDeriv k (tailPhysicalLift D right j u))
      (if right then 𝓝[<] D.b else 𝓝[>] D.a) (𝓝 0) := by
  have hl := tailNaturalLift_jet_log_limit hD hT hphysical hu k hk
  have hR := tailPhysicalEndpoint_pos hD right
  have he := hphysical.2.1
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
    have ha : 0 < D.a := hR
    have hc : Tendsto (tailPhysicalLog false) (𝓝[>] D.a) (𝓝[<] T.endpoint) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · change Tendsto (-log) (𝓝[>] D.a) (𝓝 T.endpoint)
        rw [he]
        exact (continuousAt_log ha.ne').neg.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        change -log r < T.endpoint
        rw [he]
        exact neg_lt_neg (log_lt_log ha hr)
    apply (hl.comp hc).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [Function.comp_apply, tailPhysicalRadius_log false (ha.trans hr)]
  · simp only [↓reduceIte] at he ⊢
    have hb : 0 < D.b := hR
    have hpos : ∀ᶠ r in 𝓝[<] D.b, 0 < r :=
      nhdsWithin_le_nhds (eventually_gt_nhds hb)
    have hc : Tendsto (tailPhysicalLog true) (𝓝[<] D.b) (𝓝[<] T.endpoint) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · change Tendsto log (𝓝[<] D.b) (𝓝 T.endpoint)
        rw [he]
        exact (continuousAt_log hb.ne').tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [hpos, self_mem_nhdsWithin] with r hr hrb
        change log r < T.endpoint
        rw [he]
        exact log_lt_log hr hrb
    apply (hl.comp hc).congr'
    filter_upwards [hpos] with r hr
    simp only [Function.comp_apply, tailPhysicalRadius_log true hr]

/-- The open natural tail is exactly the corresponding physical radial
interval, including the orientation of the left endpoint. -/
theorem tailPhysicalInterior_eq {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hphysical : TailPhysicalRelation D T right j start) :
    tailPhysicalRadius right '' Ioo T.entrance T.endpoint =
      if right then Ioo (tailPhysicalRadius right T.entrance) D.b
      else Ioo D.a (tailPhysicalRadius right T.entrance) := by
  have he := tailPhysicalRadius_endpoint hD hphysical
  cases right
  · change (exp ∘ Neg.neg) '' Ioo T.entrance T.endpoint =
      Ioo D.a (exp (-T.entrance))
    rw [Set.image_comp, Set.image_neg_Ioo, image_exp_Ioo]
    change exp (-T.endpoint) = D.a at he
    rw [he]
  · change exp '' Ioo T.entrance T.endpoint = Ioo (exp T.entrance) D.b
    rw [image_exp_Ioo]
    change exp T.endpoint = D.b at he
    rw [he]

/-- The decay of all physical jets and the regular entrance produce an
actual global smooth extension, flat at the physical accumulation radius. -/
theorem tailNaturalLift_global_flat_of_jet_bounds {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hu : TailNaturalEquation T u)
    (hjets : ∀ k, PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n)))
        (iteratedDeriv k (tailPhysicalLift D right j u))) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      EqOn v (tailPhysicalLift D right j u)
        (tailPhysicalRadius right '' Ioo T.entrance T.endpoint) ∧
      ∀ k, iteratedDeriv k v (tailPhysicalEndpoint D right) = 0 := by
  have himage := tailPhysicalInterior_eq hD hphysical
  have hentry := tailPhysical_entrance_mem_core hD hT hphysical
  have hf₀ := tailNaturalLift_contDiffAt_entrance (right := right) (j := j) hD hu
  have hg₀ := tailNaturalFlux_contDiffAt_entrance (right := right) (j := j) hD hu
  have hreg : ∀ r ∈ tailPhysicalRadius right '' Ioo T.entrance T.endpoint,
      ContDiffAt ℝ ∞ (tailPhysicalLift D right j u) r ∧
        ContDiffAt ℝ ∞ (tailPhysicalFlux D right j u) r := by
    rintro r ⟨x, hx, rfl⟩
    exact ⟨tailNaturalLift_contDiffAt hD hu hx, tailNaturalFlux_contDiffAt hD hu hx⟩
  have hsys : ∀ r ∈ tailPhysicalRadius right '' Ioo T.entrance T.endpoint,
      deriv (tailPhysicalLift D right j u) r = (D.w r)⁻¹ * tailPhysicalFlux D right j u r ∧
        deriv (tailPhysicalFlux D right j u) r =
          ((j : ℝ) ^ 2 * (deriv D.w r * r⁻¹)) * tailPhysicalLift D right j u r := by
    rintro r ⟨x, hx, rfl⟩
    exact tailNaturalLift_firstOrder hD hT hphysical hu hx
  have hlimits (k : ℕ) := tailNaturalLift_jet_limit hD hT hphysical hu k (hjets k)
  obtain ⟨C, hC⟩ := hD
  have hw : ContDiff ℝ ∞ D.w := hC.1.2.2.1.1
  have hw' : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have ha : ContDiffOn ℝ ∞ (fun r => (D.w r)⁻¹) (radialCore D) := by
    intro r hr
    exact (hw.contDiffAt.inv (hC.1.2.2.2.2.1 r hr).ne').contDiffWithinAt
  have hb : ContDiffOn ℝ ∞ (fun r => (j : ℝ) ^ 2 * (deriv D.w r * r⁻¹)) (radialCore D) := by
    intro r hr
    exact (contDiffAt_const.mul (hw'.contDiffAt.mul
      (contDiffAt_id.inv (ne_of_gt (hC.1.1.trans hr.1))))).contDiffWithinAt
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte] at himage hlimits
    obtain ⟨v, hv, hveq, hvflat⟩ := physical_flat_extension_from_right isOpen_Ioo hentry hentry.1
      ha hb hf₀ hg₀
      (fun r hr => (hreg r (himage.symm ▸ hr)).1.contDiffWithinAt)
      (fun r hr => (hreg r (himage.symm ▸ hr)).2.contDiffWithinAt)
      (fun r hr => (hsys r (himage.symm ▸ hr)).1)
      (fun r hr => (hsys r (himage.symm ▸ hr)).2) hlimits
    exact ⟨v, hv, himage.symm ▸ hveq, hvflat⟩
  · simp only [↓reduceIte] at himage hlimits
    obtain ⟨v, hv, hveq, hvflat⟩ := physical_flat_extension_from_left isOpen_Ioo hentry hentry.2
      ha hb hf₀ hg₀
      (fun r hr => (hreg r (himage.symm ▸ hr)).1.contDiffWithinAt)
      (fun r hr => (hreg r (himage.symm ▸ hr)).2.contDiffWithinAt)
      (fun r hr => (hsys r (himage.symm ▸ hr)).1)
      (fun r hr => (hsys r (himage.symm ▸ hr)).2) hlimits
    exact ⟨v, hv, himage.symm ▸ hveq, hvflat⟩

/-- Once the actual whole-edge height and flux bounds are available,
all clauses of the frozen physical-flatness conclusion follow for this
same natural solution and its genuine smooth radial extension. -/
theorem tailPhysicalFlatConclusion_of_cell_bounds {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hu : TailNaturalEquation T u) (hune : ∃ x ∈ Ioo T.entrance T.endpoint, u x ≠ 0)
    (hv : PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n))) (tailPhysicalLift D right j u))
    (hq : PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n))) (tailPhysicalFlux D right j u)) :
    TailPhysicalFlatConclusion D T right j start := by
  have hjets := tailNaturalLift_jet_bounds hD hT hphysical hu hv hq
  obtain ⟨v, hvsm, hveq, hvflat⟩ :=
    tailNaturalLift_global_flat_of_jet_bounds hD hT hphysical hu hjets
  have hopen : IsOpen (tailPhysicalRadius right '' Ioo T.entrance T.endpoint) := by
    rw [tailPhysicalInterior_eq hD hphysical]
    cases right <;> exact isOpen_Ioo
  have hgerm (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :
      v =ᶠ[𝓝 (tailPhysicalRadius right x)] tailPhysicalLift D right j u :=
    Filter.mem_of_superset (hopen.mem_nhds ⟨x, hx, rfl⟩) (fun r hr => hveq hr)
  refine ⟨u, v, hu, hune, hvsm, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hveq ⟨x, hx, rfl⟩).trans (tailPhysicalLift_radius D right j u x)
  · intro x hx
    have hflux : (fun r => D.w r * deriv v r) =ᶠ[𝓝 (tailPhysicalRadius right x)]
        (fun r => D.w r * deriv (tailPhysicalLift D right j u) r) := by
      filter_upwards [(hgerm x hx).deriv] with r hr
      rw [hr]
    unfold radialJacobi
    rw [hflux.deriv_eq, (hgerm x hx).eq_of_nhds]
    exact tailNaturalLift_radialJacobi hD hT hphysical hu hx
  · intro k
    rw [radialJet_eq_iteratedDeriv]
    change iteratedDeriv k v (tailPhysicalEndpoint D right) = 0
    exact hvflat k
  · intro k
    obtain ⟨C, hC, hb⟩ := hjets k
    refine ⟨C, hC, fun n x hx => ?_⟩
    have hxt : x ∈ Ioo T.entrance T.endpoint :=
      ⟨(deepTail_entrance_le_node hT n).trans_lt hx.1,
        hx.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩
    rw [radialJet_eq_iteratedDeriv, (hgerm x hxt).iteratedDeriv_eq k]
    exact hb n _ ⟨x, hx, rfl⟩

end ContinuousFlexibility.Radial
