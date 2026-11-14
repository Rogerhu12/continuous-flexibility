module

public import ContinuousFlexibility.Analysis.MaterialCellEndpointModels
public import Mathlib.Topology.Order.OrderClosed

/-!
# The actual host-cell coordinate bound at a closed endpoint

A genuine open interval contained in a material cell inherits the same
uniform cell-index bound at both interior endpoints by continuity. The
sample and original cell are retained; neither endpoint is required to
belong to that open cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem material_cell_endpointX_closed_interval
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧
      (∀ j r, r ∈ D.cells j →
        |endpointX 1 (endpointDistance D r) - (D.cellIndex j : ℝ)| ≤ B) ∧
      ∀ l u j, D.a < l → l < u → u < D.b → Ioo l u ⊆ D.cells j →
        ∀ r ∈ Icc l u,
          |endpointX 1 (endpointDistance D r) - (D.cellIndex j : ℝ)| ≤ B := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcompare⟩ := hdata
  obtain ⟨B, A, hB, _, hindex⟩ := hcompare
  let X : ℝ → ℝ := fun r => endpointX 1 (endpointDistance D r)
  have hd : Continuous (endpointDistance D) :=
    (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)
  have hp (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < endpointDistance D r :=
    lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hX : ContinuousOn X (Ioo D.a D.b) :=
    ((continuousOn_const.div hd.continuousOn
      (fun r hr => (hp r hr).ne')).log
        (fun r hr => (div_pos zero_lt_one (hp r hr)).ne')).sqrt
  refine ⟨B, hB, fun j r hr => (hindex j r hr).1, ?_⟩
  intro l u j hal hlu hub hhost r hr
  have hsub : Icc l u ⊆ Ioo D.a D.b :=
    fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hub⟩
  have hcont : ContinuousOn
      (fun x => |X x - (D.cellIndex j : ℝ)|) (closure (Ioo l u)) := by
    rw [closure_Ioo hlu.ne]
    exact (hX.sub continuousOn_const).abs.mono hsub
  exact le_on_closure (fun x hx => (hindex j x (hhost hx)).1)
    hcont continuousOn_const (by simpa only [closure_Ioo hlu.ne] using hr)

end ContinuousFlexibility.Statements
