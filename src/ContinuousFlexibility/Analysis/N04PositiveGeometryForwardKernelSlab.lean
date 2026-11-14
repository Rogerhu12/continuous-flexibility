module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsSlab

/-!
# Forward radial kernel jets on the same physical slab

The coefficient box and the selected collar widths are exactly those
used by the inverse kernel. The evaluation radius stays between the two
physical endpoints, so all ordinary finite-kernel jets have the same
kind of sampled material envelope.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem n04PositiveGeometry_radialKernel_forward_bounds
    {I : Type} {W : I → ℝ} (hW : ∀ i, 1 ≤ W i) (n : ℕ)
    (l r c d κ M : I → ℝ)
    (hlc : ∀ i, l i < c i) (hcd : ∀ i, c i < d i) (hdr : ∀ i, d i < r i)
    (hκ : ∀ i, 0 < κ i) (hM : ∀ i, 0 ≤ M i)
    (hl : HasPositiveEnvelope W (fun i => |l i|))
    (hr : HasPositiveEnvelope W (fun i => |r i|))
    (hc : HasPositiveEnvelope W (fun i => |c i|))
    (hd : HasPositiveEnvelope W (fun i => |d i|))
    (hMcost : HasPositiveEnvelope W M)
    (hwidth : ∀ side, HasPositiveEnvelope W (fun i =>
      |(endpointFiberWidths n (l i) (r i) (c i) (d i) (κ i) (M i) side)⁻¹|))
    (hspan : ∀ side : Bool, HasPositiveEnvelope W
      (fun i => |((if side then r i else c i) - (if side then d i else l i))⁻¹|)) :
    ∀ k : ℕ, ∃ C Q : ℝ, 0 < C ∧ 0 ≤ Q ∧
      ∀ i (a : N04PositiveRadialCoefficients n),
        a ∈ n04PositiveGeometry_radialCoefficientDomain n (κ i) (M i) →
      ∀ x ∈ Icc (l i) (r i),
        ‖iteratedFDeriv ℝ k
          (n04PositiveGeometry_radialKernel n (l i) (r i) (c i) (d i)
            (endpointFiberWidths n (l i) (r i) (c i) (d i) (κ i) (M i)))
          (a, x)‖ ≤ C * W i ^ Q := by
  let P := N04PositiveRadialCoefficients n
  let Ω : I → Set (P × ℝ) := fun i =>
    n04PositiveGeometry_radialCoefficientDomain n (κ i) (M i) ×ˢ Icc (l i) (r i)
  let J := {z : I × (P × ℝ) // z.2 ∈ Ω z.1}
  let e : J → I := fun z => z.1.1
  let p : J → P × ℝ := fun z => z.1.2
  have hgeom (i : I) := n04PositiveGeometry_radialKernel_geometry n
    (hlc i) (hcd i) (hdr i) (hκ i) (hM i)
  have hp : HasPositiveEnvelope (fun z : J => W (e z)) (fun z => ‖p z‖) := by
    apply n04PositiveGeometry_envelope_reindex ((hMcost.add hW hl).add hW hr) e |>.mono
    intro z
    have ha : ‖z.1.2.1‖ ≤ M (e z) := by
      apply (pi_norm_le_iff_of_nonneg (hM (e z))).mpr
      intro side
      apply (pi_norm_le_iff_of_nonneg (hM (e z))).mpr
      intro j
      simpa only [Real.norm_eq_abs] using ((z.2.1 side).2 j).le
    have hx : |z.1.2.2| ≤ |l (e z)| + |r (e z)| := by
      apply abs_le.mpr
      have hz := z.2.2
      constructor <;> linarith only [hz.1, hz.2, neg_abs_le (l (e z)),
        le_abs_self (r (e z)), abs_nonneg (l (e z)), abs_nonneg (r (e z))]
    rw [Prod.norm_def, Real.norm_eq_abs]
    apply max_le
    · exact ha.trans (by linarith only [abs_nonneg (l (e z)), abs_nonneg (r (e z))])
    · exact hx.trans (by linarith only [hM (e z)])
  have hmiddle (side : Bool) := n04PositiveGeometry_radialKernel_middleMass_envelope
    hW n l r c d κ M hlc hcd hdr hκ hM hspan side
  have hb := n04PositiveGeometry_radialKernel_bounds (fun z : J => hW (e z)) n p
    (fun z => l (e z)) (fun z => r (e z)) (fun z => c (e z)) (fun z => d (e z))
    (fun z => endpointFiberWidths n (l (e z)) (r (e z)) (c (e z)) (d (e z))
      (κ (e z)) (M (e z))) (fun z => hcd (e z))
    (fun z => (hgeom (e z)).1) (fun z => (hgeom (e z)).2.1) hp
    (n04PositiveGeometry_envelope_reindex hl e) (n04PositiveGeometry_envelope_reindex hr e)
    (n04PositiveGeometry_envelope_reindex hc e) (n04PositiveGeometry_envelope_reindex hd e)
    (fun side => n04PositiveGeometry_envelope_reindex (hwidth side) e)
    (fun side => n04PositiveGeometry_envelope_reindex (hspan side) e)
    (fun side => n04PositiveGeometry_envelope_reindex (hmiddle side) e)
  intro k
  obtain ⟨C, Q, hC, hQ, hb⟩ := hb.jets k
  exact ⟨C, Q, hC, hQ.le, fun i a ha x hx => hb ⟨(i, (a, x)), ha, hx⟩⟩

end ContinuousFlexibility.Analysis
