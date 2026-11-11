import ContinuousFlexibility.Radial.InnerRadialAffineLift
import ContinuousFlexibility.Radial.InnerPieceProjection

/-!
# Support of the actual physical first-order domain

Physical piece projection is continuous. Its fixed-point equations pass
from the actual compact smooth core to the closed zero-endpoint domain.
The fixed affine lifts have the same support, so every full-domain field
is supported in its genuine interval. This supplies the physical
source/Poisson pairing used in the global adjoint identity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

theorem innerRadialH1Zero_piece_projection (D : ReferenceData) (a b : ℝ)
    {q : InnerRadialH1Pair D} (hq : q ∈ innerRadialH1Zero D a b) :
    innerL2PieceProjection (radialHilbertMeasure D) (Ioo a b) q.1 = q.1 ∧
      innerL2PieceProjection (radialHilbertMeasure D) (Ioo a b) q.2 = q.2 := by
  let P := innerL2PieceProjection (radialHilbertMeasure D) (Ioo a b)
  have hclosed : IsClosed {q : InnerRadialH1Pair D | P q.1 = q.1 ∧ P q.2 = q.2} :=
    (isClosed_eq (P.continuous.comp continuous_fst) continuous_fst).inter
      (isClosed_eq (P.continuous.comp continuous_snd) continuous_snd)
  apply (closure_minimal ?_ hclosed) ((mem_innerRadialH1Zero D a b q).mp hq)
  rintro r ⟨φ, _, _, _, hu, hd⟩
  have hfix {u : RadialModeL2 D} {f : ℝ → ℝ}
      (hf : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator f) :
      P u = u := by
    apply innerL2PieceProjection_eq_self _ _ measurableSet_Ioo
    filter_upwards [hf] with x hx
    intro hout
    rw [hx, indicator_of_notMem hout]
  exact ⟨hfix hu, hfix hd⟩

section FullDomain

variable (D : ReferenceData) (hw : Continuous D.w) {a b : ℝ}
  (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
  (hpos : ∀ r ∈ Icc a b, 0 < D.w r)

theorem innerRadialAffineUnitPair_piece_projection (i : Fin 2) :
    innerL2PieceProjection (radialHilbertMeasure D) (Ioo a b)
      (innerRadialAffineUnitPair D hw ha hcore hpos i).1 =
      (innerRadialAffineUnitPair D hw ha hcore hpos i).1 := by
  apply innerL2PieceProjection_eq_self _ _ measurableSet_Ioo
  filter_upwards [innerRadialAffineUnitPair_value_ae D hw ha hcore hpos i] with x hx
  intro hout
  rw [hx, indicator_of_notMem hout]

theorem innerRadialAffineLift_piece_projection (z : Fin 2 → ℝ) :
    innerL2PieceProjection (radialHilbertMeasure D) (Ioo a b)
      (innerRadialAffineLift D hw ha hcore hpos z).1 =
      (innerRadialAffineLift D hw ha hcore hpos z).1 := by
  simp only [innerRadialAffineLift_apply, Prod.fst_add, Prod.smul_fst,
    map_add, map_smul, innerRadialAffineUnitPair_piece_projection]

/-- The true full physical piece domain is supported in that piece. -/
theorem innerRadialH1Domain_piece_projection {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Domain D hw ha hcore hpos) :
    innerL2PieceProjection (radialHilbertMeasure D) (Ioo a b) q.1 = q.1 := by
  have hz := (mem_innerRadialH1Domain D hw ha hcore hpos q).mp hq
  have hp := (innerRadialH1Zero_piece_projection D a b hz).1
  rw [Prod.fst_sub, map_sub, innerRadialAffineLift_piece_projection] at hp
  have he := congrArg
    (fun z : RadialModeL2 D => z +
      (innerRadialAffineLift D hw ha hcore hpos
        (innerRadialH1Trace D hw ha hcore hpos q)).1) hp
  simpa only [sub_add_cancel] using he

theorem innerRadialH1Domain_supported {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Domain D hw ha hcore hpos) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b → q.1 r = 0 := by
  have hs := innerL2PieceProjection_supported (radialHilbertMeasure D) (Ioo a b)
    measurableSet_Ioo q.1
  rwa [innerRadialH1Domain_piece_projection D hw ha hcore hpos hq] at hs

end FullDomain

/-- Actual restriction may be moved off a field supported in the piece. -/
theorem innerL2PieceProjection_inner_fixed {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (F u : Lp ℝ 2 μ)
    (hu : innerL2PieceProjection μ s u = u) :
    ⟪innerL2PieceProjection μ s F, u⟫_ℝ = ⟪F, u⟫_ℝ := by
  have he := ContinuousLinearMap.adjoint_inner_right (innerL2PieceProjection μ s) F u
  have hs := ContinuousLinearMap.isSelfAdjoint_iff'.mp (innerL2PieceProjection_selfAdjoint μ s)
  rw [hs, hu] at he
  exact he.symm

end ContinuousFlexibility.Radial
