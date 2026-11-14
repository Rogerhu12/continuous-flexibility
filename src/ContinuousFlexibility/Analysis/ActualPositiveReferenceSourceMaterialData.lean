import ContinuousFlexibility.Analysis.ActualReferenceRootFiniteMaterialData
import ContinuousFlexibility.Analysis.ActualPositiveReferenceEndpointData
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Material data of the actual interior positive reference source

The certified source uses the opposite negative root. Its fixed affine
translation does not affect positive radial jets, and its orientation
has absolute value one. The original height is unchanged. Thus the
proved raw root envelope controls the exact scalar data consumed by the
prescribed positive reference interpolation, without changing the host.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04Coordinates_actual_positive_reference_source_material_data
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (hK : 0 < K₀) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ N : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ (i : N04PositiveComponent D.a D.b (deriv D.w)) (side : Bool),
      ∀ src : N04PositiveEndpointSource C i side, src.val = some m →
        let K := n04bActualTypedAtlas hT hS hN hfield e
        let c := n04PositiveEndpoint i side
        let y := n04PositiveReferenceSourceCoordinate src K
        let h := n04PositiveReferenceSourceHeight src K
        let M := B * (C0 * T.E0 (T.sample j)) ^ B
        1 ≤ M ∧ M⁻¹ ≤ radialBoundaryJet y c 1 0 ∧
          M⁻¹ ≤ radialBoundaryJet h c 0 0 ∧
          (∀ n : ℕ, 1 ≤ n → n ≤ N → |radialBoundaryJet y c n 0| ≤ M) ∧
          ∀ n : ℕ, n ≤ N → |radialBoundaryJet h c n 0| ≤ M := by
  obtain ⟨C0, hC0, hfloor, hfinite⟩ :=
    n04Coordinates_actual_reference_root_finite_material_data hT hS hN hfield e hK
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro N
  obtain ⟨B, hB, hbound⟩ := hfinite N
  refine ⟨B, hB, ?_⟩
  intro m j hhost hoptical i side src hsrc
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let k := if side then (K.cutPair m).1 else (K.cutPair m).2
  let c := n04PositiveEndpoint i side
  let s : ℝ := if side then 1 else -1
  let v : ℝ := if side then 1 else 0
  rcases src with ⟨o, ho⟩
  change o = some m at hsrc
  subst o
  have hc : c = (if !side then C.right m else C.left m) := by
    change n04PositiveEndpoint i side = _
    change n04PositiveEndpoint i side = (if side then C.left m else C.right m) at ho
    rw [ho]
    cases side <;> rfl
  have hk : e.symm (.inl (m, !side)) = k := by cases side <;> rfl
  have hs : (if !side then (-1 : ℝ) else 1) = s := by cases side <;> rfl
  have hsabs : |s| = 1 := by cases side <;> norm_num [s]
  have hraw := hbound m j hhost hoptical (!side)
  simp only [hk, ← hc, hs] at hraw
  have hy (n : ℕ) (hn : 1 ≤ n) :
      radialBoundaryJet (n04PositiveReferenceSourceCoordinate
        (i := i) (side := side) ⟨some m, ho⟩ K) c n 0 =
        s * radialBoundaryJet (fun p => (K.chart z₀ k p).1) c n 0 := by
    change iteratedDeriv n (fun r : ℝ => v + s * (K.chart z₀ k (r, 0)).1) c = _
    rw [iteratedDeriv_const_add (by omega : 0 < n), iteratedDeriv_const_mul_field]
    rfl
  refine ⟨hraw.1, ?_, ?_, ?_, ?_⟩
  · change _ ≤ radialBoundaryJet (n04PositiveReferenceSourceCoordinate
      (i := i) (side := side) ⟨some m, ho⟩ K) c 1 0
    rw [hy 1 le_rfl]
    simpa only [radialBoundaryJet, iteratedDeriv_one] using hraw.2.1
  · simpa only [n04PositiveReferenceSourceHeight, radialBoundaryJet, iteratedDeriv_zero]
      using hraw.2.2.1
  · intro n hn hNn
    change |radialBoundaryJet (n04PositiveReferenceSourceCoordinate
      (i := i) (side := side) ⟨some m, ho⟩ K) c n 0| ≤ _
    rw [hy n hn, abs_mul, hsabs, one_mul]
    exact hraw.2.2.2.1 n hn hNn
  · intro n hn
    exact hraw.2.2.2.2 n hn

end ContinuousFlexibility.Analysis
