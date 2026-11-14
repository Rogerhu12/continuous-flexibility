import ContinuousFlexibility.Analysis.ActualNegativeMaterialSamples

/-!
# A genuine negative host and the stored half sample

An arbitrary cell containing the whole open negative component need
not be the cell stored by either optical half. Their samples nevertheless
have uniformly bounded endpoint-coordinate distance: the actual middle
point belongs to the host, while the existing half-sample comparison
holds at that same point. No uniqueness of cells is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)

/-- The host is quantified after the common constant. It is not
identified with the actual typed atlas's stored cell. -/
theorem n04bActualTypedAtlas_negative_host_sample_endpointX :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      |endpointX 1 (Statements.endpointDistance D (T.sample j)) -
        endpointX 1 (Statements.endpointDistance D (T.sample (K.cell k)))| ≤ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  obtain ⟨A, hA, hdist⟩ :=
    n04bActualTypedAtlas_negative_sample_endpointX hT hS hN hfield e
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, hcompare⟩ := hdata
  obtain ⟨B, P, hB, _, hindex⟩ := hcompare
  refine ⟨2 * B + A, add_nonneg (mul_nonneg (by norm_num) hB.le) hA, ?_⟩
  intro k m side hk j hhost
  let r := (C.left m + C.right m) / 2
  have hb := hN.1.1.2.2.2.1.1 m
  have hr : r ∈ Ioo (C.left m) (C.right m) := by
    dsimp only [r]
    constructor <;> linarith only [hb.2.1]
  have hs := abs_le.mp (hindex j (T.sample j) (hsample j)).1
  have hp := abs_le.mp (hindex j r (hhost hr)).1
  have ht := abs_le.mp (hdist k m side hk r ⟨hr.1.le, hr.2.le⟩)
  apply abs_le.mpr
  constructor <;> linarith only [hs.1, hs.2, hp.1, hp.2, ht.1, ht.2]

/-- Any fixed material power at the original full-component host
transfers to the exact sample retained by the selected optical half. -/
theorem n04bActualTypedAtlas_negative_host_sample_weights
    (γ η P : ℝ) (hP : 0 ≤ P) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      T.H (T.sample j) ^ γ * T.M (T.sample j) ^ η * T.E0 (T.sample j) ^ P ≤
        B * (T.H (T.sample (K.cell k)) ^ γ *
          T.M (T.sample (K.cell k)) ^ η * T.E0 (T.sample (K.cell k)) ^ A) := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  obtain ⟨A₀, hA₀, hdist⟩ :=
    n04bActualTypedAtlas_negative_host_sample_endpointX hT hS hN hfield e
  obtain ⟨B, A, hB, hA, hbound⟩ :=
    material_global_H_M_E0_rpow_bounded_X_shift hT hN.1.1.1.1 γ η hP hA₀
  refine ⟨B, A, hB, hA, ?_⟩
  intro k m side hk j hhost
  exact hbound (T.sample j) (T.sample (K.cell k))
    (materialSample_mem_interval hN.1.1.1.1 hT j)
    (materialSample_mem_interval hN.1.1.1.1 hT (K.cell k))
    (hdist k m side hk j hhost)

/-- In particular, a host coefficient loss is paid at the same stored
half sample, without a lower bound of one for the original envelope. -/
theorem n04bActualTypedAtlas_negative_host_sample_E0_power
    (P : ℝ) (hP : 0 ≤ P) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      T.E0 (T.sample j) ^ P ≤ B * T.E0 (T.sample (K.cell k)) ^ A := by
  simpa only [Real.rpow_zero, one_mul] using
    n04bActualTypedAtlas_negative_host_sample_weights hT hS hN hfield e 0 0 P hP

end ContinuousFlexibility.Analysis
