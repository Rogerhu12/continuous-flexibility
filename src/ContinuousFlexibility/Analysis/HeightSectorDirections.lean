import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Genuine height and scalar directions in the sector space

The height direction is inserted into the existing physical sector.
Its sector seminorm is exactly the height-pair seminorm.  The formulas
below describe the actual lifted state, including the reference height.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

def heightSectorDirection (S : PhysicalSpacesData) (η : HeightPair S) :
    StateDirections S :=
  ⟨(η, 0), by
    change stateSector S ((η, 0) : AnnularState S)
    simp only [stateSector, map_zero, Pi.zero_apply, neg_zero]
    exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩⟩

def heightParameterDirection (S : PhysicalSpacesData) (η : HeightPair S) :
    StateDirections S × ℝ := (heightSectorDirection S η, 0)

def scalarParameterDirection (S : PhysicalSpacesData) :
    StateDirections S × ℝ := (0, 1)

theorem heightSectorDirection_coe (S : PhysicalSpacesData) (η : HeightPair S) :
    (heightSectorDirection S η).val = ((η, 0) : AnnularState S) := rfl

theorem heightParameterDirection_grading (S : PhysicalSpacesData)
    (η : HeightPair S) (n : ℕ) :
    pairGrading (sectorGrading S) realGrading n (heightParameterDirection S η) =
      heightPairGrading S n η := by
  change heightPairGrading S n η +
    (realGrading n 0 + ((S.circle (3 / 4 : ℝ)).grading n 0 +
      (S.circle (3 / 4 : ℝ)).grading n 0)) + realGrading n 0 = _
  simp only [map_zero, add_zero]

theorem scalarParameterDirection_grading (S : PhysicalSpacesData) (n : ℕ) :
    pairGrading (sectorGrading S) realGrading n (scalarParameterDirection S) = 1 := by
  change sectorGrading S n 0 + ‖(1 : ℝ)‖ = 1
  simp only [map_zero, norm_one, zero_add]

theorem liftSectorParameter_height_line (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ)
    (η : HeightPair S) (t : ℝ) :
    liftSectorParameter S C (z + t • heightParameterDirection S η) =
      ((liftSectorParameter S C z).1 + t • ((η, 0) : AnnularState S), z.2) := by
  change (C.referenceState + (z.1.val + t • ((η, 0) : AnnularState S)),
    z.2 + t * 0) = ((C.referenceState + z.1.val) + t • ((η, 0) : AnnularState S), z.2)
  rw [add_assoc, mul_zero, add_zero]

theorem liftSectorParameter_scalar_line (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ) (t : ℝ) :
    liftSectorParameter S C (z + t • scalarParameterDirection S) =
      ((liftSectorParameter S C z).1, z.2 + t) := by
  change (C.referenceState + (z.1.val + t • (0 : AnnularState S)), z.2 + t * 1) = _
  rw [smul_zero, add_zero, mul_one]
  rfl

theorem liftSectorParameter_height_line_tail (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ)
    (η : HeightPair S) (t : ℝ) :
    (liftSectorParameter S C (z + t • heightParameterDirection S η)).1.2 =
      (liftSectorParameter S C z).1.2 := by
  rw [liftSectorParameter_height_line]
  change (liftSectorParameter S C z).1.2 +
    t • (0 : ℝ × (CircleSpace S × CircleSpace S)) = _
  rw [smul_zero, add_zero]

theorem liftSectorParameter_height_line_field (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ)
    (η : HeightPair S) (t : ℝ) (p : PolarPoint) :
    stateU S (liftSectorParameter S C (z + t • heightParameterDirection S η)).1 p =
      stateU S (liftSectorParameter S C z).1 p + t * heightPairField S η p := by
  rw [liftSectorParameter_height_line]
  change (S.height (3 / 4 : ℝ)).decode
      ((liftSectorParameter S C z).1.1.1 + t • η.1) p +
      ((liftSectorParameter S C z).1.1.2 + t * η.2) * S.chiLeft p.1 =
    ((S.height (3 / 4 : ℝ)).decode (liftSectorParameter S C z).1.1.1 p +
      (liftSectorParameter S C z).1.1.2 * S.chiLeft p.1) +
      t * ((S.height (3 / 4 : ℝ)).decode η.1 p + η.2 * S.chiLeft p.1)
  rw [map_add, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem sectorParameter_line_eventually_mem
    {S : PhysicalSpacesData} {base : ℕ} {ε q₀ : ℝ}
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε q₀)
    (v : StateDirections S × ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), z + t • v ∈ sectorNeighborhood S base ε q₀ := by
  have hc : Continuous (fun t : ℝ => z + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  exact hc.continuousAt.eventually ((sectorNeighborhood_isOpen S base ε q₀).mem_nhds
    (by simpa only [zero_smul, add_zero] using hz))

theorem sectorParameter_scalar_segment_mem
    {S : PhysicalSpacesData} {base : ℕ} {ε : ℝ}
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) z.2) :
    (z.1, t) ∈ sectorNeighborhood S base ε ε := by
  refine ⟨hz.1, lt_of_le_of_lt ?_ hz.2⟩
  rcases le_total (0 : ℝ) z.2 with hq | hq
  · rw [uIcc_of_le hq] at ht
    rw [abs_of_nonneg ht.1, abs_of_nonneg hq]
    exact ht.2
  · rw [uIcc_of_ge hq] at ht
    rw [abs_of_nonpos ht.2, abs_of_nonpos hq]
    exact neg_le_neg ht.1

end ContinuousFlexibility.Statements
