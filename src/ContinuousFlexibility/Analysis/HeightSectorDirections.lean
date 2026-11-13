import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Genuine height and scalar directions in the sector space

The height direction is inserted into the existing physical sector.
Its sector seminorm is exactly the height-pair seminorm.  The formulas
below describe the actual lifted state, including the reference height.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance heightSectorDirectionsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

def heightSectorDirection (S : PhysicalSpacesData) (η : HeightPair S) :
    StateDirections S :=
  ⟨(η, 0), by
    change stateSector S ((η, 0) : AnnularState S)
    have hzero : (S.circle (3 / 4 : ℝ)).decode (0 : CircleSpace S) = 0 :=
      (S.circle (3 / 4 : ℝ)).decode.map_zero
    constructor
    · intro m θ φ
      change (S.circle (3 / 4 : ℝ)).decode (0 : CircleSpace S) m θ =
        (S.circle (3 / 4 : ℝ)).decode (0 : CircleSpace S) m φ
      simp only [hzero, Pi.zero_apply]
    · intro m θ
      change (S.circle (3 / 4 : ℝ)).decode (0 : CircleSpace S) m (-θ) =
        -(S.circle (3 / 4 : ℝ)).decode (0 : CircleSpace S) m θ
      simp only [hzero, Pi.zero_apply, neg_zero]⟩

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
  have hr0 : realGrading n (0 : ℝ) = 0 := (realGrading n).map_zero'
  have hc0 : (S.circle (3 / 4 : ℝ)).grading n (0 : CircleSpace S) = 0 :=
    ((S.circle (3 / 4 : ℝ)).grading n).map_zero'
  simp only [hr0, hc0, add_zero]

theorem scalarParameterDirection_grading (S : PhysicalSpacesData) (n : ℕ) :
    pairGrading (sectorGrading S) realGrading n (scalarParameterDirection S) = 1 := by
  change sectorGrading S n 0 + ‖(1 : ℝ)‖ = 1
  have hs0 : sectorGrading S n (0 : StateDirections S) = 0 :=
    (sectorGrading S n).map_zero'
  simp only [hs0, norm_one, zero_add]

theorem scalarParameter_line (S : PhysicalSpacesData)
    (z : StateDirections S × ℝ) (t : ℝ) :
    z + t • scalarParameterDirection S = (z.1, z.2 + t) := by
  apply Prod.ext
  · change z.1 + t • (0 : StateDirections S) = z.1
    exact (congrArg (fun w : StateDirections S => z.1 + w)
      (smul_zero t : t • (0 : StateDirections S) = 0)).trans (add_zero z.1)
  · change z.2 + t * 1 = z.2 + t
    exact congrArg (fun a : ℝ => z.2 + a) (mul_one t)

theorem scalarParameter_zero_line (S : PhysicalSpacesData)
    (x : StateDirections S) (t : ℝ) :
    (x, (0 : ℝ)) + t • scalarParameterDirection S = (x, t) := by
  exact (scalarParameter_line S (x, 0) t).trans (Prod.ext rfl (zero_add t))

theorem liftSectorParameter_height_line (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ)
    (η : HeightPair S) (t : ℝ) :
    liftSectorParameter S C (z + t • heightParameterDirection S η) =
      ((liftSectorParameter S C z).1 + t • ((η, 0) : AnnularState S), z.2) := by
  apply Prod.ext
  · change C.referenceState + (z.1.val + t • ((η, 0) : AnnularState S)) =
      (C.referenceState + z.1.val) + t • ((η, 0) : AnnularState S)
    exact (add_assoc C.referenceState z.1.val (t • ((η, 0) : AnnularState S))).symm
  · change z.2 + t * 0 = z.2
    exact (congrArg (fun a : ℝ => z.2 + a) (mul_zero t)).trans (add_zero z.2)

theorem liftSectorParameter_scalar_line (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ) (t : ℝ) :
    liftSectorParameter S C (z + t • scalarParameterDirection S) =
      ((liftSectorParameter S C z).1, z.2 + t) := by
  exact congrArg (liftSectorParameter S C) (scalarParameter_line S z t)

theorem liftSectorParameter_height_line_tail (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ)
    (η : HeightPair S) (t : ℝ) :
    (liftSectorParameter S C (z + t • heightParameterDirection S η)).1.2 =
      (liftSectorParameter S C z).1.2 := by
  have heq := congrArg (fun p : AnnularState S × ℝ => p.1.2)
    (liftSectorParameter_height_line S C z η t)
  have hz : t • (0 : ℝ × (CircleSpace S × CircleSpace S)) = 0 := smul_zero t
  exact heq.trans ((congrArg
    (fun w : ℝ × (CircleSpace S × CircleSpace S) => (liftSectorParameter S C z).1.2 + w)
    hz).trans (add_zero _))

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
  have habs : |t| ≤ |z.2| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht
  exact ⟨hz.1, habs.trans_lt hz.2⟩

end ContinuousFlexibility.Statements
