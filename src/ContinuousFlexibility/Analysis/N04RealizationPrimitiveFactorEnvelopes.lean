import ContinuousFlexibility.Analysis.N04RealizationPrimitiveMaterialJets
import ContinuousFlexibility.Analysis.N04RealizationPrimitiveFactors
import ContinuousFlexibility.Analysis.N04RealizationChartAtomEnvelopes
import ContinuousFlexibility.Analysis.N04RealizationMaterialSampleEnvelopes
import ContinuousFlexibility.Analysis.N06FiniteSourceGeometry

/-!
# Actual chart and source factors for primitive material jets

All evaluations are on the moving physical piece or its genuine current
canonical image. Current and reference fields use the same canonical
point. Only positive coordinate jets are used, and sampled and pointwise
coefficient costs are kept together until the final material conversion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base high : ℕ} {ε : ℝ}

theorem n04Realization_sourceFactor_pos
    (hgeom : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {q : PolarPoint}
    (hq : q ∈ canonicalOpen S K m) :
    0 < canonicalSource S K z m (fun _ => 1) q := by
  have hc := hgeom.charts z hz hs m
  have hp := hc.2.2.2.2.2.2.2 _ (hc.2.1 hq)
  simp only [canonicalSource, mul_one]
  exact div_pos hp.1 (abs_pos.mpr hp.2.1)

theorem n04Realization_inverseChart_jacobian_ne
    (hgeom : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {q : PolarPoint}
    (hq : q ∈ canonicalOpen S K m) :
    planeJacobian (K.inverseChart z m) q ≠ 0 := by
  apply abs_pos.mp
  rw [n07a_actual_inverseChart_jacobian_abs hgeom hz hs m hq]
  have hc := hgeom.charts z hz hs m
  exact inv_pos.mpr (abs_pos.mpr (hc.2.2.2.2.2.2.2 _ (hc.2.1 hq)).2.1)

/-- The source and its reciprocal are the existing two scalar atoms,
with smoothness proved from geometry on the actual canonical domain. -/
theorem n04Realization_sourceFactor_atom_input
    (hgeom : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (inv : Bool) :
    ContDiffOn ℝ ∞ (fun q => if inv then
      (canonicalSource S K z m (fun _ => 1) q)⁻¹
      else canonicalSource S K z m (fun _ => 1) q) (canonicalOpen S K m) ∧
    EqOn ((fun q => if inv then (canonicalSource S K z m (fun _ => 1) q)⁻¹
      else canonicalSource S K z m (fun _ => 1) q) ∘ canonicalUnitPoint K m)
      (atom D T S C L K z m (if inv then .sourceFactorInverse else .sourceFactor))
      unitStrip := by
  have hf := n06_canonicalSource_contDiffOn hgeom hz hs
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : PolarPoint => (1 : ℝ)) (annularOpen D)) m
  constructor
  · cases inv
    · exact hf
    · exact hf.inv (fun q hq => (n04Realization_sourceFactor_pos hgeom hz hs m hq).ne')
  · intro p _
    cases inv <;> rfl

/-- Composition of the actual absolute Jacobian needs only positive
outer coordinate jets and positive inner coordinate jets. -/
theorem n04Realization_absJacobian_comp_envelope
    {X : Type*} {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → PolarPoint)
    (F Q : X → PolarPoint → PolarPoint)
    (hF : ∀ x, ContDiffAt ℝ ∞ (F x) (Q x (p x)))
    (hQ : ∀ x, ContDiffAt ℝ ∞ (Q x) (p x))
    (hne : ∀ x, planeJacobian (F x) (Q x (p x)) ≠ 0) (n : ℕ)
    (hFj : ∀ j, 0 < j → j ≤ n + 1 → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (F x) (Q x (p x))‖))
    (hQj : ∀ j, 0 < j → j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (Q x) (p x)‖)) :
    HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n
      (fun y => |planeJacobian (F x) (Q x y)|) (p x)‖) := by
  have hJ (x : X) : ContDiffAt ℝ ∞ (planeJacobian (F x)) (Q x (p x)) :=
    ContinuousFlexibility.contDiffAt_planeJacobian (hF x)
  have hJj (j : ℕ) (hj : j ≤ n) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (fun y => |planeJacobian (F x) y|)
        (Q x (p x))‖) :=
    n04Realization_envelope_abs_jets (fun x => Q x (p x))
      (fun x => planeJacobian (F x)) (fun x => (hJ x).continuousAt) hne j
      (n04Realization_envelope_planeJacobian_jets hW (fun x => Q x (p x)) F hF j
        (fun k hk hkj => hFj k hk (by omega)))
  exact n04Realization_envelope_comp_jets hW p
    (fun x y => |planeJacobian (F x) y|) Q
    (fun x => (hJ x).abs (hne x)) hQ n hJj hQj

/-- Every field of the raw-factor certificate follows from the three
actual chart/atom families. Both occurrences of a reference point use
the current canonical coordinate, on the same piece and material point. -/
theorem n04Realization_primitiveFactor_envelopes
    {X : Type*} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x)
    (z : X → AnnularState S × ℝ) (m : X → ℕ) (p : X → PolarPoint)
    (hz : ∀ x, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x, stateSector S (z x).1)
    (hp : ∀ x, n07bMaterialRadiusChart T (p x) ∈ physicalPieceOpen S K (z x) (m x))
    (hE : ∀ x, T.E0 (T.radius (p x).1) ≤ W x) (N : ℕ)
    (hraw : N04RealizationChartAtomEnvelopesAtOrder X D T S C L K base high ε (N + 2))
    (hcurrentBase : ∀ x, T.E0 (T.sample (K.cell (m x))) *
      (1 + stateGrading S high ((z x).1 - C.referenceState) + |(z x).2|) ≤ W x)
    (hrefBase : ∀ x, T.E0 (T.sample (K.cell (m x))) ≤ W x) :
    N04RealizationPrimitiveFactorEnvelopes X T S C K W z m p N := by
  let ζ : Bool → X → AnnularState S × ℝ :=
    fun reference x => if reference then (C.referenceState, 0) else z x
  have hζ (b : Bool) (x : X) : ζ b x ∈ stateNeighborhood S C base ε := by
    cases b
    · exact hz x
    · exact href
  have hsζ (b : Bool) (x : X) : stateSector S (ζ b x).1 := by
    cases b
    · exact hs x
    · exact hsref
  have hbase₀ (b : Bool) (x : X) : 0 ≤ T.E0 (T.sample (K.cell (m x))) *
      (1 + stateGrading S high ((ζ b x).1 - C.referenceState) + |(ζ b x).2|) :=
    mul_nonneg
      (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell (m x)))).2.2.1.le
      (add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _))
  have hbaseW (b : Bool) (x : X) : T.E0 (T.sample (K.cell (m x))) *
      (1 + stateGrading S high ((ζ b x).1 - C.referenceState) + |(ζ b x).2|) ≤ W x := by
    cases b
    · exact hcurrentBase x
    · simpa only [ζ, ↓reduceIte, Prod.fst, Prod.snd, sub_self, map_zero,
        abs_zero, add_zero, mul_one] using hrefBase x
  have hFj (b : Bool) (s : X → PolarPoint)
      (hmem : ∀ x, s x ∈ physicalPieceOpen S K (ζ b x) (m x))
      (j : ℕ) (hj : 0 < j) (hjN : j ≤ N + 2) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (K.chart (ζ b x) (m x)) (s x)‖) :=
    ((hraw (ζ b) m (hζ b) (hsζ b)).1 s hmem j hj hjN).base_mono (hbase₀ b) (hbaseW b)
  have hGj (b : Bool) (s : X → PolarPoint)
      (hmem : ∀ x, s x ∈ canonicalOpen S K (m x))
      (j : ℕ) (hj : 0 < j) (hjN : j ≤ N + 2) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (K.inverseChart (ζ b x) (m x)) (s x)‖) :=
    ((hraw (ζ b) m (hζ b) (hsζ b)).2.1 s hmem j hj hjN).base_mono
      (hbase₀ b) (hbaseW b)
  have hsF (b : Bool) (s : X → PolarPoint)
      (hmem : ∀ x, s x ∈ physicalPieceOpen S K (ζ b x) (m x)) (x : X) :
      ContDiffAt ℝ ∞ (K.chart (ζ b x) (m x)) (s x) :=
    (hgeom.charts (ζ b x) (hζ b x) (hsζ b x) (m x)).2.2.2.2.1.contDiffAt
      ((hgeom.domains (ζ b x) (hζ b x) (hsζ b x) (m x)).1.mem_nhds (hmem x))
  have hsG (b : Bool) (s : X → PolarPoint)
      (hmem : ∀ x, s x ∈ canonicalOpen S K (m x)) (x : X) :
      ContDiffAt ℝ ∞ (K.inverseChart (ζ b x) (m x)) (s x) :=
    (hgeom.charts (ζ b x) (hζ b x) (hsζ b x) (m x)).2.2.2.2.2.1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hmem x))
  have hFne (b : Bool) (s : X → PolarPoint)
      (hmem : ∀ x, s x ∈ physicalPieceOpen S K (ζ b x) (m x)) (x : X) :
      planeJacobian (K.chart (ζ b x) (m x)) (s x) ≠ 0 :=
    ((hgeom.charts (ζ b x) (hζ b x) (hsζ b x) (m x)).2.2.2.2.2.2.2 _ (hmem x)).2.1
  have hGne (b : Bool) (s : X → PolarPoint)
      (hmem : ∀ x, s x ∈ canonicalOpen S K (m x)) (x : X) :
      planeJacobian (K.inverseChart (ζ b x) (m x)) (s x) ≠ 0 :=
    n04Realization_inverseChart_jacobian_ne hgeom (hζ b x) (hsζ b x) (m x) (hmem x)
  have hR := n07bMaterialRadiusChart_contDiff hT
  have hRj (j : ℕ) (hj : 0 < j) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (n07bMaterialRadiusChart T) (p x)‖) := by
    obtain ⟨B, _, hb⟩ := n04Realization_materialRadius_positive_jets hT j hj
    exact (hasPositiveEnvelope_const W hW B).mono (fun x => hb (p x))
  let Q : X → PolarPoint → PolarPoint := fun x => K.chart (z x) (m x) ∘ n07bMaterialRadiusChart T
  have hQmem (x : X) : Q x (p x) ∈ canonicalOpen S K (m x) :=
    (hgeom.charts (z x) (hz x) (hs x) (m x)).1 (hp x)
  have hQ (x : X) : ContDiffAt ℝ ∞ (Q x) (p x) :=
    (hsF false (fun x => n07bMaterialRadiusChart T (p x)) hp x).comp (p x) hR.contDiffAt
  have hQj (j : ℕ) (hj : 0 < j) (hjN : j ≤ N + 1) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (Q x) (p x)‖) :=
    n04Realization_envelope_comp_positive_jets hW p (fun x => K.chart (z x) (m x))
      (fun _ => n07bMaterialRadiusChart T)
      (hsF false (fun x => n07bMaterialRadiusChart T (p x)) hp)
      (fun _ => hR.contDiffAt) hj
      (fun k hk hkj => hFj false (fun x => n07bMaterialRadiusChart T (p x)) hp k hk (by omega))
      (fun k hk _ => hRj k hk)
  let Θ : X → PolarPoint → PolarPoint := fun x =>
    canonicalReferencePoint C K (z x) (m x) ∘ n07bMaterialRadiusChart T
  have hΘmem (x : X) : Θ x (p x) ∈ physicalPieceOpen S K (C.referenceState, 0) (m x) :=
    (hgeom.charts (C.referenceState, 0) href hsref (m x)).2.1 (hQmem x)
  have hΘ (x : X) : ContDiffAt ℝ ∞ (Θ x) (p x) :=
    (hsG true (fun x => Q x (p x)) hQmem x).comp (p x) (hQ x)
  have hΘj (j : ℕ) (hj : 0 < j) (hjN : j ≤ N + 1) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (Θ x) (p x)‖) :=
    n04Realization_envelope_comp_positive_jets hW p
      (fun x => K.inverseChart (C.referenceState, 0) (m x)) Q
      (hsG true (fun x => Q x (p x)) hQmem) hQ hj
      (fun k hk hkj => hGj true (fun x => Q x (p x)) hQmem k hk (by omega))
      (fun k hk hkj => hQj k hk (hkj.trans hjN))
  let J : X → PolarPoint → ℝ := fun x y =>
    |planeJacobian (K.chart (z x) (m x)) (n07bMaterialRadiusChart T y)|
  let I : X → PolarPoint → ℝ := fun x y =>
    |planeJacobian (K.inverseChart (z x) (m x)) (Q x y)|
  have hJ (x : X) : ContDiffAt ℝ ∞ (J x) (p x) :=
    ((ContinuousFlexibility.contDiffAt_planeJacobian
      (hsF false (fun x => n07bMaterialRadiusChart T (p x)) hp x)).abs
      (hFne false (fun x => n07bMaterialRadiusChart T (p x)) hp x)).comp (p x) hR.contDiffAt
  have hI (x : X) : ContDiffAt ℝ ∞ (I x) (p x) :=
    ((ContinuousFlexibility.contDiffAt_planeJacobian
      (hsG false (fun x => Q x (p x)) hQmem x)).abs
      (hGne false (fun x => Q x (p x)) hQmem x)).comp (p x) (hQ x)
  have hJj (j : ℕ) (hj : j ≤ N + 1) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (J x) (p x)‖) :=
    n04Realization_absJacobian_comp_envelope hW p (fun x => K.chart (z x) (m x))
      (fun _ => n07bMaterialRadiusChart T)
      (hsF false (fun x => n07bMaterialRadiusChart T (p x)) hp) (fun _ => hR.contDiffAt)
      (hFne false (fun x => n07bMaterialRadiusChart T (p x)) hp) j
      (fun k hk hkj => hFj false (fun x => n07bMaterialRadiusChart T (p x)) hp k hk (by omega))
      (fun k hk _ => hRj k hk)
  have hIj (j : ℕ) (hj : j ≤ N + 1) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (I x) (p x)‖) :=
    n04Realization_absJacobian_comp_envelope hW p (fun x => K.inverseChart (z x) (m x)) Q
      (hsG false (fun x => Q x (p x)) hQmem) hQ
      (hGne false (fun x => Q x (p x)) hQmem) j
      (fun k hk hkj => hGj false (fun x => Q x (p x)) hQmem k hk (by omega))
      (fun k hk hkj => hQj k hk (hkj.trans hj))
  have hell : ContDiff ℝ ∞ (fun y : PolarPoint => T.ell (T.radius y.1)) :=
    (hT.1 T.ell (by simp)).comp_contDiff
      ((hT.2.2.2.2.2.2.1).comp contDiff_fst)
      (fun y => (hT.2.2.2.2.2.2.2.1 y.1).1)
  have hellInv : ContDiff ℝ ∞ (fun y : PolarPoint => (T.ell (T.radius y.1))⁻¹) :=
    hell.inv (fun y => (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 y.1).1).1.ne')
  have hellj (j : ℕ) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (fun y : PolarPoint => T.ell (T.radius y.1)) (p x)‖) := by
    obtain ⟨B, _, hb⟩ := n04Realization_materialEll_jets hT j
    exact (hasPositiveEnvelope_const W hW B).mono (fun x => hb (p x))
  refine
    { currentPoint := hQj
      referencePoint := hΘj
      inverseDifferential := ?_
      referenceDifferential := ?_
      inverseJacobian := hIj
      referenceJacobian := ?_
      density := ?_
      inverseDensity := ?_
      source := ?_ }
  · intro j hj
    exact n04Realization_envelope_comp_jets hW p
      (fun x => fderiv ℝ (K.inverseChart (z x) (m x))) Q
      (fun x => (hsG false (fun x => Q x (p x)) hQmem x).fderiv_right (m := ∞) (by simp)) hQ j
      (fun k hk => n04Realization_envelope_fderiv_jets (fun x => Q x (p x))
        (fun x => K.inverseChart (z x) (m x)) k
        (hGj false (fun x => Q x (p x)) hQmem (k + 1) (by omega) (by omega)))
      (fun k hk hkj => hQj k hk (hkj.trans hj))
  · intro j hj
    exact n04Realization_envelope_comp_jets hW p
      (fun x => fderiv ℝ (K.chart (C.referenceState, 0) (m x))) Θ
      (fun x => (hsF true (fun x => Θ x (p x)) hΘmem x).fderiv_right (m := ∞) (by simp)) hΘ j
      (fun k hk => n04Realization_envelope_fderiv_jets (fun x => Θ x (p x))
        (fun x => K.chart (C.referenceState, 0) (m x)) k
        (hFj true (fun x => Θ x (p x)) hΘmem (k + 1) (by omega) (by omega)))
      (fun k hk hkj => hΘj k hk (hkj.trans hj))
  · intro j hj
    exact n04Realization_absJacobian_comp_envelope hW p
      (fun x => K.chart (C.referenceState, 0) (m x)) Θ
      (hsF true (fun x => Θ x (p x)) hΘmem) hΘ
      (hFne true (fun x => Θ x (p x)) hΘmem) j
      (fun k hk hkj => hFj true (fun x => Θ x (p x)) hΘmem k hk (by omega))
      (fun k hk hkj => hΘj k hk (hkj.trans hj))
  · intro j hj
    have h := n04Realization_envelope_mul_jets hW p
      (fun _ y => T.ell (T.radius y.1)) J (fun _ => hell.contDiffAt) hJ j
      (fun k _ => hellj k) (fun k hk => hJj k (hk.trans hj))
    simpa only [J, canonicalMaterialJacobian, Function.comp_apply, n07bMaterialRadiusChart] using h
  · intro j hj
    have h := n04Realization_envelope_mul_jets hW p
      (fun _ y => (T.ell (T.radius y.1))⁻¹) I (fun _ => hellInv.contDiffAt) hI j
      (fun k _ => n04Realization_materialEllInverse_envelope hT hW p hE k)
      (fun k hk => hIj k (hk.trans hj))
    apply n04Realization_envelope_jets_congr p
      (fun x y => (T.ell (T.radius y.1))⁻¹ * I x y)
      (fun x y => (canonicalMaterialJacobian T K (z x) (m x)
        (n07bMaterialRadiusChart T y))⁻¹) j h
    intro x
    filter_upwards [(n07bSourceMaterialPiece_isOpen hT hgeom (hz x) (hs x) (m x)).mem_nhds
      (hp x)] with y hy
    exact (n04Realization_materialJacobian_inverse_eqOn hgeom (hz x) (hs x) (m x) hy).symm
  · intro b inv j hj
    let A : X → PolarPoint → ℝ := fun x q => if inv then
      (canonicalSource S K (ζ b x) (m x) (fun _ => 1) q)⁻¹
      else canonicalSource S K (ζ b x) (m x) (fun _ => 1) q
    have hA (x : X) := n04Realization_sourceFactor_atom_input (T := T) (L := L)
      hgeom (hζ b x) (hsζ b x) (m x) inv
    have hAj (k : ℕ) (hk : k ≤ j) : HasPositiveEnvelope W
        (fun x => ‖iteratedFDeriv ℝ k (A x) (Q x (p x))‖) :=
      ((hraw (ζ b) m (hζ b) (hsζ b)).2.2 (fun x => Q x (p x))
        (fun _ => if inv then .sourceFactorInverse else .sourceFactor) A hQmem
        (fun x => (hA x).1) (fun x => (hA x).2) k (by omega)).base_mono
          (hbase₀ b) (hbaseW b)
    exact n04Realization_envelope_comp_jets hW p A Q
      (fun x => (hA x).1.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hQmem x)))
      hQ j hAj (fun k hk hkj => hQj k hk (hkj.trans hj))

end ContinuousFlexibility.Analysis
