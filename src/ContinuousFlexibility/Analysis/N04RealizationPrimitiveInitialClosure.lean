module

public import ContinuousFlexibility.Analysis.N04RealizationPrimitiveFactorEnvelopes

/-!
# The three actual normalized initial factors

The common normalizer is multiplied by the current source factor,
reciprocal height, or actual reference/current height ratio. The latter
two are reconstructed from source factors and genuine inverse/reference
Jacobians on the same open material piece before jets are transferred.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}

theorem n04Realization_primitiveInitial_envelopes
    {X : Type*} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x)
    (z : X → AnnularState S × ℝ) (m : X → ℕ) (p : X → PolarPoint)
    (hz : ∀ x, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x, stateSector S (z x).1)
    (hp : ∀ x, n07bMaterialRadiusChart T (p x) ∈ physicalPieceOpen S K (z x) (m x))
    (hRatio : HasPositiveEnvelope W
      (fun x => T.H (T.radius (p x).1) / T.H (T.sample (K.cell (m x))))) (N : ℕ)
    (H : N04RealizationPrimitiveFactorEnvelopes X T S C K W z m p N) :
    ∀ i : Fin 3, ∀ k : ℕ, k ≤ N → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ k
        (canonicalPrimitiveField D T C K (z x) (m x) (.inr (.inl i)) ∘
          n07bMaterialRadiusChart T) (p x)‖) := by
  have hR := n07bMaterialRadiusChart_contDiff hT
  let Q : X → PolarPoint → PolarPoint := fun x => K.chart (z x) (m x) ∘ n07bMaterialRadiusChart T
  let Θ : X → PolarPoint → PolarPoint := fun x =>
    canonicalReferencePoint C K (z x) (m x) ∘ n07bMaterialRadiusChart T
  have hQmem (x : X) : Q x (p x) ∈ canonicalOpen S K (m x) :=
    (hgeom.charts (z x) (hz x) (hs x) (m x)).1 (hp x)
  have hQ (x : X) : ContDiffAt ℝ ∞ (Q x) (p x) :=
    ((hgeom.charts (z x) (hz x) (hs x) (m x)).2.2.2.2.1.contDiffAt
      ((hgeom.domains (z x) (hz x) (hs x) (m x)).1.mem_nhds (hp x))).comp
        (p x) hR.contDiffAt
  have hΘmem (x : X) : Θ x (p x) ∈ physicalPieceOpen S K (C.referenceState, 0) (m x) :=
    (hgeom.charts (C.referenceState, 0) href hsref (m x)).2.1 (hQmem x)
  have hΘ (x : X) : ContDiffAt ℝ ∞ (Θ x) (p x) :=
    ((n07b_canonicalReferencePoint_contDiffOn hgeom href hsref (hz x) (hs x) (m x)).contDiffAt
      ((hgeom.domains (z x) (hz x) (hs x) (m x)).1.mem_nhds (hp x))).comp
        (p x) hR.contDiffAt
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
  let σ : Bool → Bool → X → PolarPoint → ℝ := fun b inv x y =>
    if inv then (canonicalSource S K (ζ b x) (m x) (fun _ => 1) (Q x y))⁻¹
    else canonicalSource S K (ζ b x) (m x) (fun _ => 1) (Q x y)
  have hσ (b inv : Bool) (x : X) : ContDiffAt ℝ ∞ (σ b inv x) (p x) := by
    have hc := ((n06_canonicalSource_contDiffOn hgeom (hζ b x) (hsζ b x)
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : PolarPoint => (1 : ℝ)) (annularOpen D))
      (m x)).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hQmem x))).comp (p x) (hQ x)
    cases inv
    · exact hc
    · exact hc.inv (n04Realization_sourceFactor_pos hgeom (hζ b x) (hsζ b x) (m x) (hQmem x)).ne'
  have hσj (b inv : Bool) (j : ℕ) (hj : j ≤ N) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (σ b inv x) (p x)‖) := H.source b inv j (by omega)
  let I : X → PolarPoint → ℝ := fun x y => |planeJacobian (K.inverseChart (z x) (m x)) (Q x y)|
  let J : X → PolarPoint → ℝ := fun x y =>
    |planeJacobian (K.chart (C.referenceState, 0) (m x)) (Θ x y)|
  have hI (x : X) : ContDiffAt ℝ ∞ (I x) (p x) :=
    ((ContinuousFlexibility.contDiffAt_planeJacobian
      ((hgeom.charts (z x) (hz x) (hs x) (m x)).2.2.2.2.2.1.contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hQmem x)))).abs
      (n04Realization_inverseChart_jacobian_ne hgeom (hz x) (hs x) (m x) (hQmem x))).comp
        (p x) (hQ x)
  have hJ (x : X) : ContDiffAt ℝ ∞ (J x) (p x) :=
    ((ContinuousFlexibility.contDiffAt_planeJacobian
      ((hgeom.charts (C.referenceState, 0) href hsref (m x)).2.2.2.2.1.contDiffAt
        ((hgeom.domains (C.referenceState, 0) href hsref (m x)).1.mem_nhds (hΘmem x)))).abs
      ((hgeom.charts (C.referenceState, 0) href hsref (m x)).2.2.2.2.2.2.2 _ (hΘmem x)).2.1).comp
        (p x) (hΘ x)
  let V : X → PolarPoint → ℝ := fun x y => σ false true x y * I x y
  let V₀ : X → PolarPoint → ℝ := fun x y => σ true false x y * J x y
  have hV (x : X) : ContDiffAt ℝ ∞ (V x) (p x) := (hσ false true x).mul (hI x)
  have hV₀ (x : X) : ContDiffAt ℝ ∞ (V₀ x) (p x) := (hσ true false x).mul (hJ x)
  have hVj (j : ℕ) (hj : j ≤ N) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (V x) (p x)‖) :=
    n04Realization_envelope_mul_jets hW p (σ false true) I (hσ false true) hI j
      (fun k hk => hσj false true k (hk.trans hj))
      (fun k hk => H.inverseJacobian k (by omega))
  have hV₀j (j : ℕ) (hj : j ≤ N) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (V₀ x) (p x)‖) :=
    n04Realization_envelope_mul_jets hW p (σ true false) J (hσ true false) hJ j
      (fun k hk => hσj true false k (hk.trans hj))
      (fun k hk => H.referenceJacobian k (by omega))
  have hVVj (j : ℕ) (hj : j ≤ N) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (fun y => V₀ x y * V x y) (p x)‖) :=
    n04Realization_envelope_mul_jets hW p V₀ V hV₀ hV j
      (fun k hk => hV₀j k (hk.trans hj)) (fun k hk => hVj k (hk.trans hj))
  let Z : X → PolarPoint → ℝ := fun x =>
    canonicalMaterialNormalizer T K (z x) (m x) (3 / 4 : ℝ) ∘ n07bMaterialRadiusChart T
  have hZ (x : X) : ContDiffAt ℝ ∞ (Z x) (p x) :=
    (n07b_sourceNormalizationFields_contDiffAt hD hT hgeom (hz x) (hs x) (m x)
      (3 / 4 : ℝ) (hp x)).2.1.comp (p x) hR.contDiffAt
  have hΩinv : HasPositiveEnvelope W
      (fun x => (canonicalMaterialJacobian T K (z x) (m x)
        (n07bMaterialRadiusChart T (p x)))⁻¹) := by
    apply (H.inverseDensity 0 (by omega)).mono
    intro x
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      le_abs_self ((canonicalMaterialJacobian T K (z x) (m x)
        (n07bMaterialRadiusChart T (p x)))⁻¹)
  have hZj (j : ℕ) (hj : j ≤ N) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (Z x) (p x)‖) :=
    n04Realization_materialNormalizer_envelope hD hT hgeom hW z m p hz hs hp hRatio j
      (fun k hk => H.density k (by omega)) hΩinv
  intro i k hk
  fin_cases i
  · have h := n04Realization_envelope_mul_jets hW p Z (σ false false) hZ (hσ false false) k
      (fun j hj => hZj j (hj.trans hk)) (fun j hj => hσj false false j (hj.trans hk))
    apply n04Realization_envelope_jets_congr p (fun x y => Z x y * σ false false x y)
      (fun x => canonicalPrimitiveField D T C K (z x) (m x) (.inr (.inl 0)) ∘
        n07bMaterialRadiusChart T) k h
    intro x
    filter_upwards [(n07bSourceMaterialPiece_isOpen hT hgeom (hz x) (hs x) (m x)).mem_nhds
      (hp x)] with y hy
    exact congrArg (fun t : ℝ => Z x y * t)
      (n04Realization_materialSourceFactor_eqOn hgeom (hz x) (hs x) (m x) hy).symm
  · have h := n04Realization_envelope_mul_jets hW p Z V hZ hV k
      (fun j hj => hZj j (hj.trans hk)) (fun j hj => hVj j (hj.trans hk))
    apply n04Realization_envelope_jets_congr p (fun x y => Z x y * V x y)
      (fun x => canonicalPrimitiveField D T C K (z x) (m x) (.inr (.inl 1)) ∘
        n07bMaterialRadiusChart T) k h
    intro x
    filter_upwards [(n07bSourceMaterialPiece_isOpen hT hgeom (hz x) (hs x) (m x)).mem_nhds
      (hp x)] with y hy
    exact congrArg (fun t : ℝ => Z x y * t)
      (n04Realization_materialHeightInverse_eqOn hgeom (hz x) (hs x) (m x) hy).symm
  · have h := n04Realization_envelope_mul_jets hW p Z (fun x y => V₀ x y * V x y)
      hZ (fun x => (hV₀ x).mul (hV x)) k
      (fun j hj => hZj j (hj.trans hk)) (fun j hj => hVVj j (hj.trans hk))
    apply n04Realization_envelope_jets_congr p (fun x y => Z x y * (V₀ x y * V x y))
      (fun x => canonicalPrimitiveField D T C K (z x) (m x) (.inr (.inl 2)) ∘
        n07bMaterialRadiusChart T) k h
    intro x
    filter_upwards [(n07bSourceMaterialPiece_isOpen hT hgeom (hz x) (hs x) (m x)).mem_nhds
      (hp x)] with y hy
    have he := n04Realization_materialReferenceHeightRatio_eqOn hgeom href hsref
      (hz x) (hs x) (m x) hy
    calc
      Z x y * (V₀ x y * V x y) =
          Z x y * (σ true false x y * J x y * σ false true x y * I x y) := by
        dsimp only [V₀, V]
        ring
      _ = canonicalPrimitiveField D T C K (z x) (m x) (.inr (.inl 2))
          (n07bMaterialRadiusChart T y) := congrArg (fun t : ℝ => Z x y * t) he.symm

end ContinuousFlexibility.Analysis
