import ContinuousFlexibility.Analysis.N04bActualAtlasCuts
import ContinuousFlexibility.Analysis.CanonicalRootTransportBoundary
import ContinuousFlexibility.Analysis.OpenGermBoundaryJets

/-!
# Boundary jets of any matched model equal the stored atlas jets

The actual atlas and the supplied root model agree with the same physical
chart and height on the positive collar. Their ordinary boundary jets
therefore agree, independently of which smooth root model the atlas
construction selected. No common collar in the state parameter is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem matchedRoot_boundaryJets
    {r σ δ : ℝ} (hδ : 0 < δ)
    {F M : PolarPoint → PolarPoint} {h u : PolarPoint → ℝ}
    (hF : ∀ θ, ContDiffAt ℝ ∞ F (r, θ))
    (hh : ∀ θ, ContDiffAt ℝ ∞ h (r, θ))
    (hM : ∀ θ, ContDiffAt ℝ ∞ M (0, θ))
    (hu : ∀ θ, ContDiffAt ℝ ∞ u (0, θ))
    (hmatch : ∀ p ∈ Ioo (0 : ℝ) δ ×ˢ (univ : Set ℝ),
      F (rootProfileShift r σ p) = M p ∧ h (rootProfileShift r σ p) = u p)
    (θ : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun p => F (rootProfileShift r σ p)) (0, θ) =
        iteratedFDeriv ℝ n M (0, θ) ∧
      iteratedFDeriv ℝ n (fun p => h (rootProfileShift r σ p)) (0, θ) =
        iteratedFDeriv ℝ n u (0, θ) := by
  let Ω : Set PolarPoint := Ioo (0 : ℝ) δ ×ˢ (univ : Set ℝ)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  have hx : (0, θ) ∈ closure Ω := by
    dsimp only [Ω]
    rw [closure_prod_eq, closure_Ioo hδ.ne, closure_univ]
    exact ⟨⟨le_rfl, hδ.le⟩, mem_univ _⟩
  have harg : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hpoint : rootProfileShift r σ (0, θ) = (r, θ) := by
    simp only [rootProfileShift, mul_zero, add_zero]
  have hFc : ContDiffAt ℝ ∞ (fun p => F (rootProfileShift r σ p)) (0, θ) := by
    have hfAt : ContDiffAt ℝ ∞ F (rootProfileShift r σ (0, θ)) := by
      simpa only [hpoint] using hF θ
    simpa only [Function.comp_def] using hfAt.comp (0, θ) harg.contDiffAt
  have hhc : ContDiffAt ℝ ∞ (fun p => h (rootProfileShift r σ p)) (0, θ) := by
    have hhAt : ContDiffAt ℝ ∞ h (rootProfileShift r σ (0, θ)) := by
      simpa only [hpoint] using hh θ
    simpa only [Function.comp_def] using hhAt.comp (0, θ) harg.contDiffAt
  exact ⟨iteratedFDeriv_eq_of_eqOn_open_of_mem_closure hΩ hx
      (fun p hp => (hmatch p hp).1) hFc (hM θ) n,
    iteratedFDeriv_eq_of_eqOn_open_of_mem_closure hΩ hx
      (fun p hp => (hmatch p hp).2) hhc (hu θ) n⟩

/-- A supplied matched root collar determines the ordinary jets of the
same actual typed atlas, even if its internal smooth witness differs. -/
theorem n04Realization_actualAtlas_matchedRoot_boundaryJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool)
    {δ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (hδ : 0 < δ)
    (hcollar : N04bRootChartHeightCollar D L z
      (if side then C.right m else C.left m) (if side then -1 else 1) G δ)
    (hphysical : MapsTo
      (rootProfileShift (if side then C.right m else C.left m)
        (if side then -1 else 1))
      (Ioo (0 : ℝ) δ ×ˢ (univ : Set ℝ))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hmatch : ∀ x ∈ Ioo (0 : ℝ) δ, ∀ θ : ℝ,
      let p := rootProfileShift (if side then C.right m else C.left m)
        (if side then -1 else 1) (x, θ)
      extendedRootEvenOddChart G (x, θ) =
        n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side p ∧
      rootSmoothHeight (n04bRootLeadingCoefficient L z
          (if side then C.right m else C.left m) (if side then -1 else 1)) G (x, θ) =
        n04bRootPhysicalHeight (L.coefficients z)
          (n04bCharacteristicHalfGap (L.coefficients z))
          (n04bActualTravelChart S C L z m) (C.travel m) side p) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := e.symm (.inl (m, side))
    let r := if side then C.right m else C.left m
    let σ : ℝ := if side then -1 else 1
    ∀ θ : ℝ, ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun p => K.chart z k (rootProfileShift r σ p)) (0, θ) =
          iteratedFDeriv ℝ n (extendedRootEvenOddChart G) (0, θ) ∧
        iteratedFDeriv ℝ n (fun p => K.height z k (rootProfileShift r σ p)) (0, θ) =
          iteratedFDeriv ℝ n
            (rootSmoothHeight (n04bRootLeadingCoefficient L z r σ) G) (0, θ) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k : ℕ := e.symm (.inl (m, side))
  let r : ℝ := if side then C.right m else C.left m
  let σ : ℝ := if side then -1 else 1
  have hA : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hcut : CanonicalCutGeometry S C K base ε :=
    n04bActualTypedAtlas_cutGeometry hT hS hN hfield e
  have hpair : K.cutPair m =
      (e.symm (.inl (m, false)), e.symm (.inl (m, true))) := rfl
  have hindex : (if side then (K.cutPair m).2 else (K.cutPair m).1) = k := by
    rw [hpair]
    cases side <;> rfl
  have hclosed (θ : ℝ) : (r, θ) ∈ physicalPieceClosed S K z k := by
    simpa only [hindex] using
      (canonicalCutRoot_mem_closed_and_zero hA hcut hz hs m side θ).1
  have hregular (θ : ℝ) := (hA.boundary z hz hs k).2.2.2.2.1 (r, θ) (hclosed θ)
  have hmodel (θ : ℝ) :
      ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (0, θ) ∧
        ContDiffAt ℝ ∞ (rootSmoothHeight (n04bRootLeadingCoefficient L z r σ) G) (0, θ) := by
    obtain ⟨_, hF, _, _, _, _, hh, _, _⟩ :=
      hcollar 0 θ (by simpa only [abs_zero] using hδ)
    exact ⟨hF, hh⟩
  dsimp only
  intro θ n
  refine matchedRoot_boundaryJets hδ
    (fun θ => (hregular θ).1) (fun θ => (hregular θ).2.1)
    (fun θ => (hmodel θ).1) (fun θ => (hmodel θ).2) ?_ θ n
  intro p hp
  have hactual := n04bActualTypedAtlas_negative_component_germs hT hS hN hfield
    e hz hs k m side (e.apply_symm_apply (.inl (m, side))) (hphysical hp)
  have hm := hmatch p.1 hp.1 p.2
  exact ⟨hactual.1.eq_of_nhds.trans hm.1.symm,
    hactual.2.eq_of_nhds.trans hm.2.symm⟩

end ContinuousFlexibility.Analysis
