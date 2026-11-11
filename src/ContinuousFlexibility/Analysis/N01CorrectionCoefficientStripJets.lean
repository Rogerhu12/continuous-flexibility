import ContinuousFlexibility.Analysis.N01CorrectionCoefficientJointTower
import ContinuousFlexibility.Analysis.JointJetSpatialRegularity

/-!
# Spatial regularity of the actual coefficient jets on a buffered strip

Uniqueness identifies the previously constructed pointwise parameter
jets with the pure parameter slots of the actual joint tower. Its
spatial smoothness and mixed-derivative recurrence therefore apply to
the same raw coefficient family used in the source construction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientStripJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
  (hdisc : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m p, p.1 ∈ Ioo (C.left m) (C.right m) → deriv (χ m) p.1 ≠ 0 →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
  (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)
  (hstrip : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ p : PolarPoint,
    p.1 ∈ Ioo l h →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

theorem N01Properties.returnCorrectionCoefficientScalarJets_eq_joint_on_strip
    (Q : (ℝ × ℝ) →L[ℝ] ℝ)
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S)
    {p : PolarPoint} (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ)) :
    Q (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff
        hdisc n x v p) =
      (solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) l h hl hh hstrip) Q).D
        n (x, p) (fun i => (v i, 0)) := by
  let J := solveSmoothDirectionsPostcomp
    (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
      m (j m) (hcell m) l h hl hh hstrip) Q
  let K := solveSmoothDirectionsPostcomp
    (hN.returnCorrectionCoefficient_pointTower hS hT hR j hcell χ hχrange hcutoff hdisc p) Q
  exact J.pointTower_eq_jointJet
    ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ) p hp K n x hx v

theorem N01Properties.returnCorrectionCoefficientScalarJets_component_contDiffOn_strip
    (Q : (ℝ × ℝ) →L[ℝ] ℝ)
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) :
    ContDiffOn ℝ ∞ (fun p => Q
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc n x v p))
      (Ioo l h ×ˢ univ) := by
  let J := solveSmoothDirectionsPostcomp
    (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
      m (j m) (hcell m) l h hl hh hstrip) Q
  apply (J.jointJet_spatial_contDiffOn (isOpen_Ioo.prod isOpen_univ)
    n x hx (fun i => (v i, 0))).congr
  intro p hp
  exact hN.returnCorrectionCoefficientScalarJets_eq_joint_on_strip
    hS hT hR j hcell χ hχrange hcutoff hdisc hχ m l h hl hh hstrip Q n x hx v hp

theorem N01Properties.returnCorrectionCoefficientScalarJets_contDiffOn_strip
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) :
    ContDiffOn ℝ ∞
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc n x v)
      (Ioo l h ×ˢ univ) :=
  (hN.returnCorrectionCoefficientScalarJets_component_contDiffOn_strip hS hT hR
    j hcell χ hχrange hcutoff hdisc hχ m l h hl hh hstrip
    (ContinuousLinearMap.fst ℝ ℝ ℝ) n x hx v).prodMk
      (hN.returnCorrectionCoefficientScalarJets_component_contDiffOn_strip hS hT hR
        j hcell χ hχrange hcutoff hdisc hχ m l h hl hh hstrip
        (ContinuousLinearMap.snd ℝ ℝ ℝ) n x hx v)

theorem N01Properties.returnCorrectionCoefficientScalarJets_component_mixed_hasDerivAt_line_strip
    (Q : (ℝ × ℝ) →L[ℝ] ℝ) (a b n : ℕ)
    (x w : (StateDirections S × ℝ) × CircleSpace S)
    {t : ℝ} (ht : x + t • w ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S)
    {p : PolarPoint} (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ)) :
    HasDerivAt
      (fun s => mixedDerivative a b (fun q => Q
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          n (x + s • w) v q)) p)
      (mixedDerivative a b (fun q => Q
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          (n + 1) (x + t • w) (Fin.cons w v) q)) p) t := by
  let J := solveSmoothDirectionsPostcomp
    (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
      m (j m) (hcell m) l h hl hh hstrip) Q
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod
    (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))
  have hV := (isOpen_Ioo : IsOpen (Ioo l h)).prod (isOpen_univ : IsOpen (univ : Set ℝ))
  have hc := ((sectorNeighborhood_convex S base ε ε).prod
    (convex_univ : Convex ℝ (univ : Set (CircleSpace S)))).prod
      ((convex_Ioo l h).prod (convex_univ : Convex ℝ (univ : Set ℝ)))
  have heq (k : ℕ) (y : (StateDirections S × ℝ) × CircleSpace S)
      (hy : y ∈ sectorNeighborhood S base ε ε ×ˢ univ)
      (vs : Fin k → (StateDirections S × ℝ) × CircleSpace S) :
      mixedDerivative a b (fun q => Q
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc k y vs q)) p =
        mixedDerivative a b (fun q => J.D k (y, q) (fun i => (vs i, 0))) p :=
    mixedDerivative_congr_on_open hV
      (fun q hq => hN.returnCorrectionCoefficientScalarJets_eq_joint_on_strip
        hS hT hR j hcell χ hχrange hcutoff hdisc hχ m l h hl hh hstrip Q k y hy vs hq) a b hp
  have hcons : (fun i : Fin (n + 1) => ((Fin.cons w v) i, (0 : PolarPoint))) =
      Fin.cons (w, 0) (fun i => (v i, 0)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hd := J.jointJet_mixed_hasDerivAt_line hU hV hc a b n x w ht
    (fun i => (v i, 0)) hp
  have hvalue := heq (n + 1) (x + t • w) ht (Fin.cons w v)
  rw [hcons] at hvalue
  apply (hd.congr_deriv hvalue.symm).congr_of_eventuallyEq
  have hnear : ∀ᶠ s in 𝓝 t, x + s • w ∈ sectorNeighborhood S base ε ε ×ˢ univ :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
      (hU.mem_nhds ht)
  filter_upwards [hnear] with s hs
  exact heq n (x + s • w) hs v

theorem N01Properties.returnCorrectionCoefficientScalarJets_mixed_hasDerivAt_line_strip
    (a b n : ℕ) (x w : (StateDirections S × ℝ) × CircleSpace S)
    {t : ℝ} (ht : x + t • w ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S)
    {p : PolarPoint} (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ)) :
    HasDerivAt
      (fun s => mixedDerivative a b (fun q =>
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          n (x + s • w) v q).1) p)
      (mixedDerivative a b (fun q =>
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          (n + 1) (x + t • w) (Fin.cons w v) q).1) p) t ∧
    HasDerivAt
      (fun s => mixedDerivative a b (fun q =>
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          n (x + s • w) v q).2) p)
      (mixedDerivative a b (fun q =>
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          (n + 1) (x + t • w) (Fin.cons w v) q).2) p) t :=
  ⟨hN.returnCorrectionCoefficientScalarJets_component_mixed_hasDerivAt_line_strip
    hS hT hR j hcell χ hχrange hcutoff hdisc hχ m l h hl hh hstrip
    (ContinuousLinearMap.fst ℝ ℝ ℝ) a b n x w ht v hp,
    hN.returnCorrectionCoefficientScalarJets_component_mixed_hasDerivAt_line_strip
    hS hT hR j hcell χ hχrange hcutoff hdisc hχ m l h hl hh hstrip
    (ContinuousLinearMap.snd ℝ ℝ ℝ) a b n x w ht v hp⟩

end ContinuousFlexibility.Statements
