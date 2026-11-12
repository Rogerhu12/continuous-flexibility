import ContinuousFlexibility.Analysis.N01CorrectionCoefficientStripJets
import ContinuousFlexibility.Analysis.MaterialCoordinateParameterDerivatives

/-!
# The actual correction coefficient jets on the whole annulus

Every point is either in one of the common positive open strips or has
one spatial neighborhood where all cutoff derivatives vanish. This
alternative is uniform over all states. The genuine strip towers and
the actual zero jets therefore patch at every parameter order, including
all mixed spatial derivatives. The material-coordinate recurrence is
then the chain rule for these same fields.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientSpatialJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01CorrectionCoefficientSpatialJetsSectorSMul (S : PhysicalSpacesData) :
    SMul ℝ (StateDirections S × ℝ) := Prod.instSMul

local instance n01CorrectionCoefficientSpatialJetsParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ ((StateDirections S × ℝ) × CircleSpace S) := Prod.instSMul

local instance n01CorrectionCoefficientSpatialJetsRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

private theorem coefficientSpatial_contDiffOn_of_cover
    {Ω : Set PolarPoint} {Z : PolarPoint → Prop}
    (l h : ℕ → ℝ) (f : PolarPoint → ℝ × ℝ)
    (hcover : ∀ p ∈ Ω, (∃ m, p.1 ∈ Ioo (l m) (h m)) ∨ Z p)
    (hstrip : ∀ m, ContDiffOn ℝ ∞ f (Ioo (l m) (h m) ×ˢ (univ : Set ℝ)))
    (hzero : ∀ p, Z p → f =ᶠ[𝓝 p] fun _ => 0) :
    ContDiffOn ℝ ∞ f Ω := by
  intro p hp
  rcases hcover p hp with ⟨m, hm⟩ | hz
  · exact ((hstrip m).contDiffAt
      (((isOpen_Ioo : IsOpen (Ioo (l m) (h m))).prod
        (isOpen_univ : IsOpen (univ : Set ℝ))).mem_nhds
          ⟨hm, mem_univ p.2⟩)).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq (hzero p hz)).contDiffWithinAt

private theorem coefficientSpatial_mixedLine_of_cover
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {Ω : Set PolarPoint} {Z : PolarPoint → Prop}
    (A : ∀ k : ℕ, E → (Fin k → E) → PolarPoint → ℝ)
    (l h : ℕ → ℝ) (hU : IsOpen U)
    (hcover : ∀ p ∈ Ω, (∃ m, p.1 ∈ Ioo (l m) (h m)) ∨ Z p)
    (hstrip : ∀ m (a b k : ℕ) (y w : E) (s : ℝ), y + s • w ∈ U →
      ∀ (vs : Fin k → E) (p : PolarPoint), p.1 ∈ Ioo (l m) (h m) →
        HasDerivAt (fun u => mixedDerivative a b (A k (y + u • w) vs) p)
          (mixedDerivative a b (A (k + 1) (y + s • w) (Fin.cons w vs)) p) s)
    (hzero : ∀ p, Z p → ∀ (a b k : ℕ) (y : E), y ∈ U →
      ∀ vs : Fin k → E, mixedDerivative a b (A k y vs) p = 0)
    (a b n : ℕ) (x w : E) {t : ℝ} (ht : x + t • w ∈ U)
    (v : Fin n → E) {p : PolarPoint} (hp : p ∈ Ω) :
    HasDerivAt (fun s => mixedDerivative a b (A n (x + s • w) v) p)
      (mixedDerivative a b (A (n + 1) (x + t • w) (Fin.cons w v)) p) t := by
  rcases hcover p hp with ⟨m, hm⟩ | hz
  · exact hstrip m a b n x w t ht v p hm
  · have hvalue := hzero p hz a b (n + 1) (x + t • w) ht (Fin.cons w v)
    apply ((hasDerivAt_const t (0 : ℝ)).congr_deriv hvalue.symm).congr_of_eventuallyEq
    have hnear : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
        (hU.mem_nhds ht)
    filter_upwards [hnear] with s hs
    exact hzero p hz a b n (x + s • w) hs v

private theorem correctionCoefficient_materialLine_of_ordinary
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (U : Set E) (hU : IsOpen U)
    (A : (k : ℕ) → E → (Fin k → E) → PolarPoint → ℝ × ℝ)
    (hregular : ∀ (k : ℕ) (y : E), y ∈ U → ∀ (vs : Fin k → E),
      ContDiffOn ℝ ∞ (A k y vs) (annularOpen D))
    (n : ℕ) (x w : E) (v : Fin n → E) (t : ℝ) (ht : x + t • w ∈ U)
    (hderiv : ∀ a b : ℕ, ∀ p ∈ annularOpen D,
      HasDerivAt
        (fun s => mixedDerivative a b (fun q => (A n (x + s • w) v q).1) p)
        (mixedDerivative a b (fun q => (A (n + 1) (x + t • w) (Fin.cons w v) q).1) p) t ∧
      HasDerivAt
        (fun s => mixedDerivative a b (fun q => (A n (x + s • w) v q).2) p)
        (mixedDerivative a b (fun q => (A (n + 1) (x + t • w) (Fin.cons w v) q).2) p) t) :
    MixedJetHasDerivAt
      (fun s q => (A n (x + s • w) v (T.radius q.1, q.2)).1)
      (fun q => (A (n + 1) (x + t • w) (Fin.cons w v) (T.radius q.1, q.2)).1) t ∧
    MixedJetHasDerivAt
      (fun s q => (A n (x + s • w) v (T.radius q.1, q.2)).2)
      (fun q => (A (n + 1) (x + t • w) (Fin.cons w v) (T.radius q.1, q.2)).2) t := by
  let F : ℝ → PolarPoint → ℝ × ℝ := fun s q => A n (x + s • w) v q
  let G : PolarPoint → ℝ × ℝ := A (n + 1) (x + t • w) (Fin.cons w v)
  have hline : Continuous (fun s : ℝ => x + s • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
    hline.continuousAt.eventually (hU.mem_nhds ht)
  have hF : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞ (F s) (annularOpen D) :=
    hnear.mono (fun s hs => hregular n (x + s • w) hs v)
  have hG : ContDiffOn ℝ ∞ G (annularOpen D) :=
    hregular (n + 1) (x + t • w) ht (Fin.cons w v)
  have hF₁ : ∀ᶠ s in 𝓝 t,
      ContDiffOn ℝ ∞ (fun p => (F s p).1) (annularOpen D) :=
    hF.mono (fun s hs => hs.fst)
  have hF₂ : ∀ᶠ s in 𝓝 t,
      ContDiffOn ℝ ∞ (fun p => (F s p).2) (annularOpen D) :=
    hF.mono (fun s hs => hs.snd)
  have hG₁ : ContDiffOn ℝ ∞ (fun p => (G p).1) (annularOpen D) := hG.fst
  have hG₂ : ContDiffOn ℝ ∞ (fun p => (G p).2) (annularOpen D) := hG.snd
  constructor
  · exact mixedJetHasDerivAt_comp_materialCoordinate (D := D) (T := T)
      (F := fun s p => (F s p).1) (G := fun p => (G p).1) (t := t) hT
      hF₁ hG₁ (fun a b p hp => (hderiv a b p hp).1)
  · exact mixedJetHasDerivAt_comp_materialCoordinate (D := D) (T := T)
      (F := fun s p => (F s p).2) (G := fun p => (G p).2) (t := t) hT
      hF₂ hG₂ (fun a b p hp => (hderiv a b p hp).2)

theorem N01Properties.cutoffStrip_or_eventually_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (χ : ℕ → ℝ → ℝ)
    (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    (l h : ℕ → ℝ)
    (hstripSupport : ∀ m, tsupport (deriv (χ m)) ⊆ Ioo (l m) (h m))
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    (∃ m, r ∈ Ioo (l m) (h m)) ∨
      ∀ᶠ s in 𝓝 r, ∀ m, deriv (χ m) s = 0 := by
  classical
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  by_cases hex : ∃ m, r ∈ Ioo (C.left m) (C.right m)
  · obtain ⟨m, hm⟩ := hex
    by_cases hactive : r ∈ tsupport (deriv (χ m))
    · exact Or.inl ⟨m, hstripSupport m hactive⟩
    · right
      have hzero : deriv (χ m) =ᶠ[𝓝 r] fun _ => 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hactive
      filter_upwards [isOpen_Ioo.mem_nhds hm, hzero] with s hs hsm
      intro i
      by_cases him : i = m
      · subst i
        exact hsm
      · by_contra hi
        exact Set.disjoint_left.mp (hC.2.2.1 i m him) (hsupp i hi) hs
  · right
    have hn : 0 ≤ deriv D.w r := by
      by_contra hn
      exact hex (hC.2.2.2.2.1 r hr (lt_of_not_ge hn))
    exact hN.cutoffs_deriv_eventually_zero_of_nonnegative χ hsupp hend hr hn

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

theorem N01Properties.returnCorrectionCoefficientScalarJets_eventually_zero
    {p : PolarPoint} (hzero : ∀ᶠ r in 𝓝 p.1, ∀ m, deriv (χ m) r = 0)
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) :
    hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc n x v
      =ᶠ[𝓝 p] fun _ => 0 := by
  let J : ∀ q : PolarPoint,
      SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
        (fun y : (StateDirections S × ℝ) × CircleSpace S =>
          returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C y.1) q y.2) :=
    hN.returnCorrectionCoefficient_pointTower hS hT hR j hcell χ hχrange hcutoff hdisc
  have hz := returnCorrectionCoefficientError_jets_eventually_zero
    (E := (StateDirections S × ℝ) × CircleSpace S)
    (D := D) (S := S) (C := C)
    (U := sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
    R χ (fun y => liftSectorParameter S C y.1) (fun y => y.2) J hzero n x hx v
  filter_upwards [hz] with q hq
  exact (hN.returnCorrectionCoefficientScalarJets_apply hS hT hR j hcell χ hχrange
    hcutoff hdisc n x v q).trans hq

theorem N01Properties.returnCorrectionCoefficientScalarJets_component_mixed_zero
    (Q : (ℝ × ℝ) →L[ℝ] ℝ)
    {p : PolarPoint} (hzero : ∀ᶠ r in 𝓝 p.1, ∀ m, deriv (χ m) r = 0)
    (a b n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) :
    mixedDerivative a b (fun q => Q
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff
        hdisc n x v q)) p = 0 := by
  have hz := hN.returnCorrectionCoefficientScalarJets_eventually_zero hS hT hR j hcell
    χ hχrange hcutoff hdisc hzero n x hx v
  have hq : (fun q => Q
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff
        hdisc n x v q)) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    filter_upwards [hz] with q hq
    simpa only [map_zero] using congrArg Q hq
  exact (mixedDerivative_congr_of_eventuallyEq hq a b).trans
    (by simp only [mixedDerivative, iteratedDeriv_const, ite_self])

variable
  (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
  (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
    χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (hstripSupport : ∀ m, tsupport (deriv (χ m)) ⊆ Ioo (l m) (h m))
  (hstripDisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

include hχ hsupp hend hl hh hstripSupport hstripDisc

theorem N01Properties.returnCorrectionCoefficientScalarJets_contDiffOn
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) :
    ContDiffOn ℝ ∞
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc n x v)
      (annularOpen D) := by
  exact coefficientSpatial_contDiffOn_of_cover
    (Ω := annularOpen D) (Z := fun p => ∀ᶠ r in 𝓝 p.1, ∀ m, deriv (χ m) r = 0)
    l h (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc n x v)
    (fun p hp => hN.cutoffStrip_or_eventually_zero χ hsupp hend l h hstripSupport hp.1)
    (fun m => hN.returnCorrectionCoefficientScalarJets_contDiffOn_strip hS hT hR
      j hcell χ hχrange hcutoff hdisc hχ m (l m) (h m) (hl m) (hh m)
      (fun z hz q hq => hstripDisc z hz m q hq) n x hx v)
    (fun p hzero => hN.returnCorrectionCoefficientScalarJets_eventually_zero
      hS hT hR j hcell χ hχrange hcutoff hdisc hzero n x hx v)

theorem N01Properties.returnCorrectionCoefficientScalarJets_component_mixed_hasDerivAt_line
    (Q : (ℝ × ℝ) →L[ℝ] ℝ) (a b n : ℕ)
    (x w : (StateDirections S × ℝ) × CircleSpace S)
    {t : ℝ} (ht : x + t • w ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    HasDerivAt
      (fun s => mixedDerivative a b (fun q => Q
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          n (x + s • w) v q)) p)
      (mixedDerivative a b (fun q => Q
        (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
          (n + 1) (x + t • w) (Fin.cons w v) q)) p) t := by
  exact coefficientSpatial_mixedLine_of_cover
    (E := (StateDirections S × ℝ) × CircleSpace S)
    (U := sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
    (Ω := annularOpen D) (Z := fun q => ∀ᶠ r in 𝓝 q.1, ∀ m, deriv (χ m) r = 0)
    (fun k y vs q => Q (hN.returnCorrectionCoefficientScalarJets
      hS hT hR j hcell χ hχrange hcutoff hdisc k y vs q)) l h
    ((sectorNeighborhood_isOpen S base ε ε).prod
      (isOpen_univ : IsOpen (univ : Set (CircleSpace S))))
    (fun q hq => hN.cutoffStrip_or_eventually_zero χ hsupp hend l h hstripSupport hq.1)
    (fun m a b k y w s hs vs q hq =>
      hN.returnCorrectionCoefficientScalarJets_component_mixed_hasDerivAt_line_strip
        hS hT hR j hcell χ hχrange hcutoff hdisc hχ m (l m) (h m) (hl m) (hh m)
        (fun z hz q hq => hstripDisc z hz m q hq) Q a b k y w hs vs ⟨hq, mem_univ q.2⟩)
    (fun q hzero a b k y hy vs =>
      hN.returnCorrectionCoefficientScalarJets_component_mixed_zero
        hS hT hR j hcell χ hχrange hcutoff hdisc Q hzero a b k y hy vs)
    a b n x w ht v hp

theorem N01Properties.returnCorrectionCoefficientScalarJets_mixed_hasDerivAt_line
    (a b n : ℕ) (x w : (StateDirections S × ℝ) × CircleSpace S)
    {t : ℝ} (ht : x + t • w ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
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
  ⟨hN.returnCorrectionCoefficientScalarJets_component_mixed_hasDerivAt_line
    hS hT hR j hcell χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc
    (ContinuousLinearMap.fst ℝ ℝ ℝ) a b n x w ht v hp,
    hN.returnCorrectionCoefficientScalarJets_component_mixed_hasDerivAt_line
    hS hT hR j hcell χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc
    (ContinuousLinearMap.snd ℝ ℝ ℝ) a b n x w ht v hp⟩

theorem N01Properties.returnCorrectionCoefficientScalarJets_mixedJetHasDerivAt
    (n : ℕ) (x w : (StateDirections S × ℝ) × CircleSpace S)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S)
    (t : ℝ) (ht : x + t • w ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    MixedJetHasDerivAt
      (fun s q => (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange
        hcutoff hdisc n (x + s • w) v (T.radius q.1, q.2)).1)
      (fun q => (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange
        hcutoff hdisc (n + 1) (x + t • w) (Fin.cons w v) (T.radius q.1, q.2)).1) t ∧
    MixedJetHasDerivAt
      (fun s q => (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange
        hcutoff hdisc n (x + s • w) v (T.radius q.1, q.2)).2)
      (fun q => (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange
        hcutoff hdisc (n + 1) (x + t • w) (Fin.cons w v) (T.radius q.1, q.2)).2) t := by
  let A : (k : ℕ) → ((StateDirections S × ℝ) × CircleSpace S) →
      (Fin k → (StateDirections S × ℝ) × CircleSpace S) → PolarPoint → ℝ × ℝ :=
    fun k y vs q => hN.returnCorrectionCoefficientScalarJets
      hS hT hR j hcell χ hχrange hcutoff hdisc k y vs q
  have hregular (k : ℕ) (y : (StateDirections S × ℝ) × CircleSpace S)
      (hy : y ∈ sectorNeighborhood S base ε ε ×ˢ univ)
      (vs : Fin k → (StateDirections S × ℝ) × CircleSpace S) :
      ContDiffOn ℝ ∞ (A k y vs) (annularOpen D) :=
    hN.returnCorrectionCoefficientScalarJets_contDiffOn hS hT hR j hcell χ hχrange
      hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc k y hy vs
  exact correctionCoefficient_materialLine_of_ordinary
    (E := (StateDirections S × ℝ) × CircleSpace S) (D := D) (T := T) hT
    (sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
    ((sectorNeighborhood_isOpen S base ε ε).prod
      (isOpen_univ : IsOpen (univ : Set (CircleSpace S))))
    A hregular n x w v t ht
    (fun a b p hp => hN.returnCorrectionCoefficientScalarJets_mixed_hasDerivAt_line
      hS hT hR j hcell χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh
      hstripSupport hstripDisc a b n x w ht v hp)

end ContinuousFlexibility.Statements
