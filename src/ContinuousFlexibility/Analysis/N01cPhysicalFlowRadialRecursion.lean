import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition
import ContinuousFlexibility.Analysis.SpacesJetLimits
import ContinuousFlexibility.Blueprint.N01c.Statements

/-!
# Actual physical radial jets of the ordinary characteristic flow

The physical ODE gives every radial derivative through the same Lie
recursion. No derivative of the inverse cosine coordinate is used.
The resulting identity retains the angular derivative outside a
differential expression in the actual speed, evaluated on the actual
flow. It is the qualitative identity used by the quantitative lifting.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- The expression for the next radial jet along the physical flow. -/
def physicalFlowLieJet (λ : PolarPoint → ℝ) : ℕ → PolarPoint → ℝ
  | 0 => λ
  | n + 1 => fun p =>
      radialPartial (physicalFlowLieJet λ n) p +
        λ p * angularPartial (physicalFlowLieJet λ n) p

theorem contDiffOn_physicalFlowLieJet
    {Ω : Set PolarPoint} {λ : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hλ : ContDiffOn ℝ ∞ λ Ω) (n : ℕ) :
    ContDiffOn ℝ ∞ (physicalFlowLieJet λ n) Ω := by
  induction n with
  | zero => exact hλ
  | succ n ih =>
    have hr : ContDiffOn ℝ ∞ (radialPartial (physicalFlowLieJet λ n)) Ω :=
      (ih.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
    have hθ : ContDiffOn ℝ ∞ (angularPartial (physicalFlowLieJet λ n)) Ω :=
      (ih.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
    exact hr.add (hλ.mul hθ)

theorem contDiffOn_iteratedRadialPartial
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (n : ℕ) :
    ContDiffOn ℝ ∞ ((radialPartial^[n]) f) Ω := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (ih.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const

/-- Actual mixed derivatives of the iterated physical radial partial. -/
theorem mixedDerivative_iteratedRadialPartial
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (n a b : ℕ) {p : PolarPoint} (hp : p ∈ Ω) :
    mixedDerivative a b ((radialPartial^[n]) f) p =
      mixedDerivative (a + n) b f p := by
  induction n generalizing a with
  | zero => simp only [Function.iterate_zero_apply, Nat.add_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply',
      mixedDerivative_radialPartial hΩ (contDiffOn_iteratedRadialPartial hΩ hf n) a b hp]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a + 1)

section PhysicalODE

variable {I : Set ℝ} {λ Θ : PolarPoint → ℝ}
  (hI : IsOpen I)
  (hλ : ContDiffOn ℝ ∞ λ (I ×ˢ (univ : Set ℝ)))
  (hΘ : ContDiffOn ℝ ∞ Θ (I ×ˢ (univ : Set ℝ)))

include hI hΘ

/-- The classical one-variable ODE identifies the actual radial partial
of the same supplied flow. -/
theorem radialPartial_eq_of_physicalFlowODE
    (hODE : ∀ r ∈ I, ∀ θ : ℝ,
      HasDerivAt (fun s => Θ (s, θ)) (λ (r, Θ (r, θ))) r)
    {p : PolarPoint} (hp : p ∈ I ×ˢ (univ : Set ℝ)) :
    radialPartial Θ p = λ (p.1, Θ p) := by
  have hd := ((hΘ.contDiffAt ((hI.prod isOpen_univ).mem_nhds hp)).
    differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2))
  have hd' : HasDerivAt (fun r => Θ (r, p.2)) (radialPartial Θ p) p.1 := by
    simpa only [Function.comp_def, radialPartial, Prod.eta] using hd
  exact hd'.unique (hODE p.1 hp.1 p.2)

/-- Chain rule along the physical graph, with the actual ODE substituted
only after the coordinate differential has been evaluated. -/
theorem radialPartial_along_physicalFlow
    {F : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F (I ×ˢ (univ : Set ℝ)))
    (hODE : ∀ r ∈ I, ∀ θ : ℝ,
      HasDerivAt (fun s => Θ (s, θ)) (λ (r, Θ (r, θ))) r)
    {p : PolarPoint} (hp : p ∈ I ×ˢ (univ : Set ℝ)) :
    radialPartial (fun q => F (q.1, Θ q)) p =
      radialPartial F (p.1, Θ p) +
        λ (p.1, Θ p) * angularPartial F (p.1, Θ p) := by
  have hΩ : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have ht := (hΘ.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hf := (hF.contDiffAt (hΩ.mem_nhds ⟨hp.1, mem_univ _⟩)).
    differentiableAt (by simp)
  have hg := (hasFDerivAt_fst p).prodMk ht.hasFDerivAt
  have hd := hf.hasFDerivAt.comp p hg
  have he : (fun q => F (q.1, Θ q)) = F ∘ (fun q => (q.1, Θ q)) := by
    simp only [Function.comp_def]
  rw [he, radialPartial, hd.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.fst_apply]
  change fderiv ℝ F (p.1, Θ p) (1, radialPartial Θ p) = _
  rw [radialPartial_eq_of_physicalFlowODE hI hΘ hODE hp,
    spaces_fderiv_eq_planeDifferential, spacesPlaneDifferentialMap_apply]
  ring

include hλ

/-- The whole actual iterated radial derivative is given by the same
physical Lie expression on the entire open component. -/
theorem iteratedRadialPartial_physicalFlow_eq_lie
    (hODE : ∀ r ∈ I, ∀ θ : ℝ,
      HasDerivAt (fun s => Θ (s, θ)) (λ (r, Θ (r, θ))) r)
    (n : ℕ) :
    EqOn ((radialPartial^[n + 1]) Θ)
      (fun p => physicalFlowLieJet λ n (p.1, Θ p))
      (I ×ˢ (univ : Set ℝ)) := by
  have hΩ : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  induction n with
  | zero =>
    intro p hp
    simpa only [Nat.zero_add, Function.iterate_one, physicalFlowLieJet] using
      radialPartial_eq_of_physicalFlowODE hI hΘ hODE hp
  | succ n ih =>
    intro p hp
    rw [Function.iterate_succ_apply']
    have he : ((radialPartial^[n + 1]) Θ) =ᶠ[𝓝 p]
        (fun q => physicalFlowLieJet λ n (q.1, Θ q)) := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      exact ih hq
    have hr := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0))
      (he.fderiv_eq (𝕜 := ℝ))
    calc
      _ = radialPartial (fun q => physicalFlowLieJet λ n (q.1, Θ q)) p := hr
      _ = _ := radialPartial_along_physicalFlow hI hΘ
        (contDiffOn_physicalFlowLieJet hΩ hλ n) hODE hp

/-- Every positive physical radial order is reduced to an angular
derivative of a differential expression in the actual speed. -/
theorem mixedDerivative_physicalFlow_eq_lie
    (hODE : ∀ r ∈ I, ∀ θ : ℝ,
      HasDerivAt (fun s => Θ (s, θ)) (λ (r, Θ (r, θ))) r)
    (n b : ℕ) {p : PolarPoint} (hp : p ∈ I ×ˢ (univ : Set ℝ)) :
    mixedDerivative (n + 1) b Θ p =
      iteratedDeriv b
        (fun θ => physicalFlowLieJet λ n (p.1, Θ (p.1, θ))) p.2 := by
  have hΩ : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hleft := contDiffOn_iteratedRadialPartial hΩ hΘ (n + 1)
  have hright : ContDiffOn ℝ ∞
      (fun q => physicalFlowLieJet λ n (q.1, Θ q))
      (I ×ˢ (univ : Set ℝ)) :=
    (contDiffOn_physicalFlowLieJet hΩ hλ n).comp
      (contDiff_fst.contDiffOn.prodMk hΘ) (fun q hq => ⟨hq.1, mem_univ _⟩)
  have hm := mixedDerivative_iteratedRadialPartial hΩ hΘ (n + 1) 0 b hp
  have he := mixedDerivative_eq_of_eqOn hΩ hleft hright
    (iteratedRadialPartial_physicalFlow_eq_lie hI hλ hΘ hODE n) 0 b hp
  calc
    _ = mixedDerivative 0 b ((radialPartial^[n + 1]) Θ) p := by
      simpa only [Nat.zero_add] using hm.symm
    _ = mixedDerivative 0 b
        (fun q => physicalFlowLieJet λ n (q.1, Θ q)) p := he
    _ = _ := by simp only [mixedDerivative, iteratedDeriv_zero]

end PhysicalODE

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- The actual reference-subtracted family, with every positive radial
order represented in physical coordinates on its original component. -/
theorem ordinaryFlowFamily_eq_physicalLieDifference
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {U : Set (AnnularState S × ℝ)}
    (hFlow : ordinaryFlowConditions D S C U)
    (hλ : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞
      (minusCharacteristicSpeed (originalCoefficients D S C z))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hΘ : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞
      (fun q : PolarPoint => C.minusFlow z m q.1 q.2)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (href : (C.referenceState, (0 : ℝ)) ∈ U)
    {z : AnnularState S × ℝ} (hz : z ∈ U) (m n b : ℕ)
    {p : PolarPoint} (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ordinaryFlowFamily S C m (n + 1) b p z =
      iteratedDeriv b (fun θ =>
        physicalFlowLieJet (minusCharacteristicSpeed (originalCoefficients D S C z)) n
          (p.1, C.minusFlow z m p.1 θ)) p.2 -
      iteratedDeriv b (fun θ =>
        physicalFlowLieJet
          (minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0))) n
          (p.1, C.minusFlow (C.referenceState, 0) m p.1 θ)) p.2 := by
  have hΩ : IsOpen (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hpoint : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    ⟨hp, mem_univ _⟩
  unfold ordinaryFlowFamily
  rw [mixedDerivative_sub_of_contDiffOn hΩ (hΘ z hz m)
    (hΘ (C.referenceState, 0) href m) (n + 1) b hpoint]
  rw [mixedDerivative_physicalFlow_eq_lie isOpen_Ioo (hλ z hz m) (hΘ z hz m)
      (fun r hr θ => (hFlow z hz m θ).2.2.1 r hr) n b hpoint,
    mixedDerivative_physicalFlow_eq_lie isOpen_Ioo
      (hλ (C.referenceState, 0) href m) (hΘ (C.referenceState, 0) href m)
      (fun r hr θ => (hFlow (C.referenceState, 0) href m θ).2.2.1 r hr) n b hpoint]

end ContinuousFlexibility.Statements
