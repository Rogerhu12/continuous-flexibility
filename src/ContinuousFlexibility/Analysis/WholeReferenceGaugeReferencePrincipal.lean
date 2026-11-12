import ContinuousFlexibility.Analysis.RadialReferencePotentialGerms
import ContinuousFlexibility.Analysis.WholePositiveReferencePrincipal
import ContinuousFlexibility.Analysis.WholeReferenceGaugeReferenceRadial
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasPrincipalDensity

/-!
# Qualitative reference principal fields on every actual whole piece

The negative fields retain their genuine Airy density. Their radial
reference chart and height force the physical mixed coefficient to be
zero, so the potential is radial by actual local differentiation. The
positive fields use the scalar formulas for the same chosen Y and H.
This proves the qualitative first clause of ReferencePrincipal on the
same atlas, independently of its remaining uniform endpoint lower bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem negative_reference_qualitative_of_radial_density
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hradial : CanonicalGeometry.ReferenceRadial S C K)
    (A : SymmetricCoefficients) (w : ℝ → ℝ) (m : ℕ)
    (ha : ∀ q ∈ referencePhysicalPieceOpen S K m, A.a q = w q.1)
    (hunit : ∀ q ∈ referencePhysicalPieceOpen S K m,
      (coordinatePrincipalDensity A (K.chart (C.referenceState, 0) m)
        (K.height (C.referenceState, 0) m)).a q = 1 ∧
      (coordinatePrincipalDensity A (K.chart (C.referenceState, 0) m)
        (K.height (C.referenceState, 0) m)).b q = 0 ∧
      (coordinatePrincipalDensity A (K.chart (C.referenceState, 0) m)
        (K.height (C.referenceState, 0) m)).c q =
          -(K.chart (C.referenceState, 0) m q).1)
    (hcoeff : K.coefficients (C.referenceState, 0) m =
      inverseChartPrincipalCoefficients A (K.chart (C.referenceState, 0) m)
        (K.inverseChart (C.referenceState, 0) m) (K.height (C.referenceState, 0) m))
    (hpotential : ∀ p, K.potential (C.referenceState, 0) m p =
      inverseChartPotential A (K.chart (C.referenceState, 0) m)
        (K.inverseChart (C.referenceState, 0) m) (K.height (C.referenceState, 0) m) p)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    let B := K.coefficients (C.referenceState, 0) m
    0 < B.a p ∧ B.b p = 0 ∧ B.a p = B.a (p.1, 0) ∧ B.c p = B.c (p.1, 0) ∧
      K.potential (C.referenceState, 0) m p =
        K.potential (C.referenceState, 0) m (p.1, 0) := by
  let F := K.chart (C.referenceState, 0) m
  let G := K.inverseChart (C.referenceState, 0) m
  let h := K.height (C.referenceState, 0) m
  have hcharts := hA.charts (C.referenceState, 0) href hsref m
  have hmap {q : PolarPoint} (hq : q ∈ canonicalOpen S K m) :
      G q ∈ referencePhysicalPieceOpen S K m := by
    rw [← hA.referenceDomain m]
    exact hcharts.2.1 hq
  have hF : ContDiffOn ℝ ∞ F
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ (univ : Set ℝ)) := by
    change ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
      (referencePhysicalPieceOpen S K m)
    rw [← hA.referenceDomain m]
    exact hcharts.2.2.2.2.1
  have hshape (q : PolarPoint) (hq : q ∈ referencePhysicalPieceOpen S K m) :
      F q = ((F (q.1, 0)).1, q.2) := (hradial.1 m q hq).1
  have hheight (q : PolarPoint) (hq : q ∈ referencePhysicalPieceOpen S K m) :
      h q = h (q.1, 0) := (hradial.1 m q hq).2
  have hb (q : PolarPoint) (hq : q ∈ referencePhysicalPieceOpen S K m) : A.b q = 0 :=
    physical_mixed_zero_of_radial_unit_density hF hshape hheight
      (fun x hx => ⟨(hunit x hx).1, (hunit x hx).2.1⟩) hq
  let P : ℝ → ℝ := fun r => h (r, 0) *
    deriv (fun t => w t * deriv (fun s => h (s, 0)) t) r /
      |deriv (fun t => (F (t, 0)).1) r|
  have hpot (q : PolarPoint) (hq : q ∈ canonicalOpen S K m) :
      K.potential (C.referenceState, 0) m q = P (G q).1 := by
    rw [hpotential q]
    exact inverseChartPotential_radial_formula_on_strip hF hshape hheight ha hb (hmap hq)
  have hprincipal (q : PolarPoint) (hq : q ∈ canonicalOpen S K m) :
      (K.coefficients (C.referenceState, 0) m).a q = 1 ∧
      (K.coefficients (C.referenceState, 0) m).b q = 0 ∧
      (K.coefficients (C.referenceState, 0) m).c q = -q.1 := by
    rw [hcoeff]
    simpa only [inverseChartPrincipalCoefficients, G, hcharts.2.2.2.1 q hq] using
      hunit (G q) (hmap hq)
  have hp₀ : (p.1, (0 : ℝ)) ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  have hr : (G p).1 = (G (p.1, 0)).1 := by
    have he := congrArg (fun q : PolarPoint => q.1) (hradial.2 m p hp)
    exact he
  have ha₀ := hprincipal p hp
  have ha₁ := hprincipal (p.1, 0) hp₀
  refine ⟨?_, ha₀.2.1, ha₀.1.trans ha₁.1.symm, ha₀.2.2.trans ha₁.2.2.symm, ?_⟩
  · rw [ha₀.1]
    exact zero_lt_one
  · exact (hpot p hp).trans ((congrArg P hr).trans (hpot (p.1, 0) hp₀).symm)

theorem n04WholeReferenceGaugeAtlasData_actual_referencePrincipal_qualitative
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base newBase loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) (hε' : 0 < ε')
    (href : ∀ i, τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hA : CanonicalGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N) newBase ε') :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell (fun i => positiveReferenceCylinderChart (Y i))
      (fun i => positiveReferenceCylinderInverse (Y i))
      (fun i p => H i p.1) τ σ Q N
    ∀ m p, p ∈ canonicalOpen S V m →
      let A := V.coefficients (C.referenceState, 0) m
      0 < A.a p ∧ A.b p = 0 ∧ A.a p = A.a (p.1, 0) ∧ A.c p = A.c (p.1, 0) ∧
        V.potential (C.referenceState, 0) m p =
          V.potential (C.referenceState, 0) m (p.1, 0) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  have hz₀ : z₀ ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ : stateSector S z₀.1 := hN.1.1.2.2.1.stateSector
  have hz₀' : z₀ ∈ stateNeighborhood S C newBase ε' :=
    reference_mem_stateNeighborhood S C newBase hε'
  have hradial := n04WholeReferenceGaugeAtlasData_actual_referenceRadial
    hT hS hN hfield e₀ e cell Y H τ σ Q N hε' href hA
  dsimp only
  intro m p hp
  cases hi : e m with
  | inr i =>
      have h := n04WholeReferenceGaugeAtlasData_positive_reference_qualitative
        hT hS hN hfield e₀ e cell Y H τ σ Q N m i hi (hgeometry i) (href i) hp
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  | inl j =>
      have hneg : V.positive m = false := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      have hunit (q : PolarPoint) (hq : q ∈ referencePhysicalPieceOpen S V m) :
          (coordinatePrincipalDensity (L.coefficients z₀) (V.chart z₀ m) (V.height z₀ m)).a q = 1 ∧
          (coordinatePrincipalDensity (L.coefficients z₀) (V.chart z₀ m) (V.height z₀ m)).b q = 0 ∧
          (coordinatePrincipalDensity (L.coefficients z₀) (V.chart z₀ m) (V.height z₀ m)).c q =
            -(V.chart z₀ m q).1 := by
        have hqV : q ∈ physicalPieceOpen S V z₀ m := by
          rw [hA.referenceDomain m]
          exact hq
        have hqW : q ∈ physicalPieceOpen S W z₀ m := hqV
        have hmW : W.positive m = false := hneg
        have h := n04WholeCanonicalAtlasData_actual_negativePrincipalDensity
          hT hS hN hfield e₀ e cell σ τ Q N hz₀ hs₀ m hmW q hqW
        simpa only [V, W, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, hi] using h
      have hf := n04WholeReferenceGaugeAtlasData_actual_operatorFields
        hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N z₀ m
      apply negative_reference_qualitative_of_radial_density hA hz₀' hs₀ hradial
        (L.coefficients z₀) D.w m _ hunit hf.1 _ hp
      · intro q _hq
        exact (hN.2.1 z₀ hz₀ hs₀ q).trans (hN.1.1.reference_coefficients q).1
      · intro q
        have hpot := hf.2 q
        change V.potential z₀ m q = (if V.positive m then -1 else (1 : ℝ)) *
          inverseChartPotential (L.coefficients z₀) (V.chart z₀ m)
            (V.inverseChart z₀ m) (V.height z₀ m) q at hpot
        simpa only [hneg, Bool.false_eq_true, ↓reduceIte, one_mul] using hpot

end ContinuousFlexibility.Analysis
