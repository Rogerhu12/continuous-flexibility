import ContinuousFlexibility.Analysis.FixedPositiveReferencePotentialMaterialJets
import ContinuousFlexibility.Analysis.WholePositiveReferencePotentialJets
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# The potential atom of one fixed positive reference family

The coordinate, height, original cell and normalized material data are
already selected. The same fields are used in the actual whole atlas and
in every derivative estimate. This proof selects numerical constants only.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped Topology ContDiff BigOperators

/-- Smoothness, periodicity and all spatial material bounds for the
actual potential atom, with the same fixed family as the principal atoms. -/
theorem n04WholeReferenceGauge_positive_potentialReferenceJets_fixedFamily
    {D₀ : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D₀ T) (hS : IsPhysicalSpaces D₀ T S)
    (hN : NonlinearPropertiesThrough03 D₀ T S C R L base loss ε)
    (hfield : N04bFieldRegularity D₀ S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D₀)
    {C0 : ℝ} (hC0 : 1 ≤ C0) (hfloor : ∀ j, 1 ≤ C0 * T.E0 (T.sample j))
    (hE0 : ∀ j, 1 ≤ T.E0 (T.sample j))
    (cell : N04PositiveComponent D₀.a D₀.b (deriv D₀.w) → ℕ)
    (Y H : N04PositiveComponent D₀.a D₀.b (deriv D₀.w) → ℝ → ℝ)
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hjets : ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv k (H i) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤
        A * (C0 * T.E0 (T.sample (cell i))) ^ A) :
    ∀ s : ℕ, ∃ BM : ℝ, 0 < BM ∧
      ∀ (e : ℕ ≃ N04WholePieceIndex D₀)
        (τ σ : (AnnularState S × ℝ) →
          N04PositiveComponent D₀.a D₀.b (deriv D₀.w) → PolarPoint → PolarPoint)
        (Q : (AnnularState S × ℝ) →
          N04PositiveComponent D₀.a D₀.b (deriv D₀.w) → PolarPoint → ℝ)
        (N : Set ℝ),
        (∀ i, τ (C.referenceState, 0) i = id ∧
          σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) →
      let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N
      ∀ m, V.positive m = true →
        ContDiffOn ℝ ∞ (atom D₀ T S C L V (C.referenceState, 0) m .potential) unitStrip ∧
        (∀ p ∈ unitStrip, atom D₀ T S C L V (C.referenceState, 0) m .potential
          (p + (0, Real.pi)) = atom D₀ T S C L V (C.referenceState, 0) m .potential p) ∧
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (atom D₀ T S C L V (C.referenceState, 0) m .potential) p| ≤
            BM * T.E0 (T.sample (V.cell m)) ^ BM := by
  classical
  have hDgeom := n04b_profileGeometry_of_through03 hN
  have hline : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hH (i) : ContDiff ℝ ∞ (H i) := by
    simpa only [Function.comp_def] using (hgeometry i).height_smooth.comp hline
  have hχ (i) : ContDiff ℝ ∞ (Function.invFun (Y i)) := by
    simpa only [positiveReferenceCylinderInverse, Function.comp_def] using
      (hgeometry i).inverse_smooth.fst.comp hline
  have hrange (i) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      Function.invFun (Y i) x ∈ Icc D₀.a D₀.b := by
    have hr : Function.invFun (Y i) x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) :=
      ((hgeometry i).inverse_maps_open (x := (x, 0)) ⟨hx, mem_univ _⟩).1
    have hcore := n04PositiveComponent_interval_subset
      (hDgeom.2.2.1.1.continuous_deriv (by simp)) i hr
    exact ⟨hcore.1.le, hcore.2.le⟩
  have hpotential := fixedPositiveReference_potential_material_jets hDgeom.2.2.1.1
    (fun i => C0 * T.E0 (T.sample (cell i))) (fun i => hfloor (cell i))
    Y H hH hχ hrange hjets
  choose M hM hactual using hpotential
  intro s
  let D : ℝ := 1 + ∑ k : Fin (s + 1), M k.val
  have hD : 1 ≤ D := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun k _ => zero_le_one.trans (hM k.val)))
  have hMD (a : ℕ) (ha : a ≤ s) : M a ≤ D :=
    (Finset.single_le_sum (f := fun k : Fin (s + 1) => M k.val)
      (fun k _ => zero_le_one.trans (hM k.val))
      (Finset.mem_univ (⟨a, by omega⟩ : Fin (s + 1)))).trans
        (le_add_of_nonneg_left zero_le_one)
  obtain ⟨BM, hBM, hpack⟩ := coefficientEnvelope_pack (D * C0 ^ D) D
  refine ⟨BM, hBM, ?_⟩
  intro e τ σ Q N href
  let A := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let V := n04WholeReferenceGaugeAtlasData C L A e cell ψ χ h₀ τ σ Q N
  dsimp only
  intro m hm
  cases hi : e m with
  | inl j =>
      have hnegative : V.positive m = false := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      exact False.elim (Bool.false_ne_true (hnegative.symm.trans hm))
  | inr i =>
      obtain ⟨hl, hr, _, _, _, hsample, _, _, _, _, _, _⟩ :=
        n04WholeReferenceGaugeAtlasData_positive_fields C L A e cell ψ χ h₀ τ σ Q N
          (C.referenceState, 0) m i hi
      have hl' : V.left m = 0 := hl
      have hr' : V.right m = 1 := hr
      have hunit (p : PolarPoint) : canonicalUnitPoint V m p = p := by
        change (V.left m + (V.right m - V.left m) * p.1, p.2) = p
        simp only [hl', hr', sub_zero, one_mul, zero_add, Prod.mk.eta]
      have hatom : atom D₀ T S C L V (C.referenceState, 0) m .potential =
          V.potential (C.referenceState, 0) m := by
        funext p
        change V.potential (C.referenceState, 0) m (canonicalUnitPoint V m p) = _
        rw [hunit]
      let f : ℝ → ℝ := fun t => -(H i (Function.invFun (Y i) t) *
        deriv ((fun r => D₀.w r * deriv (H i) r) ∘ Function.invFun (Y i)) t)
      have hflux : ContDiff ℝ ∞
          ((fun r => D₀.w r * deriv (H i) r) ∘ Function.invFun (Y i)) :=
        (hDgeom.2.2.1.1.mul (contDiff_infty_iff_deriv.mp (hH i)).2).comp (hχ i)
      have hf : ContDiff ℝ ∞ f :=
        (((hH i).comp (hχ i)).mul (contDiff_infty_iff_deriv.mp hflux).2).neg
      have hEq : EqOn (atom D₀ T S C L V (C.referenceState, 0) m .potential)
          (fun p : PolarPoint => f p.1) unitStrip := by
        intro p hp
        have hpCanonical : p ∈ canonicalOpen S V m := by
          simpa only [unitStrip, canonicalOpen, hl', hr'] using hp
        rw [hatom]
        exact (n04WholeReferenceGaugeAtlasData_positive_reference_potential_flux_germ
          hT hS hN hfield e₀ e cell Y H τ σ Q N m i hi (hgeometry i) (href i)
          hpCanonical).self_of_nhds
      have hmodel : ContDiffOn ℝ ∞ (fun p : PolarPoint => f p.1) unitStrip :=
        (hf.comp contDiff_fst).contDiffOn
      refine ⟨hmodel.congr (fun p hp => hEq hp), ?_, ?_⟩
      · intro p hp
        have hp' : p + (0, Real.pi) ∈ unitStrip := by
          refine ⟨?_, mem_univ _⟩
          change 0 < p.1 + 0 ∧ p.1 + 0 < 1
          simpa only [add_zero] using hp.1
        calc
          _ = f (p + (0, Real.pi)).1 := hEq hp'
          _ = f p.1 := by simp only [Prod.add_def, add_zero]
          _ = _ := (hEq hp).symm
      · intro p hp a b hab
        rw [mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) hEq a b hp,
          n08_mixedDerivative_radial, hsample]
        let t : ℝ := T.E0 (T.sample (cell i))
        let W : ℝ := C0 * t
        have ht : 1 ≤ t := hE0 (cell i)
        have hW : 1 ≤ W := hfloor (cell i)
        have hcost : M a * W ^ M a ≤ BM * t ^ BM := by
          calc
            _ ≤ D * W ^ D := mul_le_mul (hMD a (by omega))
              (Real.rpow_le_rpow_of_exponent_le hW (hMD a (by omega)))
              (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hD)
            _ = (D * C0 ^ D) * t ^ D := by
              dsimp only [W]
              rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans ht)]
              ring
            _ ≤ BM * t ^ BM := hpack t ht
        have hrhs : 0 ≤ BM * t ^ BM :=
          mul_nonneg hBM.le (Real.rpow_nonneg (zero_le_one.trans ht) _)
        by_cases hb : b = 0
        · rw [if_pos hb]
          exact (hactual a i p.1 hp.1).trans hcost
        · rw [if_neg hb, abs_zero]
          exact hrhs

end ContinuousFlexibility.Analysis
