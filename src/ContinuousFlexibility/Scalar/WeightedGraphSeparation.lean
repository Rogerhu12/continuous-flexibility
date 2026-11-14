module

public import ContinuousFlexibility.Scalar.WeightedGraph
public import ContinuousFlexibility.Analysis.MaterialHeightRegularity
public import ContinuousFlexibility.Analysis.TameElementaryCalculus
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Separation, maximality, and closedness of the physical weak graph

Compact radial tests separate the actual smooth periodic source functions.
Consequently the weak graph has at most one output for each common height.
Integration by parts identifies that output with an actual decoded operator;
continuity of the realized linear operator then proves closedness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- Smooth periodic functions are determined by the compact radial test
pairing. The proof tests against `ρ(r) f(r,θ)` and first shows that the
angular square integral is zero at each interior radius. -/
theorem eq_zero_of_physical_scalar_test_pairing
    (D : ReferenceData) (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfp : Function.Periodic f (0, Real.pi))
    (hoff : ∀ p, p ∉ annularOpen D → f p = 0)
    (hpair : ∀ φ : PolarPoint → ℝ, IsPhysicalScalarTest D φ →
      scalarAnnularIntegral D (fun p => f p * φ p) = 0) : f = 0 := by
  let G (r : ℝ) : ℝ := ∫ θ in (0 : ℝ)..Real.pi, f (r, θ) ^ 2
  have hG : Continuous G :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => f (r, θ) ^ 2)
      (by
        simpa only [Function.comp_def, Function.uncurry] using!
          (continuous_pow 2).comp hf.continuous) 0 Real.pi
  have hGa : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo D.a D.b → G r = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hG.continuousOn.locallyIntegrableOn measurableSet_Ioo)
    intro ρ hρ hc hs
    let φ (p : PolarPoint) : ℝ := ρ p.1 * f p
    have hφ : IsPhysicalScalarTest D φ := by
      refine ⟨(hρ.comp contDiff_fst).mul hf, ?_, tsupport ρ, hc, hs, ?_⟩
      · intro p
        change ρ (p.1 + 0) * f (p + (0, Real.pi)) = ρ p.1 * f p
        rw [add_zero, hfp p]
      · intro r hr θ
        change ρ r * f (r, θ) = 0
        rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]
    have hz : (∫ r in D.a..D.b, ρ r * G r) = 0 := by
      calc
        _ = scalarAnnularIntegral D (fun p => f p * φ p) := by
          unfold scalarAnnularIntegral G
          apply intervalIntegral.integral_congr
          intro r _
          dsimp only
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro θ _
          dsimp [φ]
          ring
        _ = 0 := hpair φ hφ
    have he : (∫ r, ρ r * G r) = ∫ r in D.a..D.b, ρ r * G r := by
      rw [intervalIntegral.integral_of_le hab]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro r hr
      have hρzero : ρ r = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hr ⟨(hs h).1, (hs h).2.le⟩)
      rw [hρzero, zero_mul]
    simpa only [smul_eq_mul] using he.trans hz
  have hGzero : EqOn G (fun _ => 0) (Ioo D.a D.b) :=
    Measure.eqOn_Ioo_of_ae_eq (volume : Measure ℝ)
      ((ae_restrict_iff' measurableSet_Ioo).mpr hGa)
      hG.continuousOn continuous_const.continuousOn
  have hzero (r : ℝ) (hr : r ∈ Ioo D.a D.b) (θ : ℝ) : f (r, θ) = 0 := by
    have hslice : Continuous (fun t : ℝ => f (r, t)) :=
      hf.continuous.comp (continuous_const.prodMk continuous_id)
    have hsquare : Continuous (fun t : ℝ => f (r, t) ^ 2) := hslice.pow 2
    have hae : (fun t : ℝ => f (r, t) ^ 2) =ᵐ[volume.restrict (Ioc 0 Real.pi)] 0 :=
      (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae Real.pi_pos.le
        (Filter.Eventually.of_forall fun t => sq_nonneg (f (r, t)))
        (hsquare.intervalIntegrable 0 Real.pi)).mp (hGzero hr)
    have hsqzero : EqOn (fun t : ℝ => f (r, t) ^ 2) (fun _ => 0) (Ioc 0 Real.pi) :=
      Measure.eqOn_Ioc_of_ae_eq (volume : Measure ℝ) hae
        hsquare.continuousOn continuous_const.continuousOn
    have hp : Function.Periodic (fun t : ℝ => f (r, t)) Real.pi := by
      intro t
      simpa only [Prod.mk_add_mk, add_zero] using hfp (r, t)
    obtain ⟨t, ht, he⟩ := hp.exists_mem_Ioc Real.pi_pos θ 0
    have ht' : t ∈ Ioc (0 : ℝ) Real.pi := by simpa only [zero_add] using ht
    exact he.trans (sq_eq_zero_iff.mp (hsqzero ht'))
  funext p
  by_cases hp : p ∈ annularOpen D
  · exact hzero p.1 hp.1 p.2
  · exact hoff p hp

/-- For a fixed height the actual weak distribution graph has a unique
output. This does not assume any realization or continuity of the operator. -/
theorem physicalScalarWeakGraph_right_unique
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (hab : D.a ≤ D.b)
    {x : ScalarWeightedState S} {u : ScalarCommonHeight S}
    {f g : ScalarHeightSpace S}
    (hf : (u, f) ∈ PhysicalScalarWeakGraph D S x)
    (hg : (u, g) ∈ PhysicalScalarWeakGraph D S x) : f = g := by
  have hβ : (0 : ℝ) < scalarBeta := by norm_num [scalarBeta]
  have hfs := (physical_height_contDiff_and_flatJets hT hS hβ f).1
  have hgs := (physical_height_contDiff_and_flatJets hT hS hβ g).1
  have hδ := (hS.1 scalarBeta).2.2.2.1 (f - g)
  have hδs := (physical_height_contDiff_and_flatJets hT hS hβ (f - g)).1
  have hz : (S.height scalarBeta).decode (f - g) = 0 := by
    apply eq_zero_of_physical_scalar_test_pairing D hab hδs hδ.2.2.1 hδ.2.2.2.1
    intro φ hφ
    have he : (fun p => (S.height scalarBeta).decode (f - g) p * φ p) =
        (fun p => (S.height scalarBeta).decode f p * φ p -
          (S.height scalarBeta).decode g p * φ p) := by
      funext p
      simp only [map_sub, Pi.sub_apply, sub_mul]
    rw [he, scalarAnnularIntegral_sub D
      (f := fun p => (S.height scalarBeta).decode f p * φ p)
      (g := fun p => (S.height scalarBeta).decode g p * φ p)
      (hfs.continuous.mul hφ.1.continuous)
      (hgs.continuous.mul hφ.1.continuous)]
    exact sub_eq_zero.mpr ((hf φ hφ).trans (hg φ hφ).symm)
  apply sub_eq_zero.mp
  apply (hS.1 scalarBeta).2.2.2.2.2.1
  rw [hz, map_zero]

private theorem weightedGraph_commonHeight_periodic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (u : ScalarCommonHeight S) :
    Function.Periodic (scalarCommonHeightDecode S u) (0, Real.pi) := by
  have hp := ((hS.1 scalarBeta).2.2.2.1 u.1).2.2.1
  intro p
  simp only [scalarCommonHeightDecode, hp p, Prod.fst_add, add_zero]

/-- The maximal weak graph on the common smooth weighted domain equals
the graph of any actual decoded realization of the corrected operator. -/
theorem physicalScalarWeakGraph_eq_graph
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (hab : D.a ≤ D.b)
    (x : ScalarWeightedState S)
    (hA : ContDiff ℝ ∞ (scalarStateA D S x))
    (hB : ContDiff ℝ ∞ (scalarStateB D S x))
    (hC : ContDiff ℝ ∞ (scalarStateCorrectedC D S x))
    (hBp : Function.Periodic (scalarStateB D S x) (0, Real.pi))
    (hCp : Function.Periodic (scalarStateCorrectedC D S x) (0, Real.pi))
    (L : ScalarCommonHeight S → ScalarHeightSpace S)
    (hL : ∀ u p, (S.height scalarBeta).decode (L u) p = scalarStateOperator D S x u p) :
    PhysicalScalarWeakGraph D S x = {z | z.2 = L z.1} := by
  have hmem (u : ScalarCommonHeight S) : (u, L u) ∈ PhysicalScalarWeakGraph D S x := by
    apply mem_physicalScalarWeakGraph_of_decode_operator D S x u (L u) hA hB hC
    · exact physical_height_with_cutoff_contDiff hT hS
        (by norm_num [scalarBeta] : (0 : ℝ) < scalarBeta) u.1 u.2
    · exact hBp
    · exact hCp
    · exact weightedGraph_commonHeight_periodic hS u
    · exact hL u
  ext z
  constructor
  · intro hz
    exact physicalScalarWeakGraph_right_unique hT hS hab hz (hmem z.1)
  · intro hz
    change z.2 = L z.1 at hz
    rcases z with ⟨u, f⟩
    dsimp only at hz
    rw [hz]
    exact hmem u

/-- Closedness, full common-height domain, and graph identification are
consequences of the actual decode equation and continuity of its realization. -/
theorem physicalScalarWeakGraph_closed_realization
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (hab : D.a ≤ D.b)
    (x : ScalarWeightedState S)
    (hA : ContDiff ℝ ∞ (scalarStateA D S x))
    (hB : ContDiff ℝ ∞ (scalarStateB D S x))
    (hC : ContDiff ℝ ∞ (scalarStateCorrectedC D S x))
    (hBp : Function.Periodic (scalarStateB D S x) (0, Real.pi))
    (hCp : Function.Periodic (scalarStateCorrectedC D S x) (0, Real.pi))
    (L : ScalarCommonHeight S → ScalarHeightSpace S) (hLc : Continuous L)
    (hL : ∀ u p, (S.height scalarBeta).decode (L u) p = scalarStateOperator D S x u p) :
    IsClosed (PhysicalScalarWeakGraph D S x) ∧
      (∀ u, ∃ f, (u, f) ∈ PhysicalScalarWeakGraph D S x) ∧
      ∀ u f, (u, f) ∈ PhysicalScalarWeakGraph D S x ↔ f = L u := by
  rw [physicalScalarWeakGraph_eq_graph hT hS hab x hA hB hC hBp hCp L hL]
  exact ⟨isClosed_eq continuous_snd (hLc.comp continuous_fst),
    fun u => ⟨L u, rfl⟩, fun _ _ => Iff.rfl⟩

/-- The joint tame tower supplies ordinary continuity in the common-height
variable at every fixed state in its domain. -/
theorem continuous_weightedScalar_linear_of_smoothTameOn
    (S : PhysicalSpacesData) (W : WeightedScalarData S) {U : Set (ScalarWeightedState S)}
    (h : SmoothTameOn (pairGrading (scalarStateGrading S) (scalarCommonHeightGrading S))
      (scalarHeightGrading S) (U ×ˢ univ)
      (fun z : ScalarWeightedState S × ScalarCommonHeight S => W.linear z.1 z.2))
    {x : ScalarWeightedState S} (hx : x ∈ U) : Continuous (W.linear x) := by
  obtain ⟨J, _⟩ := h
  apply continuousOn_univ.mp
  exact J.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun u _ => ⟨hx, mem_univ u⟩)

private theorem weightedGraph_stateHeight_periodic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    Function.Periodic (scalarStateHeight D S x) (0, Real.pi) := by
  have hp := weightedGraph_commonHeight_periodic hS (x.1.1.2, x.1.2)
  intro p
  change scalarStatePrimitive D S x (p.1 + 0) +
      x.2 * scalarCommonHeightDecode S (x.1.1.2, x.1.2) (p + (0, Real.pi)) =
    scalarStatePrimitive D S x p.1 + x.2 * scalarCommonHeightDecode S (x.1.1.2, x.1.2) p
  rw [add_zero, hp p]

/-- The entire graph clause of `IsWeightedS05` follows from its actual
coefficient smoothness, its decoded realization, and its joint tame tower.
No further weak-solution existence or maximality hypothesis is needed. -/
theorem weightedScalar_weakGraph_clause
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (W : WeightedScalarData S) (U : Set (ScalarWeightedState S))
    (hcoeff : ∀ x ∈ U,
      ContDiff ℝ ∞ (scalarStateA D S x) ∧ ContDiff ℝ ∞ (scalarStateB D S x) ∧
        ContDiff ℝ ∞ (scalarStateCorrectedC D S x))
    (hdecode : ∀ x ∈ U, ∀ u p,
      (S.height scalarBeta).decode (W.linear x u) p = scalarStateOperator D S x u p)
    (htame : SmoothTameOn (pairGrading (scalarStateGrading S) (scalarCommonHeightGrading S))
      (scalarHeightGrading S) (U ×ˢ univ)
      (fun z : ScalarWeightedState S × ScalarCommonHeight S => W.linear z.1 z.2)) :
    ∀ x ∈ U, IsClosed (PhysicalScalarWeakGraph D S x) ∧
      (∀ u, ∃ f, (u, f) ∈ PhysicalScalarWeakGraph D S x) ∧
      ∀ u f, (u, f) ∈ PhysicalScalarWeakGraph D S x ↔ f = W.linear x u := by
  obtain ⟨_, hD⟩ := hD
  have hab : D.a ≤ D.b := hD.1.2.1.le
  intro x hx
  obtain ⟨hA, hB, hC⟩ := hcoeff x hx
  obtain ⟨_, hBp, hCp⟩ := periodic_heightCorrectedCoefficients
    (scalarStateProfile D S x) (weightedGraph_stateHeight_periodic hS x)
  exact physicalScalarWeakGraph_closed_realization hT hS hab x hA hB hC hBp hCp
    (W.linear x) (continuous_weightedScalar_linear_of_smoothTameOn S W htame hx) (hdecode x hx)

end ContinuousFlexibility.Statements
