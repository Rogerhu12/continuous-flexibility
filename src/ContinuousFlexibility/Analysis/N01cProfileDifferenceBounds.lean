import ContinuousFlexibility.Analysis.N01cProfileRadialBounds
import ContinuousFlexibility.Analysis.N01cReferenceDifferenceBounds

/-!
# Actual radial profile differences from the same reference

The existing scalar first-jet segment estimate and the existing common
neighbourhood segment theorem apply directly to every actual radial
profile jet.  The coefficient keeps the original finite control majorants,
and one explicit state-displacement factor remains.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

private theorem reference_add_displacement {E : Type*} [AddCommGroup E]
    (reference x : E) : reference + (x - reference) = x := by
  abel

private abbrev differenceStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] differenceStateTopology

private abbrev differenceStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] differenceStateGroup

private abbrev differenceStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] differenceStateModule

private abbrev differenceStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (differenceStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] differenceStateSMul

/-- The difference of every actual radial jet has one explicit
level-zero displacement factor on the original common neighbourhood. -/
theorem stateProfileRadialJet_difference_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (href : referenceStateConditions D S C) (hB : N01PartB D S C base ε)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    |iteratedDeriv n (stateProfile D S C z.1) r -
        iteratedDeriv n (stateProfile D S C C.referenceState) r| ≤
      2 * profileParameterProductMajorant (fun a => |iteratedDeriv a D.w r|)
        (fun a => stateProfileExponentJetMajorant D T C hC a r hr)
        (stateGrading S 0 C.referenceState + ε) n 1 *
          stateGrading S 0 (z.1 - C.referenceState) := by
  letI : IsTopologicalAddGroup (AnnularState S) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S) := inferInstance
  let J := stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ n r hr
  have hestimate :
      |iteratedDeriv n (stateProfile D S C (C.referenceState + (z.1 - C.referenceState))) r -
          iteratedDeriv n (stateProfile D S C C.referenceState) r| ≤
      2 * profileParameterProductMajorant (fun a => |iteratedDeriv a D.w r|)
        (fun a => stateProfileExponentJetMajorant D T C hC a r hr)
        (stateGrading S 0 C.referenceState + ε) n 1 *
          stateGrading S 0 (z.1 - C.referenceState) := by
    apply smoothDirections_abs_sub_le_of_firstJet_bound J
      (x := C.referenceState) (d := z.1 - C.referenceState) (fun _ _ => mem_univ _)
    intro t ht
    have hsegment := stateNeighborhood_reference_segment S C hz ht
    have hb := stateProfileRadialJetSmoothDirections_rawProductBound_on_neighborhood
      hS hT hRef hD hC hχ href hB n 1 r hr hsegment
      (Fin.cons (z.1 - C.referenceState) Fin.elim0 : Fin 1 → AnnularState S)
    simpa only [Prod.fst_add, Prod.fst_smul, Prod.fst_sub,
      Fin.prod_univ_one, Fin.cons_zero] using hb
  have hendpoint :
      iteratedDeriv n (stateProfile D S C (C.referenceState + (z.1 - C.referenceState))) r =
        iteratedDeriv n (stateProfile D S C z.1) r :=
    congrArg (fun x : AnnularState S => iteratedDeriv n (stateProfile D S C x) r)
      (reference_add_displacement C.referenceState z.1)
  exact (congrArg (fun t : ℝ =>
    |t - iteratedDeriv n (stateProfile D S C C.referenceState) r|) hendpoint).symm.trans_le hestimate

/-- The same estimate concerns the derivative of the actual profile
difference, by the ordinary linearity of radial differentiation. -/
theorem iteratedDeriv_stateProfile_difference_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (href : referenceStateConditions D S C) (hB : N01PartB D S C base ε)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    |iteratedDeriv n (fun s => stateProfile D S C z.1 s -
        stateProfile D S C C.referenceState s) r| ≤
      2 * profileParameterProductMajorant (fun a => |iteratedDeriv a D.w r|)
        (fun a => stateProfileExponentJetMajorant D T C hC a r hr)
        (stateGrading S 0 C.referenceState + ε) n 1 *
          stateGrading S 0 (z.1 - C.referenceState) := by
  have hzjet : ContDiffAt ℝ n (stateProfile D S C z.1) r :=
    ((contDiffOn_stateProfile hD hχ hC z.1).contDiffAt (isOpen_Ioo.mem_nhds hr)).of_le
      (by simp)
  have hrefjet : ContDiffAt ℝ n (stateProfile D S C C.referenceState) r :=
    ((contDiffOn_stateProfile hD hχ hC C.referenceState).contDiffAt
      (isOpen_Ioo.mem_nhds hr)).of_le (by simp)
  exact (congrArg abs (iteratedDeriv_fun_sub hzjet hrefjet)).trans_le
    (stateProfileRadialJet_difference_bound hS hT hRef hD hC hχ href hB n r hr hz)

end ContinuousFlexibility.Statements
