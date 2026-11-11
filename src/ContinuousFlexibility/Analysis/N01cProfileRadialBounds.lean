import ContinuousFlexibility.Analysis.N01cDistributedRadialProducts
import ContinuousFlexibility.Analysis.N01cStateProfileProductBounds

/-!
# All radial orders of the actual profile parameter tower

Every bound is obtained from the actual mixed derivative identity.  The
finite Leibniz coefficient retains the original control majorants at their
assigned radial orders.  On the original N01b neighbourhood, the base state
is bounded by the reference-state level-zero seminorm plus its radius, and
the original denominator comparison bounds the exponential by two.

No control support is assigned to a material cell in this module.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

private abbrev radialBoundsStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] radialBoundsStateTopology

private abbrev radialBoundsStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] radialBoundsStateGroup

private abbrev radialBoundsStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] radialBoundsStateModule

private abbrev radialBoundsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (radialBoundsStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] radialBoundsStateSMul

theorem contDiffAt_stateProfileParameterExponent
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (x : AnnularState S) (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    ContDiffAt ℝ ∞ (fun s => x.2.1 * D.chi s + stateControlSum C x s) r :=
  (contDiffAt_const.mul hχ.contDiffAt).add
    ((contDiffOn_stateControlSum hC x).contDiffAt (isOpen_Ioo.mem_nhds hr))

/-- Every actual radial profile jet is bounded by the finite products of
its actual exponent jets and the original reference-profile jets. -/
theorem abs_iteratedDeriv_stateProfile_le_rawMajorant
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    |iteratedDeriv n (stateProfile D S C x) r| ≤
      Real.exp (x.2.1 * D.chi r + stateControlSum C x r) *
        scaledExponentialJetMajorant (fun a => |iteratedDeriv a D.w r|)
          (fun a => stateProfileExponentJetMajorant D T C hC a r hr)
          (stateGrading S 0 x) n :=
  abs_iteratedDeriv_mul_exp_le hD.2.2.1.1.contDiffAt
    (contDiffAt_stateProfileParameterExponent hC hχ x r hr)
    (fun a => stateProfileExponentJetMajorant D T C hC a r hr)
    (stateGrading S 0 x)
    (fun a => abs_iteratedDeriv_stateProfileExponent_le hS hT hRef hC hχ a r hr x) n

/-- The all-order raw estimate for the actual radial profile tower.
The finite coefficient retains the exact distribution of spatial orders;
the state direction factors have only the original level-zero grading. -/
theorem stateProfileRadialJetSmoothDirections_rawProductBound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (n k : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    (x : AnnularState S) (v : Fin k → AnnularState S) :
    |(stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ n r hr).D k x v| ≤
      Real.exp (x.2.1 * D.chi r + stateControlSum C x r) *
        profileParameterProductMajorant (fun a => |iteratedDeriv a D.w r|)
          (fun a => stateProfileExponentJetMajorant D T C hC a r hr)
          (stateGrading S 0 x) n k * ∏ i, stateGrading S 0 (v i) := by
  let W : ℕ → ℝ := fun a => |iteratedDeriv a D.w r|
  let P : ℕ → ℝ := fun a => stateProfileExponentJetMajorant D T C hC a r hr
  let q : ℝ := stateGrading S 0 x
  let e : ℝ := Real.exp (x.2.1 * D.chi r + stateControlSum C x r)
  let f : Fin (k + 1) → ℝ → ℝ :=
    Fin.cons (stateProfile D S C x)
      (fun i s => (v i).2.1 * D.chi s + stateControlSum C (v i) s)
  let M : Fin (k + 1) → ℕ → ℝ :=
    Fin.cons (fun j => e * scaledExponentialJetMajorant W P q j)
      (fun i j => P j * stateGrading S 0 (v i))
  have hf (i : Fin (k + 1)) : ContDiffAt ℝ ∞ (f i) r :=
    Fin.cases (motive := fun i : Fin (k + 1) => ContDiffAt ℝ ∞ (f i) r)
      ((contDiffOn_stateProfile hD hχ hC x).contDiffAt (isOpen_Ioo.mem_nhds hr))
      (fun i => contDiffAt_stateProfileParameterExponent hC hχ (v i) r hr) i
  have hM (i : Fin (k + 1)) (j : ℕ) : |iteratedDeriv j (f i) r| ≤ M i j :=
    Fin.cases (motive := fun i : Fin (k + 1) => |iteratedDeriv j (f i) r| ≤ M i j)
      (abs_iteratedDeriv_stateProfile_le_rawMajorant hS hT hRef hD hC hχ j r hr x)
      (fun i => abs_iteratedDeriv_stateProfileExponent_le hS hT hRef hC hχ j r hr (v i)) i
  have hprod : (fun s => ∏ i : Fin (k + 1), f i s) =
      (fun s => stateProfile D S C x s *
        ∏ i, ((v i).2.1 * D.chi s + stateControlSum C (v i) s)) := by
    funext s
    simp only [Fin.prod_univ_succ, f, Fin.cons_zero, Fin.cons_succ]
  have heq :
      (stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ n r hr).D k x v =
        iteratedDeriv n (fun s => ∏ i : Fin (k + 1), f i s) r :=
    (stateProfileRadialJetSmoothDirections_D_apply hS hT hRef hD hC hχ n k r hr x v).trans
      (congrArg (fun g : ℝ → ℝ => iteratedDeriv n g r) hprod.symm)
  have hb := abs_iteratedDeriv_finProduct_le_radialLeibniz k n f r hf M hM
  exact (congrArg abs heq).trans_le
    (hb.trans_eq (radialLeibniz_product_factorization W P q e n k
      (fun i => stateGrading S 0 (v i))))

/-- The original state neighbourhood bounds the actual base-state grading,
without changing its reference state or its radius. -/
theorem stateGrading_zero_le_reference_add_radius
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    stateGrading S 0 z.1 ≤ stateGrading S 0 C.referenceState + ε :=
  seminorm_le_reference_add_of_displacement_bound (stateGrading S 0) z.1 C.referenceState
    ((stateGrading_monotone S (Nat.zero_le base) _).trans hz.1.le)

/-- The exponential in the profile is bounded by the original N01b ratio
estimate, with the original reference profile positive on the core. -/
theorem n01PartB_stateProfileExponent_exp_le_two
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hD : RadialProfileGeometry D) (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    Real.exp (z.1.2.1 * D.chi r + stateControlSum C z.1 r) ≤ 2 := by
  have hw : 0 < D.w r := hD.2.2.2.2.1 r hr
  have hb : D.w r * Real.exp (z.1.2.1 * D.chi r + stateControlSum C z.1 r) ≤ D.w r * 2 :=
    ((le_abs_self (stateProfile D S C z.1 r)).trans
      (n01PartB_abs_stateProfile_le hD hS href hB hz r hr)).trans_eq (mul_comm 2 (D.w r))
  exact (mul_le_mul_left hw).mp hb

/-- All parameter orders and radial orders share the exact original
neighbourhood.  The finite coefficient is independent of z and v there
and retains every true Pj(r), including its original sampled weights. -/
theorem stateProfileRadialJetSmoothDirections_rawProductBound_on_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (hχ : ContDiff ℝ ∞ D.chi)
    (href : referenceStateConditions D S C) (hB : N01PartB D S C base ε)
    (n k : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (v : Fin k → AnnularState S) :
    |(stateProfileRadialJetSmoothDirections hS hT hRef hD hC hχ n r hr).D k z.1 v| ≤
      2 * profileParameterProductMajorant (fun a => |iteratedDeriv a D.w r|)
        (fun a => stateProfileExponentJetMajorant D T C hC a r hr)
        (stateGrading S 0 C.referenceState + ε) n k *
          ∏ i, stateGrading S 0 (v i) := by
  let W : ℕ → ℝ := fun a => |iteratedDeriv a D.w r|
  let P : ℕ → ℝ := fun a => stateProfileExponentJetMajorant D T C hC a r hr
  have hW (a : ℕ) : 0 ≤ W a := abs_nonneg _
  have hP (a : ℕ) : 0 ≤ P a := stateProfileExponentJetMajorant_nonneg hT hRef hC a r hr
  have hq : 0 ≤ stateGrading S 0 z.1 := apply_nonneg _ _
  have hcoef0 : 0 ≤ profileParameterProductMajorant W P (stateGrading S 0 z.1) n k :=
    profileParameterProductMajorant_nonneg W P _ hW hP hq n k
  have hcoef :
      profileParameterProductMajorant W P (stateGrading S 0 z.1) n k ≤
        profileParameterProductMajorant W P (stateGrading S 0 C.referenceState + ε) n k :=
    profileParameterProductMajorant_mono W P hW hP hq
      (stateGrading_zero_le_reference_add_radius hz) n k
  exact (stateProfileRadialJetSmoothDirections_rawProductBound
    hS hT hRef hD hC hχ n k r hr z.1 v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul (n01PartB_stateProfileExponent_exp_le_two hD hS href hB hz r hr)
          hcoef hcoef0 (by norm_num))
        (Finset.prod_nonneg (fun i _ => apply_nonneg (stateGrading S 0) (v i))))

end ContinuousFlexibility.Statements
