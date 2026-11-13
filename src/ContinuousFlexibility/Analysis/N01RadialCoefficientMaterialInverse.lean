import ContinuousFlexibility.Analysis.ReturnCorrectionVelocityBounds
import ContinuousFlexibility.Analysis.N01ReferenceOpticalCollars
import ContinuousFlexibility.Analysis.MaterialSampleRadialPolynomial

/-!
# A material inverse bound for the actual radial coefficient

The existing N01 denominator ratios bound the radial coefficient below
by a fixed multiple of the same reference profile. The reference inverse
profile estimate extends to both component endpoints and retains the
actual containing material cell. N03 preserves this radial coefficient
exactly. No retained Morse witness or optical root lower is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

private theorem radialCoefficient_lower_of_ratios
    {w W Q d : ℝ} (hw : 0 < w) (hW : 0 < W)
    (hWw : (1 / 2 : ℝ) ≤ W / w) (hQW : (7 / 8 : ℝ) ≤ Q / W)
    (hd : (1 / 2 : ℝ) ≤ d) (hd' : d ≤ 3 / 2) :
    w / 16 ≤ Q / (d * Real.sqrt d) := by
  have hW' := (le_div_iff₀ hw).mp hWw
  have hQ' := (le_div_iff₀ hW).mp hQW
  have hQw : w / 4 ≤ Q := by nlinarith only [hW', hQ', hw.le]
  have hdpos : 0 < d := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hd
  have hsqrt : Real.sqrt d ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [hd']⟩
  have hden : d * Real.sqrt d ≤ 4 := by
    have h := mul_le_mul (show d ≤ 2 by linarith only [hd']) hsqrt
      (Real.sqrt_nonneg d) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    exact h
  apply (le_div_iff₀ (mul_pos hdpos (Real.sqrt_pos.mpr hdpos))).mpr
  calc
    (w / 16) * (d * Real.sqrt d) ≤ (w / 16) * 4 :=
      mul_le_mul_of_nonneg_left hden (div_nonneg hw.le (by norm_num))
    _ = w / 4 := by ring
    _ ≤ Q := hQw

/-- The actual N01 ratios give a lower bound on the full physical annulus,
including both endpoints of every negative component. -/
theorem N01Properties.originalRadialCoefficient_ge_sixteenth_profile
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    D.w p.1 / 16 ≤ (originalCoefficients D S C z).a p := by
  have hgeom : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hw : 0 < D.w p.1 := hgeom.2.2.2.2.1 p.1 hp.1
  have hW : 0 < stateProfile D S C z.1 p.1 := by
    change 0 < D.w p.1 * Real.exp _
    exact mul_pos hw (Real.exp_pos _)
  have hdata := hN
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, hcoeff, _⟩
  have hb := hcoeff z hz hsector p hp
  have h := radialCoefficient_lower_of_ratios hw hW
    hb.1 hb.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  change _ ≤ polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p
  unfold polarLinearA linearRadial polarScale inverseDThreeHalves
  simpa only [one_div, ← div_eq_mul_inv] using h

private theorem referenceProfile_inverse_closedComponent_bound
    {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ A : ℝ, 0 < A ∧ ∀ l h j,
      NegativeRadialComponent D l h → Ioo l h ⊆ D.cells j →
      ∀ r ∈ Icc l h, (D.w r)⁻¹ ≤ A * radialE (D.cellIndex j) ^ A := by
  obtain ⟨A, hA, hi⟩ := hD.inverse_first_jets_cell_bound
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hc : ContinuousOn (fun r => (D.w r)⁻¹) (radialCore D) :=
    hgeom.2.2.1.1.continuous.continuousOn.inv₀
      (fun r hr => (hgeom.2.2.2.2.1 r hr).ne')
  refine ⟨A, hA, ?_⟩
  intro l h j hcomp hhost r hr
  have hsub : Icc l h ⊆ radialCore D := fun x hx =>
    ⟨hcomp.1.trans_le hx.1, hx.2.trans_lt hcomp.2.2.1⟩
  have hclosure : ContinuousOn (fun x => (D.w x)⁻¹) (closure (Ioo l h)) := by
    rw [closure_Ioo hcomp.2.1.ne]
    exact hc.mono hsub
  apply le_on_closure (s := Ioo l h) (f := fun x => (D.w x)⁻¹)
    (g := fun _ => A * radialE (D.cellIndex j) ^ A) ?_ hclosure continuousOn_const
    (by simpa only [closure_Ioo hcomp.2.1.ne] using hr)
  intro x hx
  exact (le_abs_self _).trans
    ((le_add_of_nonneg_right (abs_nonneg _)).trans (hi j x (hhost hx)))

/-- One sampled material exponent bounds the actual inverse radial
coefficient on every closed negative component, for every genuine host. -/
theorem N01Properties.originalRadialCoefficient_inverse_component_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∀ p : PolarPoint, p.1 ∈ Icc (C.left m) (C.right m) →
        ((originalCoefficients D S C z).a p)⁻¹ ≤ K * T.E0 (T.sample j) ^ P := by
  obtain ⟨A, hA, hi⟩ := referenceProfile_inverse_closedComponent_bound hN.1.1
  obtain ⟨Q, P, hQ, hP, hsample⟩ :=
    materialSample_radialE_power_bound hT hN.1.1 (R := A) hA.le
  refine ⟨16 * (A * Q), P, mul_pos (by norm_num) (mul_pos hA hQ), hP, ?_⟩
  intro z hz hs m j hhost p hp
  have hcomp := n01Properties_negativeRadialComponent hN m
  have hpD : p ∈ annularOpen D :=
    ⟨⟨hcomp.1.trans_le hp.1, hp.2.trans_lt hcomp.2.2.1⟩, mem_univ _⟩
  have hw : 0 < D.w p.1 := hN.1.1.choose_spec.1.2.2.2.2.1 p.1 hpD.1
  have hcoef := hN.originalRadialCoefficient_ge_sixteenth_profile hz hs hpD
  have hinv : ((originalCoefficients D S C z).a p)⁻¹ ≤ 16 * (D.w p.1)⁻¹ := by
    have h := inv_anti₀ (div_pos hw (by norm_num : (0 : ℝ) < 16)) hcoef
    simpa only [inv_div, div_eq_mul_inv] using h
  calc
    _ ≤ 16 * (D.w p.1)⁻¹ := hinv
    _ ≤ 16 * (A * radialE (D.cellIndex j) ^ A) :=
      mul_le_mul_of_nonneg_left (hi _ _ j hcomp hhost p.1 hp) (by norm_num)
    _ ≤ 16 * (A * (Q * T.E0 (T.sample j) ^ P)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hsample j) hA.le)
        (by norm_num)
    _ = (16 * (A * Q)) * T.E0 (T.sample j) ^ P := by ring

/-- The actual N03 field inherits the same bound from its exact radial
coefficient identity, without changing the reference, spaces or returns. -/
theorem N03Properties.radialCoefficient_inverse_component_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (hL : N03Properties D T S C R L base ε) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∀ p : PolarPoint, p.1 ∈ Icc (C.left m) (C.right m) →
        ((L.coefficients z).a p)⁻¹ ≤ K * T.E0 (T.sample j) ^ P := by
  obtain ⟨K, P, hK, hP, hb⟩ := hN.originalRadialCoefficient_inverse_component_material_bound hT
  refine ⟨K, P, hK, hP, ?_⟩
  intro z hz hs m j hhost p hp
  rw [hL.1 z hz hs p]
  exact hb z hz hs m j hhost p hp

end ContinuousFlexibility.Statements
