module

public import ContinuousFlexibility.Analysis.N01cStateParameterJets
public import ContinuousFlexibility.Analysis.N01cFullNeighborhood
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Raw products for the actual controlled profile

The decoded control means have explicit level-zero seminorm bounds.
Every radial jet of the exponent is a finite linear combination of these
actual means and the actual scalar state coordinate.  Its majorant keeps
the original control derivatives and their original sample weights.

The actual profile tower then satisfies an all-parameter-order product
bound.  N01b controls its base-point profile factor on the same full state
neighbourhood.  No relation between a control's assigned cell and its
spatial support is assumed in this module.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

private theorem scalarCLMSum_apply {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (I : Finset ℕ) (a : ℕ → ℝ) (L : ℕ → E →L[ℝ] ℝ) (x : E) :
    (∑ m ∈ I, a m • L m) x = ∑ m ∈ I, a m * L m x := by
  simp only [sum_apply, smul_apply, smul_eq_mul]

private theorem scalarCLMSmulAdd_apply {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (a : ℝ) (L M : E →L[ℝ] ℝ) (x : E) :
    (a • L + M) x = a * L x + M x := by
  simp only [add_apply, smul_apply, smul_eq_mul]

private theorem scalarWeightedSum_bound (I : Finset ℕ) (a u w : ℕ → ℝ) (t : ℝ)
    (h : ∀ m ∈ I, |u m| ≤ w m * t) :
    |∑ m ∈ I, a m * u m| ≤ (∑ m ∈ I, |a m| * w m) * t := by
  calc
    |∑ m ∈ I, a m * u m| ≤ ∑ m ∈ I, |a m * u m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ I, |a m| * (w m * t) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h m hm) (abs_nonneg _)
    _ = (∑ m ∈ I, |a m| * w m) * t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      ring

private theorem scalarAffine_bound {a u v K t : ℝ}
    (hu : |u| ≤ t) (hv : |v| ≤ K * t) :
    |a * u + v| ≤ (|a| + K) * t := by
  calc
    |a * u + v| ≤ |a * u| + |v| := abs_add_le _ _
    _ ≤ |a| * t + K * t := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg _)) hv
    _ = (|a| + K) * t := (add_mul _ _ _).symm

private theorem scalarProduct_bound {k : ℕ} (a K : ℝ) (u p : Fin k → ℝ)
    (hu : ∀ i, |u i| ≤ K * p i) :
    |a * ∏ i, u i| ≤ |a| * K ^ k * ∏ i, p i := by
  rw [abs_mul, Finset.abs_prod]
  calc
    |a| * ∏ i, |u i| ≤ |a| * ∏ i, K * p i :=
      mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hu i)) (abs_nonneg _)
    _ = |a| * K ^ k * ∏ i, p i := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring

private theorem scaledExpLinearJets_comp_apply {E E' : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
    (a : ℝ) (L : E →L[ℝ] ℝ) (P : E' →L[ℝ] E)
    (k : ℕ) (x : E') (v : Fin k → E') :
    scaledExpLinearJets a (L.comp P) k x v =
      scaledExpLinearJets a L k (P x) (fun i => P (v i)) := by
  simp only [scaledExpLinearJets_apply, ContinuousLinearMap.comp_apply]


/-- The exact scalar coefficient in the decoded control-mean estimate. -/
def stateKappaSeminormWeight (T : MaterialData) (m : ℕ) : ℝ :=
  ((1 / Real.pi) * Real.sqrt Real.pi) * T.H (T.sample m) ^ (3 / 4 : ℝ)

theorem stateKappaSeminormWeight_nonneg
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) (m : ℕ) :
    0 ≤ stateKappaSeminormWeight T m := by
  obtain ⟨_, hbounds⟩ := hRef
  have hH : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hbounds.2.1 m)).2.1
  exact mul_nonneg
    (mul_nonneg (div_nonneg zero_le_one Real.pi_pos.le) (Real.sqrt_nonneg _))
    (Real.rpow_nonneg hH.le _)

/-- The control mean is bounded by the same fixed state order for every
component.  Its spatial weight remains attached to its own sample. -/
theorem abs_stateKappa_le_weight_mul_stateGrading
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (x : AnnularState S) (n m : ℕ) :
    |stateKappa S x m| ≤ stateKappaSeminormWeight T m * stateGrading S n x := by
  calc
    |stateKappa S x m| ≤
        (((1 / Real.pi) * Real.sqrt Real.pi) * stateGrading S n x) *
          T.H (T.sample m) ^ (3 / 4 : ℝ) :=
      abs_stateKappa_le_stateGrading_of_accumulatingProfile hS hT hRef x n m
    _ = stateKappaSeminormWeight T m * stateGrading S n x := by
      dsimp only [stateKappaSeminormWeight]
      ring

/-- The scalar profile parameter is one nonnegative summand of the
actual state grading. -/
theorem abs_stateNu_le_stateGrading (S : PhysicalSpacesData) (n : ℕ)
    (x : AnnularState S) : |x.2.1| ≤ stateGrading S n x := by
  have hh := apply_nonneg ((S.height (3 / 4 : ℝ)).grading n) x.1.1
  have hk := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.1
  have hc := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.2
  have hscalar := norm_nonneg x.1.2
  have h : ‖x.2.1‖ ≤ stateGrading S n x := by
    rw [stateGrading_apply]
    linarith
  simpa only [Real.norm_eq_abs] using h

/-- An explicit finite coefficient sum for the radial exponent jet.
The index set is chosen from actual local finiteness once at this radius. -/
def stateProfileExponentJetMajorant (D : ReferenceData) (T : MaterialData)
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (hC : controlGeometryConditions D S C) (n : ℕ) (r : ℝ)
    (hr : r ∈ Ioo D.a D.b) : ℝ :=
  |iteratedDeriv n D.chi r| +
    ∑ m ∈ stateControlLocalIndices hC r hr,
      |iteratedDeriv n (C.control m) r| * stateKappaSeminormWeight T m

theorem stateProfileExponentJetMajorant_nonneg
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hC : controlGeometryConditions D S C) (n : ℕ) (r : ℝ)
    (hr : r ∈ Ioo D.a D.b) :
    0 ≤ stateProfileExponentJetMajorant D T C hC n r hr := by
  apply add_nonneg (abs_nonneg _)
  exact Finset.sum_nonneg (fun m _ =>
    mul_nonneg (abs_nonneg _) (stateKappaSeminormWeight_nonneg hT hRef m))

/-- Every actual radial control jet is bounded by its explicit finite
coefficient sum times the level-zero state seminorm. -/
theorem abs_stateControlJetEvalCLM_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    |stateControlJetEvalCLM hS hT hRef hC n r hr x| ≤
      (∑ m ∈ stateControlLocalIndices hC r hr,
        |iteratedDeriv n (C.control m) r| * stateKappaSeminormWeight T m) *
          stateGrading S 0 x := by
  classical
  have heval : stateControlJetEvalCLM hS hT hRef hC n r hr x =
      ∑ m ∈ stateControlLocalIndices hC r hr,
        iteratedDeriv n (C.control m) r * stateKappa S x m :=
    (scalarCLMSum_apply (stateControlLocalIndices hC r hr)
      (fun m => iteratedDeriv n (C.control m) r) (stateKappaCLM hS hT hRef) x).trans
        (Finset.sum_congr rfl (fun m _ =>
          congrArg (fun t : ℝ => iteratedDeriv n (C.control m) r * t)
            (stateKappaCLM_apply hS hT hRef m x)))
  exact (congrArg abs heval).trans_le
    (scalarWeightedSum_bound (stateControlLocalIndices hC r hr)
      (fun m => iteratedDeriv n (C.control m) r) (fun m => stateKappa S x m)
      (stateKappaSeminormWeight T) (stateGrading S 0 x)
      (fun m _ => abs_stateKappa_le_weight_mul_stateGrading hS hT hRef x 0 m))

/-- The actual continuous-linear exponent jet has the explicit
level-zero bound, at every radial derivative order. -/
theorem abs_stateProfileExponentJetCLM_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    |stateProfileExponentJetCLM hS hT hRef hC n r hr x| ≤
      stateProfileExponentJetMajorant D T C hC n r hr * stateGrading S 0 x := by
  have heval : stateProfileExponentJetCLM hS hT hRef hC n r hr x =
      iteratedDeriv n D.chi r * x.2.1 + stateControlJetEvalCLM hS hT hRef hC n r hr x :=
    (scalarCLMSmulAdd_apply (iteratedDeriv n D.chi r) (stateNuCLM S)
      (stateControlJetEvalCLM hS hT hRef hC n r hr) x).trans
        (congrArg (fun t : ℝ => iteratedDeriv n D.chi r * t +
          stateControlJetEvalCLM hS hT hRef hC n r hr x) (stateNuCLM_apply S x))
  exact (congrArg abs heval).trans_le
    (scalarAffine_bound (abs_stateNu_le_stateGrading S 0 x)
      (abs_stateControlJetEvalCLM_le hS hT hRef hC n r hr x))

/-- The bound concerns the actual iterated radial derivative, through
the previously proved evaluation identity. -/
theorem abs_iteratedDeriv_stateProfileExponent_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (hχ : ContDiff ℝ ∞ D.chi) (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    (x : AnnularState S) :
    |iteratedDeriv n (fun s => x.2.1 * D.chi s + stateControlSum C x s) r| ≤
      stateProfileExponentJetMajorant D T C hC n r hr * stateGrading S 0 x :=
  (congrArg abs
    (stateProfileExponentJetCLM_apply hS hT hRef hC hχ n r hr x)).symm.trans_le
      (abs_stateProfileExponentJetCLM_le hS hT hRef hC n r hr x)

/-- The finite local zero jet is the same actual exponent as evaluation
over the active controls at the point. -/
theorem stateProfileExponentCLM_eq_zeroJet
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    stateProfileExponentCLM hS hT hRef hC r hr x =
      stateProfileExponentJetCLM hS hT hRef hC 0 r hr x := by
  have hcontrol : stateControlJetEvalCLM hS hT hRef hC 0 r hr x =
      stateControlSum C x r := by
    simpa only [iteratedDeriv_zero] using
      stateControlJetEvalCLM_apply hS hT hRef hC 0 r hr x
  have hzero : iteratedDeriv 0 D.chi r = D.chi r := by
    simp only [iteratedDeriv_zero]
  have hjet : stateProfileExponentJetCLM hS hT hRef hC 0 r hr x =
      D.chi r * x.2.1 + stateControlSum C x r := by
    exact (scalarCLMSmulAdd_apply (iteratedDeriv 0 D.chi r) (stateNuCLM S)
      (stateControlJetEvalCLM hS hT hRef hC 0 r hr) x).trans
        (congrArg₂ (· + ·)
          (congrArg₂ (· * ·) hzero (stateNuCLM_apply S x)) hcontrol)
  exact (stateProfileExponentCLM_apply hS hT hRef hC r hr x).trans
    ((congrArg (fun t : ℝ => t + stateControlSum C x r)
      (mul_comm x.2.1 (D.chi r))).trans hjet.symm)

theorem abs_stateProfileExponentCLM_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (x : AnnularState S) :
    |stateProfileExponentCLM hS hT hRef hC r hr x| ≤
      stateProfileExponentJetMajorant D T C hC 0 r hr * stateGrading S 0 x := by
  exact (congrArg abs (stateProfileExponentCLM_eq_zeroJet hS hT hRef hC r hr x)).trans_le
    (abs_stateProfileExponentJetCLM_le hS hT hRef hC 0 r hr x)

/-- All genuine parameter derivatives of the actual profile have a raw
product bound with fixed input order zero. -/
theorem stateProfileSmoothDirections_rawProductBound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (k : ℕ) (x : AnnularState S)
    (v : Fin k → AnnularState S) :
    |(stateProfileSmoothDirections hS hT hRef hC r hr).D k x v| ≤
      |stateProfile D S C x r| * (stateProfileExponentJetMajorant D T C hC 0 r hr) ^ k *
        ∏ i, stateGrading S 0 (v i) := by
  exact (congrArg abs (stateProfileSmoothDirections_apply hS hT hRef hC r hr k x v)).trans_le
    (scalarProduct_bound (stateProfile D S C x r)
      (stateProfileExponentJetMajorant D T C hC 0 r hr)
      (fun i => stateProfileExponentCLM hS hT hRef hC r hr (v i))
      (fun i => stateGrading S 0 (v i))
      (fun i => abs_stateProfileExponentCLM_le hS hT hRef hC r hr (v i)))

/-- N01b controls the profile factor on the original full neighbourhood,
with its original base and radius. -/
theorem n01PartB_abs_stateProfile_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hD : RadialProfileGeometry D) (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    |stateProfile D S C z.1 r| ≤ 2 * D.w r := by
  have hp : (r, (0 : ℝ)) ∈ annularOpen D := ⟨hr, mem_univ _⟩
  have hb := n01PartB_denominator_bounds hS href hB hz hp
  have hw : 0 < D.w r := hD.2.2.2.2.1 r hr
  have hprofile : 0 < stateProfile D S C z.1 r :=
    (div_pos_iff_of_pos_right hw).mp (lt_of_lt_of_le (by norm_num) hb.1)
  exact (abs_of_pos hprofile).trans_le ((div_le_iff₀ hw).mp hb.2.1)

/-- The actual all-order profile jets satisfy the raw product bound on
that same N01b neighbourhood. -/
theorem stateProfileSmoothDirections_rawProductBound_on_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (href : referenceStateConditions D S C)
    (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (k : ℕ) (v : Fin k → AnnularState S) :
    |(stateProfileSmoothDirections hS hT hRef hC r hr).D k z.1 v| ≤
      (2 * D.w r) * (stateProfileExponentJetMajorant D T C hC 0 r hr) ^ k *
        ∏ i, stateGrading S 0 (v i) := by
  exact (stateProfileSmoothDirections_rawProductBound hS hT hRef hC r hr k z.1 v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (n01PartB_abs_stateProfile_le hD hS href hB hz r hr)
        (pow_nonneg (stateProfileExponentJetMajorant_nonneg hT hRef hC 0 r hr) _))
      (Finset.prod_nonneg (fun i _ => apply_nonneg _ _)))

/-- The actual profile viewed as a function of the joint state and real
parameter, with the explicit exponential tower. -/
def jointStateProfileSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    SmoothDirections univ
      (fun z : AnnularState S × ℝ => stateProfile D S C z.1 r) :=
  (smoothDirections_scaledExpLinear (D.w r)
    ((stateProfileExponentCLM hS hT hRef hC r hr).comp
      (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ))).congr (fun z _ => by
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst'] using
          (stateProfile_eq_exp_exponentCLM hS hT hRef hC r hr z.1).symm)

/-- The joint tower pulls every direction back to its actual state
component, so its derivative is the same one already estimated. -/
theorem jointStateProfileSmoothDirections_D_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (k : ℕ) (z : AnnularState S × ℝ)
    (v : Fin k → AnnularState S × ℝ) :
    (jointStateProfileSmoothDirections hS hT hRef hC r hr).D k z v =
      (stateProfileSmoothDirections hS hT hRef hC r hr).D k z.1 (fun i => (v i).1) := by
  change scaledExpLinearJets (D.w r)
    ((stateProfileExponentCLM hS hT hRef hC r hr).comp
      (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ)) k z v =
        scaledExpLinearJets (D.w r) (stateProfileExponentCLM hS hT hRef hC r hr)
          k z.1 (fun i => (v i).1)
  simpa only [ContinuousLinearMap.coe_fst'] using
    scaledExpLinearJets_comp_apply (D.w r) (stateProfileExponentCLM hS hT hRef hC r hr)
      (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ) k z v

theorem stateGrading_fst_le_jointStateGrading (S : PhysicalSpacesData)
    (n : ℕ) (z : AnnularState S × ℝ) :
    stateGrading S n z.1 ≤ pairGrading (stateGrading S) realGrading n z := by
  exact (le_add_of_nonneg_right (apply_nonneg (realGrading n) z.2)).trans_eq
    (pairGrading_apply (stateGrading S) realGrading n z).symm

/-- The raw product estimate uses the original joint grading, as in the
coefficient-family target.  Its direction order remains zero for every
parameter arity. -/
theorem jointStateProfileSmoothDirections_rawProductBound_on_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) (href : referenceStateConditions D S C)
    (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) (k : ℕ)
    (v : Fin k → AnnularState S × ℝ) :
    |(jointStateProfileSmoothDirections hS hT hRef hC r hr).D k z v| ≤
      (2 * D.w r) * (stateProfileExponentJetMajorant D T C hC 0 r hr) ^ k *
        ∏ i, pairGrading (stateGrading S) realGrading 0 (v i) := by
  have heq := congrArg abs (jointStateProfileSmoothDirections_D_apply hS hT hRef hC r hr k z v)
  have h := stateProfileSmoothDirections_rawProductBound_on_neighborhood
    hS hT hRef hD hC href hB hz r hr k (fun i => (v i).1)
  have hw : 0 < D.w r := hD.2.2.2.2.1 r hr
  have hmajorant := stateProfileExponentJetMajorant_nonneg hT hRef hC 0 r hr
  exact heq.trans_le (h.trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _)
      (fun i _ => stateGrading_fst_le_jointStateGrading S 0 (v i)))
    (mul_nonneg (mul_nonneg (by norm_num) hw.le) (pow_nonneg hmajorant _))))

end ContinuousFlexibility.Statements
