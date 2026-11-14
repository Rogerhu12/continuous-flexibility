module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.MaterialSampleBounds
public import ContinuousFlexibility.Analysis.N01JetBounds

/-!
# Enlarging the coefficient envelope without changing the physical spaces

The envelope in `IsMaterialData` is positive but need not be at least one in
the middle of the annulus.  A smooth scalar modification makes it at least
one and leaves it unchanged wherever it is at least two.  The actual endpoint
model is larger than two, so all prescribed endpoint formulas are retained.
Only the bookkeeping envelope changes: physical and circle norms, sample
points, the state space and every geometric field are the same.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- A smooth majorant of the identity and of one on the positive half-line. -/
def materialEnvelopeMajorant (t : ℝ) : ℝ :=
  t + 1 - Real.smoothTransition (t - 1)

theorem contDiff_materialEnvelopeMajorant : ContDiff ℝ ∞ materialEnvelopeMajorant :=
  (contDiff_id.add contDiff_const).sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem le_materialEnvelopeMajorant (t : ℝ) : t ≤ materialEnvelopeMajorant t := by
  have h := Real.smoothTransition.le_one (t - 1)
  unfold materialEnvelopeMajorant
  linarith

theorem materialEnvelopeMajorant_le_add_one (t : ℝ) :
    materialEnvelopeMajorant t ≤ t + 1 := by
  exact sub_le_self _ (Real.smoothTransition.nonneg _)

theorem one_le_materialEnvelopeMajorant {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ materialEnvelopeMajorant t := by
  by_cases h : t ≤ 1
  · rw [materialEnvelopeMajorant,
      Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr h), sub_zero]
    exact le_add_of_nonneg_left ht
  · exact (le_of_not_ge h).trans (le_materialEnvelopeMajorant t)

theorem materialEnvelopeMajorant_eq_self {t : ℝ} (ht : 2 ≤ t) :
    materialEnvelopeMajorant t = t := by
  rw [materialEnvelopeMajorant,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t - 1)]
  ring

private theorem two_le_materialE0 {x : ℝ} (hx : 0 ≤ x) : 2 ≤ materialE0 x := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp : 1 ≤ materialE0Exponent x := by
    have hlog : 0 ≤ materialLogFactor x :=
      Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans
        (he.trans (le_add_of_nonneg_right hx)))
    exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hx _) hlog)
  exact he.trans (Real.exp_le_exp.mpr hexp)

private theorem materialEnvelopeMajorant_rpow_envelope
    {t M C A : ℝ} (ht : 0 < t) (hM : 1 ≤ M) (hC : 0 < C) (hA : 0 ≤ A)
    (hbound : t ^ A ≤ C * M) :
    materialEnvelopeMajorant t ^ A ≤ (C + (3 : ℝ) ^ A) * M := by
  have h3 : 0 ≤ (3 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) A
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  by_cases ht2 : 2 ≤ t
  · rw [materialEnvelopeMajorant_eq_self ht2]
    exact hbound.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h3) hM0)
  · have hη3 : materialEnvelopeMajorant t ≤ 3 :=
      (materialEnvelopeMajorant_le_add_one t).trans (by linarith)
    calc
      materialEnvelopeMajorant t ^ A ≤ (3 : ℝ) ^ A :=
        Real.rpow_le_rpow (zero_le_one.trans (one_le_materialEnvelopeMajorant ht.le)) hη3 hA
      _ ≤ (3 : ℝ) ^ A * M := by simpa using mul_le_mul_of_nonneg_left hM h3
      _ ≤ (C + (3 : ℝ) ^ A) * M :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) hM0

/-- Once the coefficient envelope is at least one, an independent multiplier
and exponent can be packaged in the single constant used by the frozen bounds. -/
theorem coefficientEnvelope_pack (C A : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 ≤ t → C * t ^ A ≤ B * t ^ B := by
  let B : ℝ := max 1 (max C A)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hCB : C ≤ B := (le_max_left C A).trans (le_max_right _ _)
  have hAB : A ≤ B := (le_max_right C A).trans (le_max_right _ _)
  refine ⟨B, hB, ?_⟩
  intro t ht
  exact mul_le_mul hCB (Real.rpow_le_rpow_of_exponent_le ht hAB)
    (Real.rpow_nonneg (zero_le_one.trans ht) _) hB.le

/-- Enlarge only the coefficient envelope; all norm-defining data are retained. -/
def enlargedMaterialData (T : MaterialData) : MaterialData :=
  { T with E0 := fun r => materialEnvelopeMajorant (T.E0 r) }

theorem enlargedMaterialData_E0 (T : MaterialData) (r : ℝ) :
    (enlargedMaterialData T).E0 r = materialEnvelopeMajorant (T.E0 r) := rfl

theorem le_enlargedMaterialData_E0 (T : MaterialData) (r : ℝ) :
    T.E0 r ≤ (enlargedMaterialData T).E0 r := le_materialEnvelopeMajorant _

theorem one_le_enlargedMaterialData_E0 {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    1 ≤ (enlargedMaterialData T).E0 r :=
  one_le_materialEnvelopeMajorant (hT.2.1 r hr).2.2.1.le

/-- The enlargement preserves the exact material specification, including
the same endpoint collars, sample points, and radial expansion coefficients. -/
theorem isMaterialData_enlargedMaterialData {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    IsMaterialData D (enlargedMaterialData T) := by
  have hcell : ∀ m, D.cells m ⊆ Ioo D.a D.b := by
    obtain ⟨_, hb⟩ := hD
    exact hb.2.1.2.2.2.1
  obtain ⟨hsmooth, hpositive, hderiv, hmono, hleft, hright, hradiusSmooth,
    hradiusRight, hradiusLeft, hradiusDeriv, hendpoint, henvelope, hheight,
    hlog, hexpansion, hsample, hwidths, hcomparison⟩ := hT
  refine ⟨?_, ?_, hderiv, hmono, hleft, hright, hradiusSmooth, hradiusRight,
    hradiusLeft, hradiusDeriv, ?_, ?_, hheight, hlog, ?_, hsample, ?_, ?_⟩
  · intro f hf
    simp only [enlargedMaterialData, mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact hsmooth _ (by simp)
    · exact hsmooth _ (by simp)
    · exact contDiff_materialEnvelopeMajorant.comp_contDiffOn (hsmooth _ (by simp))
    · exact hsmooth _ (by simp)
    · exact hsmooth _ (by simp)
  · intro r hr
    have hp := hpositive r hr
    exact ⟨hp.1, hp.2.1,
      zero_lt_one.trans_le (one_le_materialEnvelopeMajorant hp.2.2.1.le), hp.2.2.2⟩
  · obtain ⟨d0, δ, hd0, hδ, hδlt, hl, hr⟩ := hendpoint
    refine ⟨d0, δ, hd0, hδ, hδlt, ?_, ?_⟩
    · intro r hr
      obtain ⟨he, hH, hE, hM⟩ := hl r hr
      refine ⟨he, hH, ?_, hM⟩
      change materialEnvelopeMajorant (T.E0 r) = materialE0 (endpointX d0 (r - D.a))
      rw [hE]
      have hx : 0 ≤ endpointX d0 (r - D.a) := Real.sqrt_nonneg _
      exact materialEnvelopeMajorant_eq_self (two_le_materialE0 hx)
    · intro r hr'
      obtain ⟨he, hH, hE, hM⟩ := hr r hr'
      refine ⟨he, hH, ?_, hM⟩
      change materialEnvelopeMajorant (T.E0 r) = materialE0 (endpointX d0 (D.b - r))
      rw [hE]
      have hx : 0 ≤ endpointX d0 (D.b - r) := Real.sqrt_nonneg _
      exact materialEnvelopeMajorant_eq_self (two_le_materialE0 hx)
  · intro A
    by_cases hA : 0 ≤ A
    · obtain ⟨C, hC, hb⟩ := henvelope A
      refine ⟨C + (3 : ℝ) ^ A,
        add_pos_of_pos_of_nonneg hC (Real.rpow_nonneg (by norm_num) A), ?_⟩
      intro r hr
      exact materialEnvelopeMajorant_rpow_envelope (hpositive r hr).2.2.1
        (hpositive r hr).2.2.2 hC hA (hb r hr)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro r hr
      change materialEnvelopeMajorant (T.E0 r) ^ A ≤ 1 * T.M r
      rw [one_mul]
      exact (Real.rpow_le_one_of_one_le_of_nonpos
        (one_le_materialEnvelopeMajorant (hpositive r hr).2.2.1.le)
        (le_of_not_ge hA)).trans (hpositive r hr).2.2.2
  · intro n
    obtain ⟨c, hc, ⟨C, A, hC, hA, hb⟩, heq⟩ := hexpansion n
    refine ⟨c, hc, ⟨C, A, hC, hA, ?_⟩, heq⟩
    intro j r hr
    exact (hb j r hr).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hpositive r hr).2.2.1.le (le_materialEnvelopeMajorant _) hA) hC)
  · obtain ⟨widths, K, hK, hw, hdisjoint⟩ := hwidths
    refine ⟨widths, K, hK, ?_, hdisjoint⟩
    intro m
    obtain ⟨hwpos, hwlower, hwsub⟩ := hw m
    refine ⟨hwpos, ?_, hwsub⟩
    have hmem : T.sample m ∈ Ioo D.a D.b := hcell m (hsample m)
    have hspos : 0 < T.E0 (T.sample m) := (hpositive _ hmem).2.2.1
    have hp : materialEnvelopeMajorant (T.E0 (T.sample m)) ^ (-K) ≤
        T.E0 (T.sample m) ^ (-K) := by
      rw [Real.rpow_neg (zero_lt_one.trans_le (one_le_materialEnvelopeMajorant hspos.le)).le,
        Real.rpow_neg hspos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hspos K)
        (Real.rpow_le_rpow hspos.le (le_materialEnvelopeMajorant _) hK.le)
    exact (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hK.le)).trans hwlower
  · obtain ⟨C, A, hC, hA, hb⟩ := hcomparison
    refine ⟨C, A, hC, hA, ?_⟩
    intro m r hr
    obtain ⟨hindex, hleft, hright⟩ := hb m r hr
    refine ⟨hindex, ?_, ?_⟩
    · exact hleft.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hpositive r (hcell m hr)).2.2.1.le
          (le_materialEnvelopeMajorant _) hA) hC.le)
    · exact hright.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hpositive r (hcell m hr)).2.2.1.le
          (le_materialEnvelopeMajorant _) hA) hC.le)

/-- The actual spaces and their gradings do not use the bookkeeping envelope. -/
theorem isPhysicalSpaces_enlargedMaterialData {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (h : IsPhysicalSpaces D T S) :
    IsPhysicalSpaces D (enlargedMaterialData T) S := h

private theorem oneHighVariationWeight_nonneg
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x : E) {k : ℕ} (v : Fin k → E) :
    0 ≤ oneHighVariationWeight p base high x v := by
  classical
  unfold oneHighVariationWeight
  apply add_nonneg
  · exact mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
      (Finset.prod_nonneg fun _ _ => apply_nonneg _ _)
  · exact Finset.sum_nonneg fun _ _ => mul_nonneg (apply_nonneg _ _)
      (Finset.prod_nonneg fun _ _ => apply_nonneg _ _)

private theorem materialSample_factor_le_enlarged {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B ≤
      B * (enlargedMaterialData T).H ((enlargedMaterialData T).sample m) ^ (3 / 4 : ℝ) *
        (enlargedMaterialData T).E0 ((enlargedMaterialData T).sample m) ^ B := by
  have hp := hT.2.1 _ (materialSample_mem_interval hD hT m)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hp.2.2.1.le (le_materialEnvelopeMajorant _) hB)
    (mul_nonneg hB (Real.rpow_nonneg hp.2.1.le _))

private theorem enlarge_directional_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U : Set E} {f : E → ℝ} {p : ℕ → Seminorm ℝ E}
    (base high : ℕ) (x0 : E) (k : ℕ) {A A' w : ℝ} (hA : A ≤ A')
    (h : ∃ J : SmoothDirections U f, ∀ z ∈ U, ∀ v : Fin k → E,
      w * |J.D k z v| ≤ A * oneHighVariationWeight p base high (z - x0) v) :
    ∃ J : SmoothDirections U f, ∀ z ∈ U, ∀ v : Fin k → E,
      w * |J.D k z v| ≤ A' * oneHighVariationWeight p base high (z - x0) v := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J, fun z hz v => ?_⟩
  exact (hJ z hz v).trans (mul_le_mul_of_nonneg_right hA
    (oneHighVariationWeight_nonneg p base high (z - x0) v))

private theorem n01CoefficientJetBounds_enlargedMaterialData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : N01CoefficientJetBounds D T S C base loss ε) :
    N01CoefficientJetBounds D (enlargedMaterialData T) S C base loss ε := by
  intro k s
  obtain ⟨B, hB, hb⟩ := h k s
  refine ⟨B, hB, ?_⟩
  intro m i a b p hab hp
  simpa only [one_mul] using enlarge_directional_bound
    (p := pairGrading (stateGrading S) realGrading) base (s + loss)
    (C.referenceState, 0) k (w := 1)
    (materialSample_factor_le_enlarged hD hT hB.le m)
    (by simpa only [one_mul] using hb m i a b p hab hp)

private theorem n01FlowJetBounds_enlargedMaterialData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : N01FlowJetBounds T S C base loss ε) :
    N01FlowJetBounds (enlargedMaterialData T) S C base loss ε := by
  intro k
  obtain ⟨parameterLoss, horder⟩ := h k
  refine ⟨parameterLoss, ?_⟩
  intro s
  obtain ⟨B, hB, hb⟩ := horder s
  refine ⟨B, hB, ?_⟩
  intro m a b p hab hp
  exact enlarge_directional_bound
    (p := pairGrading (stateGrading S) realGrading) base (s + loss + parameterLoss)
    (C.referenceState, 0) k
    (materialSample_factor_le_enlarged hD hT hB.le (C.cell m))
    (hb m a b p hab hp)

/-- All genuine coefficient and ordinary-flow towers already supplied by N01
retain their constants and losses under the envelope enlargement. -/
theorem n01Properties_enlargedMaterialData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (h : N01Properties D T S C base loss ε) :
    N01Properties D (enlargedMaterialData T) S C base loss ε := by
  have hcoefficient := n01CoefficientJetBounds_of_properties h
  have hflowJets := n01FlowJetBounds_of_properties h
  obtain ⟨hD, hε, href, hcontrol, hcells, hcontrols, hflow, hleft,
    hinverse, hgeometry, hroots, _, _⟩ := h
  refine ⟨hD, hε, href, hcontrol, hcells, ?_, hflow, hleft,
    hinverse, hgeometry, hroots,
    n01CoefficientJetBounds_enlargedMaterialData hD.1 hT hcoefficient,
    n01FlowJetBounds_enlargedMaterialData hD.1 hT hflowJets⟩
  intro s
  obtain ⟨B, hB, hb⟩ := hcontrols s
  refine ⟨B, hB, ?_⟩
  intro m r hr
  have hp := hT.2.1 _ (materialSample_mem_interval hD.1 hT (C.cell m))
  exact (hb m r hr).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hp.2.2.1.le (le_materialEnvelopeMajorant _) hB.le) hB.le)

/-- The same actual cumulative construction works with the enlarged envelope. -/
theorem nonlinearPropertiesThrough03_enlargedMaterialData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε) :
    NonlinearPropertiesThrough03 D (enlargedMaterialData T) S C R L base loss ε :=
  ⟨⟨n01Properties_enlargedMaterialData hT h.1.1, h.1.2⟩, h.2⟩

end ContinuousFlexibility.Analysis
