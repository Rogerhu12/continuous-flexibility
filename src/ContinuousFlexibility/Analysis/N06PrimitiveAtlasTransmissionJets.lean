import ContinuousFlexibility.Statements.N06PrimitiveGeometryBridge
import ContinuousFlexibility.Analysis.N06ActualEndpointFirstJets
import ContinuousFlexibility.Analysis.N06AtlasTransmissionJets

/-!
# Primitive forward jets give the actual atlas transmission records

The primitive root matching identity already concerns the same actual
charts and heights on both sides. Removing its fixed normal alignments
gives the two `N06RootFirstJets` records with common boundary functions.
The endpoint labels and signs in that identity are independent of the
state, so the reference and current pairs have the same labels and signs.

The current closed geometry chooses the reversal flag of each piece.
Its boundary values identify the primitive endpoint labels with those
flags. No new atlas, inverse, material estimate, or weak equation is
assumed. Artificial cuts continue to use the original N04 cut law.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- The ordinary derivative of the actual aligned chart, evaluated on
one physical vector. This only differentiates the fixed affine alignment. -/
theorem n06_primitive_alignedChart_fderiv_apply
    {S : PhysicalSpacesData} {K : CanonicalData S}
    {z : AnnularState S × ℝ} {m : ℕ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ (K.chart z m) p)
    (endpoint orientation : ℝ) (v : PolarPoint) :
    fderiv ℝ (endpointAlignedChart K z m endpoint orientation) p v =
      (orientation * (fderiv ℝ (K.chart z m) p v).1,
        (fderiv ℝ (K.chart z m) p v).2) := by
  change fderiv ℝ (fun q =>
    (orientation * ((K.chart z m q).1 - endpoint), (K.chart z m q).2)) p v = _
  have hd := ((hF.hasFDerivAt.fst.sub_const endpoint).const_mul orientation).prodMk
    hF.hasFDerivAt.snd
  simpa only [ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul] using
    congrArg (fun A : PolarPoint →L[ℝ] PolarPoint => A v) hd.fderiv

/-- Unaligning the genuine common first jets produces the precise two
records used by the finite H2 Green formula. The signs are the primitive
fixed orientations; the common scale and angular drift are actual jets. -/
theorem n06_primitive_rootPair_firstJets
    {S : PhysicalSpacesData} {K : CanonicalData S}
    {z : AnnularState S × ℝ} {i j : ℕ} {r ei ej si sj : ℝ}
    (hsi : si = 1 ∨ si = -1) (hsj : sj = 1 ∨ sj = -1)
    (hFi : ∀ θ, DifferentiableAt ℝ (K.chart z i) (r, θ))
    (hFj : ∀ θ, DifferentiableAt ℝ (K.chart z j) (r, θ))
    (hhi : ∀ θ, DifferentiableAt ℝ (K.height z i) (r, θ))
    (hhj : ∀ θ, DifferentiableAt ℝ (K.height z j) (r, θ))
    (hmatch : ∀ θ : ℝ,
      (endpointAlignedChart K z i ei si (r, θ)).1 = 0 ∧
      endpointAlignedChart K z i ei si (r, θ) =
        endpointAlignedChart K z j ej sj (r, θ) ∧
      fderiv ℝ (endpointAlignedChart K z i ei si) (r, θ) =
        fderiv ℝ (endpointAlignedChart K z j ej sj) (r, θ) ∧
      K.height z i (r, θ) = K.height z j (r, θ) ∧
      fderiv ℝ (K.height z i) (r, θ) = fderiv ℝ (K.height z j) (r, θ)) :
    ∃ β H ρ κ Hr : ℝ → ℝ,
      N06RootFirstJets (K.chart z i) (K.height z i) r ei si β H ρ κ Hr ∧
      N06RootFirstJets (K.chart z j) (K.height z j) r ej sj β H ρ κ Hr := by
  have hsi0 : si ≠ 0 := by rcases hsi with rfl | rfl <;> norm_num
  have hsj0 : sj ≠ 0 := by rcases hsj with rfl | rfl <;> norm_num
  have hvalueI (θ : ℝ) : (K.chart z i (r, θ)).1 = ei := by
    have he : si * ((K.chart z i (r, θ)).1 - ei) = 0 := (hmatch θ).1
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hsi0)
  have hvalueJ (θ : ℝ) : (K.chart z j (r, θ)).1 = ej := by
    have he : sj * ((K.chart z j (r, θ)).1 - ej) = 0 :=
      (congrArg Prod.fst (hmatch θ).2.1).symm.trans (hmatch θ).1
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hsj0)
  have hangle (θ : ℝ) : (K.chart z j (r, θ)).2 = (K.chart z i (r, θ)).2 :=
    (congrArg Prod.snd (hmatch θ).2.1).symm
  have hderiv (θ : ℝ) :
      (si * (fderiv ℝ (K.chart z i) (r, θ) (1, 0)).1,
        (fderiv ℝ (K.chart z i) (r, θ) (1, 0)).2) =
      (sj * (fderiv ℝ (K.chart z j) (r, θ) (1, 0)).1,
        (fderiv ℝ (K.chart z j) (r, θ) (1, 0)).2) := by
    have he := congrArg (fun A : PolarPoint →L[ℝ] PolarPoint => A (1, 0))
      (hmatch θ).2.2.1
    simpa only [n06_primitive_alignedChart_fderiv_apply (hFi θ),
      n06_primitive_alignedChart_fderiv_apply (hFj θ)] using he
  refine ⟨(fun θ => (K.chart z i (r, θ)).2), (fun θ => K.height z i (r, θ)),
    (fun θ => si * (fderiv ℝ (K.chart z i) (r, θ) (1, 0)).1),
    (fun θ => (fderiv ℝ (K.chart z i) (r, θ) (1, 0)).2),
    (fun θ => radialPartial (K.height z i) (r, θ)), ?_, ?_⟩
  · refine ⟨hFi, hhi, ?_, fun _ => rfl, ?_, fun _ => rfl⟩
    · intro θ
      exact Prod.ext (hvalueI θ) rfl
    · intro θ
      apply Prod.ext
      · rcases hsi with rfl | rfl <;> simp only [one_mul, neg_one_mul, neg_neg]
      · rfl
  · refine ⟨hFj, hhj, ?_, ?_, ?_, ?_⟩
    · intro θ
      exact Prod.ext (hvalueJ θ) (hangle θ)
    · intro θ
      exact (hmatch θ).2.2.2.1.symm
    · intro θ
      apply Prod.ext
      · have he := congrArg Prod.fst (hderiv θ)
        change si * (fderiv ℝ (K.chart z i) (r, θ) (1, 0)).1 =
          sj * (fderiv ℝ (K.chart z j) (r, θ) (1, 0)).1 at he
        rw [he]
        rcases hsj with rfl | rfl <;> simp only [one_mul, neg_one_mul, neg_neg]
      · exact (congrArg Prod.snd (hderiv θ)).symm
    · intro θ
      exact (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
        (hmatch θ).2.2.2.2).symm

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open CanonicalGeometry ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The primitive classification identifies every positive neighbor
interface as a root; the other alternative consists of two negative halves. -/
private theorem n06_primitive_positiveInterface_root
    (h04 : N04Properties D T S C L K base loss ε)
    (hclassification : PhysicalInterfaceClassification D K)
    {i j : ℕ} (hjoin : K.physicalRight i = K.physicalLeft j)
    (hpositive : K.positive i = true ∨ K.positive j = true) :
    i ≠ j ∧ deriv D.w (K.physicalRight i) = 0 := by
  have hij : i ≠ j := by
    intro he
    have hbad : K.physicalRight i = K.physicalLeft i := by simpa only [← he] using hjoin
    exact (h04.1.referenceBounds i).1.ne' hbad
  refine ⟨hij, ?_⟩
  rcases hclassification i j hij hjoin with hroot | ⟨n, hn⟩
  · exact hroot
  · have hcuts := h04.2.1.1.1 n
    have hi : K.positive i = false := by simpa only [hn] using hcuts.1
    have hj : K.positive j = false := by simpa only [hn] using hcuts.2.1
    rcases hpositive with h | h
    · exact False.elim (Bool.noConfusion (h.symm.trans hi))
    · exact False.elim (Bool.noConfusion (h.symm.trans hj))

/-- The original closed-domain regularity supplies the four actual
differentiability hypotheses at a true neighboring root circle. -/
private theorem n06_primitive_rootPair_differentiable
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {i j : ℕ} (hjoin : K.physicalRight i = K.physicalLeft j)
    (hpositive : K.positive i = true ∨ K.positive j = true) :
    (∀ θ, DifferentiableAt ℝ (K.chart z i) (K.physicalRight i, θ)) ∧
    (∀ θ, DifferentiableAt ℝ (K.chart z j) (K.physicalRight i, θ)) ∧
    (∀ θ, DifferentiableAt ℝ (K.height z i) (K.physicalRight i, θ)) ∧
    (∀ θ, DifferentiableAt ℝ (K.height z j) (K.physicalRight i, θ)) := by
  have htrue := n06_positive_adjacent_trueSides h04 hjoin hpositive
  have hi := (n06_trueEndpoint_current_geometry hC h04 hz hs i true htrue.1).1
  have hj := (n06_trueEndpoint_current_geometry hC h04 hz hs j false htrue.2).1
  have hbI := (h04.1.boundary z hz hs i).2.2.2.2.1
  have hbJ := (h04.1.boundary z hz hs j).2.2.2.2.1
  have hj' (θ : ℝ) : (K.physicalRight i, θ) ∈ physicalPieceClosed S K z j := by
    rw [hjoin]
    exact hj θ
  exact ⟨fun θ => (hbI _ (hi θ)).1.differentiableAt (by simp),
    fun θ => (hbJ _ (hj' θ)).1.differentiableAt (by simp),
    fun θ => (hbI _ (hi θ)).2.1.differentiableAt (by simp),
    fun θ => (hbJ _ (hj' θ)).2.1.differentiableAt (by simp)⟩

/-- The primitive transmission data constructs every actual atlas
first-jet record required by the existing finite Green chain, on the
original atlas. The reversal flags and all endpoint inverse circles
are conclusions. Reference radiality and any coefficient estimates are
unnecessary for this first-jet construction. -/
theorem n06_exists_atlasTransmissionJets_of_primitive
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (htransmission : TransmissionGeometry D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) :
    ∃ reverse : ℕ → Bool, N06AtlasTransmissionJets S C K z reverse := by
  classical
  obtain ⟨reverse, hendpoints, _⟩ := n06_exists_actualEndpoint_firstJets h01 h04 hz hs
  refine ⟨reverse, hendpoints, ?_⟩
  intro i j hjoin hpositive
  have hroot := n06_primitive_positiveInterface_root h04 htransmission.1 hjoin hpositive
  obtain ⟨ei, ej, si, sj, _hei, _hej, hsi, hsj, hmatching⟩ :=
    htransmission.2.1 i j hroot.1 hjoin hroot.2
  have hC : controlGeometryConditions D S C := h01.2.2.2.1
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsref : stateSector S C.referenceState := n05_referenceState_sector h01.2.2.1
  have hd := n06_primitive_rootPair_differentiable hC h04 hz hs hjoin hpositive
  have hdref := n06_primitive_rootPair_differentiable hC h04 href hsref hjoin hpositive
  obtain ⟨β, H, ρ, κ, Hr, Ji, Jj⟩ := n06_primitive_rootPair_firstJets hsi hsj
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 (hmatching z (Or.inr ⟨hz, hs⟩))
  obtain ⟨β₀, H₀, ρ₀, κ₀, Hr₀, Ji₀, Jj₀⟩ := n06_primitive_rootPair_firstJets hsi hsj
    hdref.1 hdref.2.1 hdref.2.2.1 hdref.2.2.2
      (hmatching (C.referenceState, 0) (Or.inl rfl))
  have htrue := n06_positive_adjacent_trueSides h04 hjoin hpositive
  obtain ⟨_, _, _, _, _, _, ⟨JeI⟩⟩ := hendpoints i true htrue.1
  obtain ⟨_, _, _, _, _, _, ⟨JeJ⟩⟩ := hendpoints j false htrue.2
  have hei : ei = n06Endpoint (K.left i) (K.right i)
      (if reverse i then !true else true) := by
    calc
      ei = (K.chart z i (K.physicalRight i, 0)).1 :=
        (congrArg Prod.fst (Ji.chart_value 0)).symm
      _ = _ := congrArg Prod.fst (JeI.chart_value 0)
  have hej : ej = n06Endpoint (K.left j) (K.right j)
      (if reverse j then !false else false) := by
    calc
      ej = (K.chart z j (K.physicalRight i, 0)).1 :=
        (congrArg Prod.fst (Jj.chart_value 0)).symm
      _ = (K.chart z j (K.physicalLeft j, 0)).1 := by rw [hjoin]
      _ = _ := congrArg Prod.fst (JeJ.chart_value 0)
  rw [hei] at Ji₀ Ji
  rw [hej] at Jj₀ Jj
  exact ⟨si, sj, β₀, H₀, ρ₀, κ₀, Hr₀, β, H, ρ, κ, Hr, Ji₀, Jj₀, Ji, Jj⟩

end ContinuousFlexibility.Statements
