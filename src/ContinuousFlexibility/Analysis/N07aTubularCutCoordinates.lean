import ContinuousFlexibility.Analysis.N07aSmoothLocalCoordinates
import ContinuousFlexibility.Analysis.N07aTubularLocalSigns
import ContinuousFlexibility.Analysis.N07aTubularDifferential
import ContinuousFlexibility.Analysis.N07aClosedChartDifferentials
import ContinuousFlexibility.Analysis.N07aCurrentCutMeasure

/-!
# Genuine smooth tubular coordinates around the current middle cut

The angular curve is the actual common inverse-chart boundary. Its normal
direction is the left inverse derivative at the chosen center. The scalar
left chart radius identifies the two physical sides on one closed rectangle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

def n07aTubularCutMap (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (k : ℕ) (θ₀ : ℝ) (p : PolarPoint) : PolarPoint :=
  canonicalCutPoint S K z k p.2 + (p.1 - K.cutRadius k) •
    fderiv ℝ (K.inverseChart z (K.cutPair k).1) (K.cutRadius k, θ₀) (1, 0)

theorem n07aTubularCutMap_cut (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (k : ℕ) (θ₀ θ : ℝ) :
    n07aTubularCutMap S K z k θ₀ (K.cutRadius k, θ) = canonicalCutPoint S K z k θ := by
  simp only [n07aTubularCutMap, sub_self, zero_smul, add_zero]

/-- The stored inverse germ is a genuine left inverse on a physical neighborhood. -/
theorem n07a_boundaryInverseGerm_eventually_leftInverse
    {F G : PolarPoint → PolarPoint} {p : PolarPoint}
    (h : CanonicalBoundaryInverseGerm F G p) :
    ∀ᶠ x in 𝓝 p, G (F x) = x := by
  obtain ⟨e, he, hp, _, hG⟩ := h
  have hF : ContinuousAt F p := he ▸ e.continuousAt hp
  have hnear : (fun x => G (F x)) =ᶠ[𝓝 p] (fun x => e.symm (F x)) :=
    hG.comp_tendsto hF
  have hinv : ∀ᶠ x in 𝓝 p, e.symm (F x) = x := by
    simpa only [he] using e.eventually_left_inverse hp
  exact hnear.trans hinv

structure N07aTubularCutCoordinates (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (k : ℕ) (θ₀ : ℝ) where
  left : ℝ
  right : ℝ
  lower : ℝ
  upper : ℝ
  left_lt : left < K.cutRadius k
  lt_right : K.cutRadius k < right
  lower_lt : lower < θ₀
  lt_upper : θ₀ < upper
  e : OpenPartialHomeomorph PolarPoint PolarPoint
  coe_map : (e : PolarPoint → PolarPoint) = n07aTubularCutMap S K z k θ₀
  map_smooth : ContDiff ℝ ∞ (e : PolarPoint → PolarPoint)
  inverse_smooth : ContDiffOn ℝ ∞ e.symm e.target
  closed_source : Icc left right ×ˢ Icc lower upper ⊆ e.source
  component : MapsTo e (Icc left right ×ˢ Icc lower upper)
    (Ioo (C.left k) (C.right k) ×ˢ (univ : Set ℝ))
  cut_eq : ∀ θ, e (K.cutRadius k, θ) = canonicalCutPoint S K z k θ
  left_mem_iff : ∀ p ∈ Icc left right ×ˢ Icc lower upper,
    e p ∈ physicalPieceOpen S K z (K.cutPair k).1 ↔ p.1 < K.cutRadius k
  right_mem_iff : ∀ p ∈ Icc left right ×ˢ Icc lower upper,
    e p ∈ physicalPieceOpen S K z (K.cutPair k).2 ↔ K.cutRadius k < p.1
  left_open : MapsTo e (Ioo left (K.cutRadius k) ×ˢ Ioo lower upper)
    (physicalPieceOpen S K z (K.cutPair k).1)
  right_open : MapsTo e (Ioo (K.cutRadius k) right ×ˢ Ioo lower upper)
    (physicalPieceOpen S K z (K.cutPair k).2)
  left_closed : MapsTo e (Icc left (K.cutRadius k) ×ˢ Icc lower upper)
    (physicalPieceClosed S K z (K.cutPair k).1)
  right_closed : MapsTo e (Icc (K.cutRadius k) right ×ˢ Icc lower upper)
    (physicalPieceClosed S K z (K.cutPair k).2)
  inverse_fderiv : fderiv ℝ e.symm (canonicalCutPoint S K z k θ₀) =
    fderiv ℝ (K.chart z (K.cutPair k).1) (canonicalCutPoint S K z k θ₀)

theorem n07a_tubularCutCoordinates_exists
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (k : ℕ) (θ₀ : ℝ) : Nonempty (N07aTubularCutCoordinates S C K z k θ₀) := by
  let R := K.cutRadius k
  let iL := (K.cutPair k).1
  let iR := (K.cutPair k).2
  let G := K.inverseChart z iL
  let F := K.chart z iL
  let Γ := canonicalCutPoint S K z k
  let H := n07aTubularCutMap S K z k θ₀
  let q₀ : PolarPoint := (R, θ₀)
  let N : Set PolarPoint := Ioo (C.left k) (C.right k) ×ˢ (univ : Set ℝ)
  obtain ⟨_, _, _, _, _, hR, hlzero, _, hright, _⟩ := h04.2.1.1.1 k
  have hq (θ : ℝ) : (R, θ) ∈ canonicalClosed S K iL := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · change K.left (K.cutPair k).1 ≤ K.cutRadius k
      simpa only [hlzero] using hR.le
    · exact hright.symm.le
  have hFG (θ : ℝ) : F (Γ θ) = (R, θ) :=
    (h04.1.boundary z hz hs iL).2.2.2.1 _ (hq θ)
  have hΓ : ContDiff ℝ ∞ Γ := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    exact (n04b_inverseChart_contDiffAt_closed h04.1 hz hs iL (hq θ)).comp θ
      (contDiffAt_const.prodMk contDiffAt_id)
  have hH : ContDiff ℝ ∞ H :=
    (hΓ.comp contDiff_snd).add ((contDiff_fst.sub contDiff_const).smul contDiff_const)
  have hHline (θ : ℝ) : H (R, θ) = Γ θ := n07aTubularCutMap_cut S K z k θ₀ θ
  have hHcenter : H q₀ = Γ θ₀ := hHline θ₀
  have hG : ContDiffAt ℝ ∞ G q₀ :=
    n04b_inverseChart_contDiffAt_closed h04.1 hz hs iL (hq θ₀)
  have hHd : HasFDerivAt H (fderiv ℝ G q₀) q₀ :=
    n07a_tubularMap_hasFDerivAt (hG.differentiableAt (by simp))
  have hI := n07a_actualChart_fderiv_inverse_closed h04.1 hz hs iL (hq θ₀)
  have hleftInv : Function.LeftInverse (fderiv ℝ F (Γ θ₀)) (fderiv ℝ G q₀) :=
    fun v => congrArg (fun M : PolarPoint →L[ℝ] PolarPoint => M v) hI.1
  have hrightInv : Function.RightInverse (fderiv ℝ F (Γ θ₀)) (fderiv ℝ G q₀) :=
    fun v => congrArg (fun M : PolarPoint →L[ℝ] PolarPoint => M v) hI.2
  let A := planeLinearEquivOfBijective (fderiv ℝ G q₀)
    ⟨hleftInv.injective, hrightInv.surjective⟩
  have hA : (A : PolarPoint →L[ℝ] PolarPoint) = fderiv ℝ G q₀ :=
    planeLinearEquivOfBijective_coe _ _
  have hAsymm : (A.symm : PolarPoint →L[ℝ] PolarPoint) = fderiv ℝ F (Γ θ₀) := by
    apply ContinuousLinearMap.ext
    intro v
    have heq := hleftInv (A.symm v)
    rw [← hA] at heq
    simpa only [ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using heq.symm
  obtain ⟨e, he, hqe, _, _, hinvs, _, hdinv⟩ :=
    n07a_smoothLocalCoordinates hH q₀ A (hHd.congr_fderiv hA.symm)
  have hinverse : fderiv ℝ e.symm (Γ θ₀) = fderiv ℝ F (Γ θ₀) := by
    simpa only [hHcenter, hAsymm] using hdinv
  have hcut := h04.2.1.1.2 z hz hs k
  have hdis : Disjoint (physicalPieceOpen S K z iL) (physicalPieceOpen S K z iR) :=
    hcut.2.2.1
  have hcover : physicalPieceOpen S K z iL ∪ physicalPieceOpen S K z iR =
      N \ Set.range Γ := hcut.2.2.2.1
  have hnotleft (θ : ℝ) : Γ θ ∉ physicalPieceOpen S K z iL := by
    intro hθ
    have hp : Γ θ ∈ physicalPieceOpen S K z iL ∪ physicalPieceOpen S K z iR := Or.inl hθ
    rw [hcover] at hp
    exact hp.2 ⟨θ, rfl⟩
  have hfront : Γ θ₀ ∈ frontier (physicalPieceOpen S K z iL) := by
    rw [(h04.1.domains z hz hs iL).1.frontier_eq]
    exact ⟨(n07a_currentCutPoint_mem_closed h04 hz hs k θ₀).1, hnotleft θ₀⟩
  have hGF : ∀ᶠ x in 𝓝 (Γ θ₀), G (F x) = x :=
    n07a_boundaryInverseGerm_eventually_leftInverse
      ((h04.1.boundary z hz hs iL).2.2.2.2.2 _ hfront)
  have hF : ContDiffAt ℝ ∞ F (Γ θ₀) :=
    ((h04.1.boundary z hz hs iL).2.2.2.2.1 _
      (n07a_currentCutPoint_mem_closed h04 hz hs k θ₀).1).1
  have hFatH : ContDiffAt ℝ ∞ F (H q₀) := by rw [hHcenter]; exact hF
  let ψ : PolarPoint → ℝ := fun q => (F (H q)).1
  have hψ : ContDiffAt ℝ 1 ψ q₀ :=
    ((hFatH.comp q₀ hH.contDiffAt).fst).of_le (by simp)
  have hψline (θ : ℝ) : ψ (R, θ) = R := by
    change (F (H (R, θ))).1 = R
    rw [hHline, hFG]
  have hψrad : radialPartial ψ q₀ = 1 := by
    have hd := ((hFatH.differentiableAt (by simp)).hasFDerivAt.comp q₀ hHd).fst
    have hcomp : (fderiv ℝ F (H q₀)).comp (fderiv ℝ G q₀) =
        ContinuousLinearMap.id ℝ PolarPoint := by
      rw [hHcenter]
      exact hI.1
    change fderiv ℝ (fun q => ((F ∘ H) q).1) q₀ (1, 0) = 1
    rw [hd.fderiv, hcomp]
    rfl
  have hHt : Tendsto H (𝓝 q₀) (𝓝 (Γ θ₀)) := by
    simpa only [hHcenter] using (hH.continuous.continuousAt (x := q₀)).tendsto
  have hN : N ∈ 𝓝 (Γ θ₀) :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds (hcut.2.1 ⟨θ₀, rfl⟩)
  have hψpos : 0 < ψ q₀ := by rw [hψline]; exact hR
  let U : Set PolarPoint := {q | q ∈ e.source ∧ H q ∈ N ∧
    G (F (H q)) = H q ∧ 0 < ψ q}
  have hU : U ∈ 𝓝 q₀ := by
    filter_upwards [e.open_source.mem_nhds hqe, hHt.eventually hN,
      hHt.eventually hGF, hψ.continuousAt.eventually (Ioi_mem_nhds hψpos)]
      with q hqe hqN hqGF hqpos
    exact ⟨hqe, hqN, hqGF, hqpos⟩
  obtain ⟨l, r, a, b, hl, hr, ha, hb, hrect, hsign⟩ :=
    n07a_exists_closedRectangle_radialSigns hψ (by rw [hψrad]; norm_num) hψline hU
  have hleft (p : PolarPoint) (hp : p ∈ Icc l r ×ˢ Icc a b) :
      H p ∈ physicalPieceOpen S K z iL ↔ p.1 < R := by
    constructor
    · intro hpx
      have hrad := ((h04.1.charts z hz hs iL).1 hpx).1.2
      rw [hright] at hrad
      exact ((hsign p.1 hp.1 p.2 hp.2).1).mp hrad
    · intro hpR
      have hcanonical : F (H p) ∈ canonicalOpen S K iL := by
        refine ⟨⟨?_, ?_⟩, mem_univ _⟩
        · rw [hlzero]
          exact (hrect hp).2.2.2
        · rw [hright]
          exact ((hsign p.1 hp.1 p.2 hp.2).1).mpr hpR
      have hm := (h04.1.charts z hz hs iL).2.1 hcanonical
      change G (F (H p)) ∈ physicalPieceOpen S K z iL at hm
      rw [(hrect hp).2.2.1] at hm
      exact hm
  have hrightSide (p : PolarPoint) (hp : p ∈ Icc l r ×ˢ Icc a b) :
      H p ∈ physicalPieceOpen S K z iR ↔ R < p.1 := by
    constructor
    · intro hpx
      have hnleft : ¬p.1 < R := fun hlt =>
        Set.disjoint_left.mp hdis ((hleft p hp).mpr hlt) hpx
      have hncut : H p ∉ Set.range Γ := by
        have hu : H p ∈ physicalPieceOpen S K z iL ∪ physicalPieceOpen S K z iR := Or.inr hpx
        rw [hcover] at hu
        exact hu.2
      have hne : p.1 ≠ R := by
        intro heq
        apply hncut
        refine ⟨p.2, ?_⟩
        simpa only [← heq, Prod.eta] using (hHline p.2).symm
      rcases lt_or_eq_of_le (le_of_not_gt hnleft) with hlt | heq
      · exact hlt
      · exact False.elim (hne heq.symm)
    · intro hpR
      have hψgt := ((hsign p.1 hp.1 p.2 hp.2).2).mpr hpR
      have hncut : H p ∉ Set.range Γ := by
        rintro ⟨θ, hθ⟩
        have heq := congrArg Prod.fst (hFG θ)
        rw [hθ] at heq
        exact (ne_of_gt hψgt) heq
      have hu : H p ∈ physicalPieceOpen S K z iL ∪ physicalPieceOpen S K z iR := by
        rw [hcover]
        exact ⟨(hrect hp).2.1, hncut⟩
      exact hu.elim (fun hpx => False.elim ((not_lt_of_ge hpR.le) ((hleft p hp).mp hpx))) id
  refine ⟨{
    left := l
    right := r
    lower := a
    upper := b
    left_lt := hl
    lt_right := hr
    lower_lt := ha
    lt_upper := hb
    e := e
    coe_map := he
    map_smooth := he ▸ hH
    inverse_smooth := hinvs
    closed_source := fun p hp => (hrect hp).1
    component := ?_
    cut_eq := ?_
    left_mem_iff := ?_
    right_mem_iff := ?_
    left_open := ?_
    right_open := ?_
    left_closed := ?_
    right_closed := ?_
    inverse_fderiv := hinverse }⟩
  · intro p hp
    simpa only [he] using (hrect hp).2.1
  · intro θ
    rw [he]
    exact hHline θ
  · intro p hp
    simpa only [he] using hleft p hp
  · intro p hp
    simpa only [he] using hrightSide p hp
  · intro p hp
    rw [he]
    apply (hleft p ⟨⟨hp.1.1.le, hp.1.2.le.trans hr.le⟩, Ioo_subset_Icc_self hp.2⟩).mpr
    exact hp.1.2
  · intro p hp
    rw [he]
    apply (hrightSide p ⟨⟨hl.le.trans hp.1.1.le, hp.1.2.le⟩, Ioo_subset_Icc_self hp.2⟩).mpr
    exact hp.1.1
  · rintro ⟨s, θ⟩ hp
    rw [he]
    change H (s, θ) ∈ physicalPieceClosed S K z iL
    rcases lt_or_eq_of_le (show s ≤ R from hp.1.2) with hsR | heq
    · exact subset_closure ((hleft (s, θ) ⟨⟨hp.1.1, hsR.le.trans hr.le⟩, hp.2⟩).mpr hsR)
    · rw [heq, hHline]
      exact (n07a_currentCutPoint_mem_closed h04 hz hs k θ).1
  · rintro ⟨s, θ⟩ hp
    rw [he]
    change H (s, θ) ∈ physicalPieceClosed S K z iR
    rcases lt_or_eq_of_le (show R ≤ s from hp.1.1) with hRs | heq
    · exact subset_closure ((hrightSide (s, θ) ⟨⟨hl.le.trans hRs.le, hp.1.2⟩, hp.2⟩).mpr hRs)
    · rw [← heq, hHline]
      exact (n07a_currentCutPoint_mem_closed h04 hz hs k θ).2

end ContinuousFlexibility.Analysis
