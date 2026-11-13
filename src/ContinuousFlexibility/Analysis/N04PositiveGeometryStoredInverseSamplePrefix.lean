import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredInverseJets
import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredForwardSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFiniteCalculus

/-!
# Sampled bounds for the original full inverse jets

The forward jets move along the actual inverse root label. A single
extra parameter shift pays for this substitution, and the finite inverse
recursion retains the same reserve and material weight.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04StoredInverseSampleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_storedInverseJet_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀)
        base ε m (!side), ∀ n : ℕ, 1 ≤ n → n ≤ 4 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_storedInverseJet W.S W.C (W.A X.e₀) m (!side) n),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds Q K s 1 z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  classical
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  have hA : CanonicalGeometry W.D W.S W.C (W.A X.e₀) base ε :=
    n04PartA_restrict (n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field X.e₀) hb hεW
  let forwardData := n04PositiveGeometry_storedForwardJet_sample_prefix
    W X hb hε hεW hεone hflow
  let Bf : ℕ := forwardData.choose
  have hBf : base ≤ Bf := forwardData.choose_spec.1
  let pf := forwardData.choose_spec.2
  let labelData := n04PositiveGeometry_rootInverseLabel_sample_prefix W X hb hε hεW hflow
  let Bl : ℕ := labelData.choose
  let pl := labelData.choose_spec.2
  let differentialData := n04PositiveGeometry_rootInverseDifferential_sample_prefix
    W X hb hε hεW hεone hflow
  let Bd : ℕ := differentialData.choose
  let pd := differentialData.choose_spec.2
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let RH : ℝ := heightData.choose
  have hheight := heightData.choose_spec.2
  let low := Bf + Bl + Bd
  have hfl : Bf ≤ low := by dsimp only [low]; omega
  have hll : Bl ≤ low := by dsimp only [low]; omega
  have hdl : Bd ≤ low := by dsimp only [low]; omega
  refine ⟨low, hBf.trans hfl, fun K => ?_⟩
  let forwardShiftData := pf K
  let cf : ℕ := forwardShiftData.choose
  let pfc := forwardShiftData.choose_spec
  let labelShiftData := pl K
  let cl : ℕ := labelShiftData.choose
  let plc := labelShiftData.choose_spec
  let differentialShiftData := pd K
  let cd : ℕ := differentialShiftData.choose
  let pdc := differentialShiftData.choose_spec
  let c := cf + cl + cd
  have hcf : cf ≤ c := by dsimp only [c]; omega
  have hcl : cl ≤ c := by dsimp only [c]; omega
  have hcd : cd ≤ c := by dsimp only [c]; omega
  refine ⟨c + 1, fun s => ?_⟩
  let forwardBoundData := pfc (s + (c + 1 - cf) * K)
  let Af : ℝ := forwardBoundData.choose
  have hAf : 1 ≤ Af := forwardBoundData.choose_spec.1
  let hf := forwardBoundData.choose_spec.2
  let labelBoundData := plc (s + (c + 1 - cl) * K)
  let Al : ℝ := labelBoundData.choose
  have hAl : 1 ≤ Al := labelBoundData.choose_spec.1
  let hl := labelBoundData.choose_spec.2
  let differentialBoundData := pdc (s + (c + 1 - cd) * K)
  let Ad : ℝ := differentialBoundData.choose
  have hAd : 1 ≤ Ad := differentialBoundData.choose_spec.1
  let hd := differentialBoundData.choose_spec.2
  have hRHone : 1 ≤ max (1 : ℝ) RH := le_max_left _ _
  have hRHmax : RH ≤ max (1 : ℝ) RH := le_max_right _ _
  let B := Af + Al + Ad + max 1 RH
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hAf, hAl, hAd, hRHone]
  have hAfB : Af ≤ B := by dsimp only [B]; linarith only [hAl, hAd, hRHone]
  have hAlB : Al ≤ B := by dsimp only [B]; linarith only [hAf, hAd, hRHone]
  have hAdB : Ad ≤ B := by dsimp only [B]; linarith only [hAf, hAl, hRHone]
  have hRHB : RH ≤ B := by dsimp only [B]; linarith only [hAf, hAl, hAd, hRHmax]
  let movingData (j : Fin 5) := n04PositiveGeometry_boundaryMoving_saved_word_bound
    (E := StateDirections W.S × ℝ) (F := PolarPoint [×j.val]→L[ℝ] PolarPoint) K s
  let cm (j : Fin 5) : ℝ := (movingData j).choose
  have hcm (j : Fin 5) : 1 ≤ cm j := (movingData j).choose_spec.1
  let hmoving (j : Fin 5) := (movingData j).choose_spec.2
  let Cm := 1 + ∑ j : Fin 5, cm j
  have hCm : 1 ≤ Cm := le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => zero_le_one.trans (hcm j))
  have hcmCm (j : Fin 5) : cm j ≤ Cm :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hcm j)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  let dm := 2 * (K + s + 1) + 2
  let inverseData := n04PositiveGeometry_boundaryInverse_plane_prefix_bound
    (X := StateDirections W.S × ℝ) (K + s + 1)
  let Ci : ℝ := inverseData.choose
  let di : ℕ := inverseData.choose_spec.2.choose
  let hinverse := inverseData.choose_spec.2.choose_spec.2
  let D := (1 + dm) * di
  have houter (M : ℝ) :
      Ci * ((1 + Cm) * M ^ (1 + dm)) ^ di = (Ci * (1 + Cm) ^ di) * M ^ D := by
    dsimp only [D]
    rw [mul_pow, ← pow_mul]
    ring
  let packData := n04PositiveGeometry_polynomial_sample_pack (Ci * (1 + Cm) ^ di) B D
  let A₀ : ℝ := packData.choose
  let hpack := packData.choose_spec.2
  let A := max 1 A₀
  have hAA : A₀ ≤ A := le_max_right _ _
  have hAone : 1 ≤ A := le_max_left _ _
  refine ⟨A, hAone, ?_⟩
  intro i side m hm hctx n hn hn4 Q z hz hzlow θ R hR hzR
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := B * E ^ B
  let t := R ^ (1 / (((s + (c + 1) * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + (c + 1) * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (hheight i).1
  have hBM : B ≤ M := le_mul_of_one_le_right (zero_le_one.trans hB)
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have hM : 1 ≤ M := hB.trans hBM
  have hHM : H ≤ M := (hheight i).2.trans (hRHB.trans hBM)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {a : ℝ} (ha : a ≤ B) : a * E ^ a ≤ M :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE ha)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hden (a : ℕ) (ha : a ≤ c) :
      s + (c + 1 - a) * K + a * K = s + (c + 1) * K :=
    n04PositiveGeometry_prefix_horizon s K a (c + 1) (by omega)
  have hspan (a : ℕ) (ha : a ≤ c) : s + K ≤ s + (c + 1 - a) * K :=
    Nat.add_le_add_left (by
      simpa only [one_mul] using Nat.mul_le_mul_right K (show 1 ≤ c + 1 - a by omega)) s
  have hhigh (b a : ℕ) (hbl : b ≤ low) (ha : a ≤ c) :
      b + (s + (c + 1 - a) * K) + a * K + 1 ≤ low + s + (c + 1) * K + 1 := by
    have he := hden a ha
    omega
  have hscale (a : ℕ) (ha : a ≤ c) :
      R ^ (1 / (((s + (c + 1 - a) * K + a * K : ℕ) : ℝ) + 1)) = t := by
    rw [hden a ha]
  have hscaleCost (a : ℝ) (a₀ : ℕ) (ha₀ : a₀ ≤ c) (N : ℕ) (w : StateAngleWord N) :
      a * E ^ a * parameterHeightWeight H w.stateArity *
        (R ^ (1 / (((s + (c + 1 - a₀) * K + a₀ * K : ℕ) : ℝ) + 1))) ^
          ((w.angleArity - 1) + a₀ * w.stateArity) =
      a * E ^ a * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - 1) + a₀ * w.stateArity) :=
    congrArg (fun u : ℝ => a * E ^ a * parameterHeightWeight H w.stateArity *
      u ^ ((w.angleArity - 1) + a₀ * w.stateArity)) (hscale a₀ ha₀)
  have hraise (a : ℝ) (ha : a ≤ B) (a₀ a₁ : ℕ) (hc : a₀ ≤ a₁) (N : ℕ) (w : StateAngleWord N) :
      a * E ^ a * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - 1) + a₀ * w.stateArity) ≤
      M * parameterHeightWeight H w.stateArity * t ^ ((w.angleArity - 1) + a₁ * w.stateArity) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hcost ha) (parameterHeightWeight_nonneg hH _))
      (pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _))
      (pow_nonneg (zero_le_one.trans ht) _)
      (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
  have hrad : n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D := hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 := hrad.symm ▸ (W.roots i side).2.1
  let Jα := n04Realization_rootLabel_inverseJointDirections W.hT W.hS hN m (!side)
  let Jb := n04PositiveGeometry_rootInverseDerivative_joint W.hT W.hS hN m (!side)
  let η := Function.invFun (n01RootLabel W.S W.C (liftSectorParameter W.S W.C z) m (!side)) θ
  have hlabel := hl i side m hm Jα Jb z hz ((hp hll z).trans hzlow) θ R hR
    ((hp (hhigh Bl cl hll hcl) z).trans hzR)
  have hα : N04BoundaryPositiveWordBounds Jα K (s + K) 1 z θ P M H t c := by
    intro N hNpos w hk ha v hv hvP
    have h := hlabel.1 N hNpos w hk (ha.trans (Nat.add_le_add_right (hspan cl hcl) 1)) v hv
      (fun j => ⟨(hp hll _).trans (hvP j).1, (hp (hhigh Bl cl hll hcl) _).trans (hvP j).2⟩)
    exact (h.trans_eq (hscaleCost Al cl hcl N w)).trans (hraise Al hAlB cl c hcl N w)
  let Jforward : ∀ j, 1 ≤ j → j ≤ 4 → SmoothDirections
      (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_storedForwardJet W.S W.C (W.A X.e₀) m (!side) j) :=
    fun j hj hj4 => n04PositiveGeometry_storedForwardJet_joint W.hT W.hS hN hεone hflow
      hctx hr hroot j hj hj4
  have hforward (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) :
      N04BoundaryWordBounds (Jforward j hj hj4) K (s + K) 1 z η P M H t c := by
    have hraw := hf i side m hm hctx j hj hj4 (Jforward j hj hj4) z hz
      ((hp hfl z).trans hzlow) η R hR ((hp (hhigh Bf cf hfl hcf) z).trans hzR)
    intro N w hk ha v hv hvP
    have h := hraw N w hk (ha.trans (Nat.add_le_add_right (hspan cf hcf) 1)) v hv
      (fun a => ⟨(hp hfl _).trans (hvP a).1, (hp (hhigh Bf cf hfl hcf) _).trans (hvP a).2⟩)
    exact (h.trans_eq (hscaleCost Af cf hcf N w)).trans (hraise Af hAfB cf c hcf N w)
  let JL := n04PositiveGeometry_storedInverseDifferential_joint W.hT W.hS hN hεone hflow
    hA hctx hr hroot
  let Jraw := JL.congr (fun y hy =>
    (n04PositiveGeometry_storedInverseBoundary_data W.hT W.hS hN hflow hA hctx hy).2.2)
  have hrawL := hd i side m hm (W.A X.e₀) hctx Jraw z hz ((hp hdl z).trans hzlow)
    θ R hR ((hp (hhigh Bd cd hdl hcd) z).trans hzR)
  have hL : N04BoundaryWordBounds JL K s 1 z θ P M H t (c + 1) := by
    have hraw : N04BoundaryWordBounds Jraw K s 1 z θ P M H t (c + 1) := by
      intro N w hk ha v hv hvP
      have h := hrawL N w hk (by have := hspan cd hcd; omega) v hv
        (fun a => ⟨(hp hdl _).trans (hvP a).1, (hp (hhigh Bd cd hdl hcd) _).trans (hvP a).2⟩)
      exact (h.trans_eq (hscaleCost Ad cd hcd N w)).trans
        (hraise Ad hAdB cd (c + 1) (by omega) N w)
    exact hraw.congr hz (fun y hy =>
      (n04PositiveGeometry_storedInverseBoundary_data W.hT W.hS hN hflow hA hctx hy).2.2.symm)
  let M' := (1 + Cm) * M ^ (1 + dm)
  have hM' := n04PositiveGeometry_power_product_cost (degree := dm) hCm hM
  let F := fun y : (StateDirections W.S × ℝ) × ℝ => (W.A X.e₀).chart (liftSectorParameter W.S W.C y.1)
    (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1)
  let G := fun y : (StateDirections W.S × ℝ) × ℝ => (W.A X.e₀).inverseChart (liftSectorParameter W.S W.C y.1)
    (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1)
  let q := fun y : (StateDirections W.S × ℝ) × ℝ => ((0, y.2) : PolarPoint)
  let JF : ∀ j, 2 ≤ j → j ≤ 4 → SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y => iteratedFDeriv ℝ j (F y) (G y (q y))) := fun j hj hj4 =>
    n04PositiveGeometry_storedForward_atInverse_joint W.hT W.hS hN hεone hflow
      hA hctx hr hroot j (by omega) hj4
  have hJF (j : ℕ) (hj : 2 ≤ j) (hj4 : j ≤ 4) :
      N04BoundaryWordBounds (JF j hj hj4) K s 1 z θ P M' H t (c + 1) := by
    let j₅ : Fin 5 := ⟨j, by omega⟩
    let JM := n04PositiveGeometry_boundaryMoving_directions (Jforward j (by omega) hj4) Jα
    have hmove := hmoving j₅ (Jforward j (by omega) hj4) Jα JM z hz θ
      (p low) (p (low + s + (c + 1) * K + 1)) R (zero_le_one.trans hR)
      M H t hM hH hHM ht c (hforward j (by omega) hj4) hα
    have hcostmove : cm j₅ * M ^ dm ≤ M' :=
      (mul_le_mul_of_nonneg_right (hcmCm j₅) (pow_nonneg (zero_le_one.trans hM) _)).trans hM'.2.2
    exact (hmove.enlarge hH (zero_le_one.trans ht) hcostmove).congr hz (fun y hy =>
      congrArg (iteratedFDeriv ℝ j (F y))
        (n04PositiveGeometry_storedInverseBoundary_data W.hT W.hS hN hflow hA hctx hy).1.symm)
  have hreg := fun y hy => n04PositiveGeometry_storedInverse_regularities W.hT W.hS hN hflow hA hctx
    (y := y) hy
  have hout := hinverse (sectorNeighborhood_isOpen W.S base ε ε) F G q
    (n04PositiveGeometry_storedInverseDifferential W.S W.C (W.A X.e₀) m (!side))
    (fun y hy => (hreg y hy).1) (fun y hy => (hreg y hy).2.1)
    (fun y hy => (hreg y hy).2.2.1) (fun y hy => (hreg y hy).2.2.2) JL JF
    K s 1 le_rfl z hz θ P M' H t hM'.1 hH (hHM.trans hM'.2.1) ht (c + 1)
    (hL.enlarge hH (zero_le_one.trans ht) hM'.2.1) hJF n hn hn4 Q
  apply hout.enlarge hH (zero_le_one.trans ht)
  calc
    Ci * M' ^ di = (Ci * (1 + Cm) ^ di) * M ^ D := houter M
    _ ≤ A₀ * E ^ A₀ := hpack E hE
    _ ≤ A * E ^ A := mul_le_mul hAA (Real.rpow_le_rpow_of_exponent_le hE hAA)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hAone)

end ContinuousFlexibility.Analysis
