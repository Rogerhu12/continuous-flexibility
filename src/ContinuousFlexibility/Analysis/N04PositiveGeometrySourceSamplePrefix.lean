import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceJets
import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredInverseSamplePrefix

/-!
# Sampled full spatial jets of the original endpoint source

The reference jets admit every later parameter shift. Their finite
composition with the actual inverse jets therefore preserves the common
high denominator, the material height, and the full angular reserve.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04SourceSampleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_sourceJet_sample_prefix
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
        (n04PositiveGeometry_sourceJet W.S W.C (X.src i side) (W.A X.e₀) n),
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
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  have hA : CanonicalGeometry W.D W.S W.C (W.A X.e₀) base ε :=
    n04PartA_restrict (n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field X.e₀) hb hεW
  obtain ⟨low, hlow, pinverse⟩ :=
    n04PositiveGeometry_storedInverseJet_sample_prefix W X hb hε hεW hεone hflow
  obtain ⟨RH, hRH, hheight⟩ := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  refine ⟨low, hlow, fun K => ?_⟩
  obtain ⟨shift, pshift⟩ := pinverse K
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨Ai, hAi, hinverse⟩ := pshift s
  obtain ⟨Ar, hAr, hreference⟩ :=
    n04PositiveGeometry_referenceForwardJet_sample_prefix W X hb hε hεW hεone hflow s
  let B := Ai + Ar + max 1 RH
  have hB : 1 ≤ B := by have := le_max_left (1 : ℝ) RH; dsimp only [B]; linarith
  have hAiB : Ai ≤ B := by have := le_max_left (1 : ℝ) RH; dsimp only [B]; linarith
  have hArB : Ar ≤ B := by have := le_max_left (1 : ℝ) RH; dsimp only [B]; linarith
  have hRHB : RH ≤ B := by have := le_max_right (1 : ℝ) RH; dsimp only [B]; linarith
  let N := K + s + 1
  choose cj hcj hcomposition using fun j : Fin 4 =>
    n04PositiveGeometry_boundaryComposition_bound (X := StateDirections W.S × ℝ)
      (E := PolarPoint) (F := PolarPoint) (G := PolarPoint) N (j.val + 1) (by omega)
  let C := 1 + ∑ j : Fin 4, cj j
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => zero_le_one.trans (hcj j))
  have hcjC (j : Fin 4) : cj j ≤ C :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hcj j)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  let degree := 5 + 2 * N
  obtain ⟨A₀, hA₀, hpack⟩ := coefficientEnvelope_pack (16 * C * B ^ degree) (B * degree)
  let A := max 1 A₀
  have hAA : A₀ ≤ A := le_max_right _ _
  have hAone : 1 ≤ A := le_max_left _ _
  refine ⟨A, hAone, ?_⟩
  intro i side m hm hctx n hn hn4 Q z hz hzlow θ R hR hzR
  let p := pairGrading (sectorGrading W.S) realGrading
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := B * E ^ B
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R
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
  have hrad := n04PositiveGeometry_sourceEndpoint_eq_root (X.src i side) hm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D := hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 := hrad.symm ▸ (W.roots i side).2.1
  let F := fun y : (StateDirections W.S × ℝ) × ℝ =>
    (W.A X.e₀).inverseChart (liftSectorParameter W.S W.C y.1)
      (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1)
  let G := fun _y : (StateDirections W.S × ℝ) × ℝ =>
    (W.A X.e₀).chart (W.C.referenceState, 0)
      (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1)
  let q := fun y : (StateDirections W.S × ℝ) × ℝ => (n04PositiveEndpoint i side, y.2)
  have hreg := fun y hy => n04PositiveGeometry_sourceComposite_regularities
    W.hT W.hS hN hflow hA (X.src i side) hm hctx (y := y) hy
  let JI : ∀ j, 1 ≤ j → j ≤ n → SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_storedInverseJet W.S W.C (W.A X.e₀) m (!side) j) := fun j hj hjn =>
    n04PositiveGeometry_storedInverseJet_joint W.hT W.hS hN hεone hflow hA hctx
      hr hroot j hj (hjn.trans hn4)
  let JF : ∀ j, 1 ≤ j → j ≤ n → SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y => iteratedFDeriv ℝ j (F y) (G y (q y))) := fun j hj hjn =>
    (JI j hj hjn).congr (fun y hy => congrArg (iteratedFDeriv ℝ j (F y)) (hreg y hy).1.symm)
  let JR : ∀ j, 1 ≤ j → j ≤ n → SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_referenceForwardJet W.S W.C (W.A X.e₀) m (!side) j) := fun j hj hjn =>
    n04PositiveGeometry_referenceForwardJet_joint W.hT W.hS hN hε hεone hflow
      hctx hr hroot j hj (hjn.trans hn4)
  let JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → PolarPoint, SmoothDirections
      (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (G y) (q y) v) := fun j hj hjn v =>
    (n04PositiveGeometry_boundaryFixedEvaluation_directions (JR j hj hjn) v).congr
      (fun _ _ => by rw [n04PositiveGeometry_referenceForwardJet, hrad])
  have hJF (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      N04BoundaryWordBounds (JF j hj hjn) K s 1 z θ P M H t shift := by
    have h := hinverse i side m hm hctx j hj (hjn.trans hn4) (JI j hj hjn)
      z hz hzlow θ R hR hzR
    exact (h.enlarge hH (zero_le_one.trans ht) (hcost hAiB)).congr hz
      (fun y hy => congrArg (iteratedFDeriv ℝ j (F y)) (hreg y hy).1.symm)
  have hJG (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) (v : Fin j → PolarPoint)
      (hv : ∀ a, ‖v a‖ ≤ 1) : N04BoundaryWordBounds (JG j hj hjn v) K s 1 z θ P M H t shift := by
    have h := hreference i side m hm hctx j hj (hjn.trans hn4) (JR j hj hjn)
      K shift z hz θ P t ht
    exact ((h.enlarge hH (zero_le_one.trans ht) (hcost hArB)).fixedEvaluation v hv).congr hz
      (fun _ _ => by rw [n04PositiveGeometry_referenceForwardJet, hrad])
  let JE (w : Fin n → Fin 2) := n04PositiveGeometry_boundaryFixedEvaluation_directions Q
    (fun a => cylinderBasisVector (w a))
  have hunit (a : Fin 2) : ‖cylinderBasisVector a‖ ≤ 1 := by
    fin_cases a <;> norm_num [cylinderBasisVector, Prod.norm_def]
  have hJE (w : Fin n → Fin 2) :
      N04BoundaryWordBounds (JE w) K s 1 z θ P (C * M ^ degree) H t shift := by
    let j₄ : Fin 4 := ⟨n - 1, by omega⟩
    have hj₄ : j₄.val + 1 = n := Nat.sub_add_cancel hn
    have hc := hcomposition j₄
    rw [hj₄] at hc
    let JC : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y => iteratedFDeriv ℝ n (F y ∘ G y) (q y) (fun a => cylinderBasisVector (w a))) :=
      (JE w).congr (fun y _ => by
        unfold n04PositiveGeometry_sourceJet
        rw [n04PositiveGeometry_sourceMap_eq_rootComposite (X.src i side) (W.A X.e₀) hm])
    have hb := hc (sectorNeighborhood_isOpen W.S base ε ε) F G q
      (fun y hy => (hreg y hy).2.1) (fun y hy => (hreg y hy).2.2) JF JG
      K s 1 le_rfl z hz θ P M H t hM hH hHM ht shift hJF hJG
      (fun a => cylinderBasisVector (w a))
      (fun a => hunit (w a)) JC
    have hbound : cj j₄ * M ^ (n + 1 + 2 * N) ≤ C * M ^ degree :=
      mul_le_mul (hcjC j₄) (pow_le_pow_right₀ hM (by dsimp only [degree]; omega))
        (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC)
    exact (hb.enlarge hH (zero_le_one.trans ht) hbound).congr hz (fun y _ => by
      unfold n04PositiveGeometry_sourceJet
      rw [n04PositiveGeometry_sourceMap_eq_rootComposite (X.src i side) (W.A X.e₀) hm])
  have hout := N04BoundaryWordBounds.of_planeBasis Q JE hz
    (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hM) _))
    hH (zero_le_one.trans ht) hJE
  apply hout.enlarge hH (zero_le_one.trans ht)
  have htwo : (2 : ℝ) ^ n ≤ 16 :=
    (pow_le_pow_right₀ (by norm_num) hn4).trans_eq (by norm_num)
  calc
    (2 : ℝ) ^ n * (C * M ^ degree) ≤ 16 * (C * M ^ degree) :=
      mul_le_mul_of_nonneg_right htwo
        (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hM) _))
    _ = (16 * C * B ^ degree) * E ^ (B * degree) := by
      dsimp only [M]
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
      ring
    _ ≤ A₀ * E ^ A₀ := hpack E hE
    _ ≤ A * E ^ A := mul_le_mul hAA (Real.rpow_le_rpow_of_exponent_le hE hAA)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hAone)

end ContinuousFlexibility.Analysis
