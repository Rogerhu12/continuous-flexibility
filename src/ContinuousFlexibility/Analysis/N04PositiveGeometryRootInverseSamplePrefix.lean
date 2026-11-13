import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseDifferentialDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseLabelSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOddPowerPrefix

/-!
# The actual inverse differential at the retained positive sample

All three scalar prefixes share one low base. Their enlarged angular
horizons align the high seminorm and power denominator before the
inverse-label substitution. The original context and atlas are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04RootInverseSampleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_rootInverseDifferential_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m → ∀ Kcur : CanonicalData W.S,
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C Kcur base ε m (!side),
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_rootInverseDifferential W.D W.S W.C hctx.choose m (!side)),
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
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  obtain ⟨Bo, hBo, po⟩ := n04PositiveGeometry_rootOddPowerTrace_sample_prefix_five
    W X hb hε hεW hεone hflow
  obtain ⟨Be, hBe, pe⟩ := n04PositiveGeometry_rootBoundaryFormula_sample_prefix_five
    W X hb hε hεW hεone hflow
  obtain ⟨Bl, hBl, pl⟩ := n04PositiveGeometry_rootInverseLabel_sample_prefix W X hb hε hεW hflow
  obtain ⟨RH, hRH, hheight⟩ := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let L := max 1 RH
  have hL : 1 ≤ L := le_max_left _ _
  let low := Bo + Be + Bl
  have hol : Bo ≤ low := by dsimp only [low]; omega
  have hel : Be ≤ low := by dsimp only [low]; omega
  have hll : Bl ≤ low := by dsimp only [low]; omega
  refine ⟨low, hBo.trans hol, fun K => ?_⟩
  obtain ⟨co, poc⟩ := po (-(2 / 3 : ℝ)) K
  obtain ⟨ce, pec⟩ := pe K
  obtain ⟨cl, plc⟩ := pl K
  let c := co + ce + cl
  have hco : co ≤ c := by dsimp only [c]; omega
  have hce : ce ≤ c := by dsimp only [c]; omega
  have hcl : cl ≤ c := by dsimp only [c]; omega
  refine ⟨c + 1, fun s => ?_⟩
  let so := s + (c + 1 - co) * K
  let se := s + (c + 1 - ce) * K
  let sl := s + (c + 1 - cl) * K
  obtain ⟨Ao, hAo, ho⟩ := poc so
  obtain ⟨Ae, hAe, he⟩ := pec se
  obtain ⟨Al, hAl, hl⟩ := plc sl
  let B := Ao + Ae + Al + L
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  have hAoB : Ao ≤ B := by dsimp only [B]; linarith
  have hAeB : Ae ≤ B := by dsimp only [B]; linarith
  have hAlB : Al ≤ B := by dsimp only [B]; linarith
  have hLB : L ≤ B := by dsimp only [B]; linarith
  obtain ⟨C, hC, degree, hd, hbound⟩ :=
    n04PositiveGeometry_rootInverseDifferential_word_bound W.D W.S W.C K s L hL
  obtain ⟨A₀, hA₀, hpack⟩ := coefficientEnvelope_pack (C * B ^ degree) (B * degree)
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hA₀A : A₀ ≤ A := le_max_right _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm Kcur hctx Q z hz hzlow θ R hR hzR
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := B * E ^ B
  let t := R ^ (1 / (((s + (c + 1) * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + (c + 1) * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (hheight i).1
  have hHL : H ≤ L := (hheight i).2.trans (le_max_right _ _)
  have hBM : B ≤ M := le_mul_of_one_le_right (zero_le_one.trans hB)
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have hM : 1 ≤ M := hB.trans hBM
  have hHM : H ≤ M := hHL.trans (hLB.trans hBM)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {a : ℝ} (ha : a ≤ B) : a * E ^ a ≤ M :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE ha)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hden (a : ℕ) (ha : a ≤ c) :
      (s + (c + 1 - a) * K) + a * K = s + (c + 1) * K := by
    calc
      _ = s + ((c + 1 - a) + a) * K := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : a ≤ c + 1)]
  have hspan (a : ℕ) (ha : a ≤ c) : s + K ≤ s + (c + 1 - a) * K := by
    exact Nat.add_le_add_left (by
      simpa only [one_mul] using Nat.mul_le_mul_right K (show 1 ≤ c + 1 - a by omega)) s
  have hhigh (l a : ℕ) (hlow : l ≤ low) (ha : a ≤ c) :
      l + (s + (c + 1 - a) * K) + a * K + 1 ≤ low + s + (c + 1) * K + 1 := by
    have heq := hden a ha
    omega
  have htpow (a : ℕ) : t ^ a =
      R ^ ((a : ℝ) / (((s + (c + 1) * K : ℕ) : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
    congr 1
    ring
  have hfinish {a u k : ℕ} {Z v : ℝ} (ha : a ≤ c)
      (hZ : Z ≤ M * parameterHeightWeight H k)
      (hv : ‖v‖ ≤ Z * R ^ (((u + a * k : ℕ) : ℝ) /
        ((((s + (c + 1 - a) * K) + a * K : ℕ) : ℝ) + 1))) :
      ‖v‖ ≤ M * parameterHeightWeight H k * t ^ (u + c * k) := by
    have hpow : R ^ (((u + a * k : ℕ) : ℝ) /
        ((((s + (c + 1 - a) * K) + a * K : ℕ) : ℝ) + 1)) ≤ t ^ (u + c * k) := by
      rw [hden a ha, ← htpow (u + a * k)]
      exact pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_right k ha) u)
    exact hv.trans (mul_le_mul hZ hpow (Real.rpow_nonneg (zero_le_one.trans hR) _)
      (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH k)))
  have hrad : n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
    have h : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact h.symm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D := by
    rw [hrad]; exact (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 := by
    rw [hrad]; exact (W.roots i side).2.1
  let g := hctx.choose
  let ρ := hctx.choose_spec.choose
  let hρ := hctx.choose_spec.choose_spec.choose
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  have href := (hc.2.2.2.2 (W.C.referenceState, 0)
    (reference_mem_stateNeighborhood W.S W.C base hε) hN.2.2.1.stateSector).1
  have hstrip (y : StateDirections W.S × ℝ) (hy : y ∈ sectorNeighborhood W.S base ε ε) :=
    (hc.2.2.2.2 (liftSectorParameter W.S W.C y)
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hy le_rfl)
      (hN.2.2.1.liftSectorParameter_sector y)).1
  let JO := n04PositiveGeometry_rootOddPowerTrace_joint W.hT W.hS hN hεone hflow
    g hc.1 hc.2.1 m (!side) hr hroot hρ hstrip (-(2 / 3 : ℝ)) 0 (by omega)
  let JE := n04PositiveGeometry_rootBoundaryFormula_joint W.hT W.hS hN hεone
    g hc.1 hc.2.1 m (!side) hr hroot 0
  let Jα := n04Realization_rootLabel_inverseJointDirections W.hT W.hS hN m (!side)
  let Jb := n04PositiveGeometry_rootInverseDerivative_joint W.hT W.hS hN m (!side)
  let η := Function.invFun (n01RootLabel W.S W.C (liftSectorParameter W.S W.C z) m (!side)) θ
  have hO : N04BoundaryWordBounds JO K (s + K) 1 z η P M H t c := by
    apply n04PositiveGeometry_boundaryWord_of_angular JO (smoothDirections_angularStateSlice JO)
      K (s + K) 1 z hz η P M H t c
    intro k hk u hu d hd' v hv
    have h := ho i side m hm g hc.1 hc.2.1 hc.2.2.1 ρ hρ href hstrip
      0 (by omega) k hk u (hu.trans (hspan co hco)) d (by omega) η
      (smoothDirections_angularStateSlice JO (u + d) η) z hz ((hp hol z).trans hzlow)
      v (fun j => (hp hol (v j)).trans (hv j).1) R hR
      ((hp (hhigh Bo co hol hco) z).trans hzR)
      (fun j => (hp (hhigh Bo co hol hco) (v j)).trans (hv j).2)
    exact hfinish hco (mul_le_mul_of_nonneg_right (hcost hAoB) (parameterHeightWeight_nonneg hH k)) h
  have hE' : N04BoundaryWordBounds JE K (s + K) 1 z η P M H t c := by
    apply n04PositiveGeometry_boundaryWord_of_angular JE (smoothDirections_angularStateSlice JE)
      K (s + K) 1 z hz η P M H t c
    intro k hk u hu d hd' v hv
    have h := he i side m hm g hc.1 hc.2.1 hc.2.2.1 ρ hρ href
      0 k hk u (hu.trans (hspan ce hce)) d (by omega) η
      (smoothDirections_angularStateSlice JE (u + d) η) z hz ((hp hel z).trans hzlow)
      v (fun j => (hp hel (v j)).trans (hv j).1) R hR
      ((hp (hhigh Be ce hel hce) z).trans hzR)
      (fun j => (hp (hhigh Be ce hel hce) (v j)).trans (hv j).2)
    exact hfinish hce (mul_le_mul_of_nonneg_right (hcost hAeB) (parameterHeightWeight_nonneg hH k)) h
  have hlabel := hl i side m hm Jα Jb z hz ((hp hll z).trans hzlow) θ R hR
    ((hp (hhigh Bl cl hll hcl) z).trans hzR)
  have htlabel : R ^ (1 / (((sl + cl * K : ℕ) : ℝ) + 1)) = t := by
    rw [show sl + cl * K = s + (c + 1) * K from hden cl hcl]
  have hlabelcost (n : ℕ) (w : StateAngleWord n) :
      Al * E ^ Al * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - 1) + cl * w.stateArity) ≤
      M * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - 1) + c * w.stateArity) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hcost hAlB) (parameterHeightWeight_nonneg hH _))
      (pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcl) _))
      (pow_nonneg (zero_le_one.trans ht) _)
      (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
  have hα : N04BoundaryPositiveWordBounds Jα K (s + K) 1 z θ P M H t c := by
    intro n hn w hk ha v hv hvP
    have h := hlabel.1 n hn w hk (ha.trans (Nat.add_le_add_right (hspan cl hcl) 1)) v hv
      (fun j => ⟨(hp hll _).trans (hvP j).1,
        (hp (hhigh Bl cl hll hcl) _).trans (hvP j).2⟩)
    rw [htlabel] at h
    exact h.trans (hlabelcost n w)
  have hb' : N04BoundaryWordBounds Jb K s 1 z θ P M H t c := by
    intro n w hk ha v hv hvP
    have h := hlabel.2 n w hk (by have hspan' := hspan cl hcl; omega) v hv
      (fun j => ⟨(hp hll _).trans (hvP j).1,
        (hp (hhigh Bl cl hll hcl) _).trans (hvP j).2⟩)
    rw [htlabel] at h
    exact h.trans (hlabelcost n w)
  have hout := hbound g m (!side) (sectorNeighborhood_isOpen W.S base ε ε) JO JE Jα Jb Q
    (fun y hy => (n04PositiveGeometry_rootOddTrace_zero_pos W.hT W.hS hN hflow
      g m (!side) hρ hy.1 (hstrip y.1 hy.1) y.2).le)
    z hz θ (p low) (p (low + s + (c + 1) * K + 1)) R (zero_le_one.trans hR)
    M H t hM hH hHM hHL ht c hO hE' hα hb'
  apply hout.enlarge hH (zero_le_one.trans ht)
  calc
    C * M ^ degree = (C * B ^ degree) * E ^ (B * degree) := by
      dsimp only [M]
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
      ring
    _ ≤ A₀ * E ^ A₀ := hpack E hE
    _ ≤ A * E ^ A := mul_le_mul hA₀A (Real.rpow_le_rpow_of_exponent_le hE hA₀A)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)

end ContinuousFlexibility.Analysis
