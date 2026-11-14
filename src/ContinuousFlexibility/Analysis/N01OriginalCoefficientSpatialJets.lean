module

public import ContinuousFlexibility.Analysis.N01CoefficientSpatialJets
public import ContinuousFlexibility.Analysis.SmoothDirectionsConstantShift

/-!
# Full original coefficients in the actual mixed parameter/spatial tower

The reference coefficient contributes only at parameter order zero.
Every positive genuine parameter jet agrees with the coefficient
increment tower, so all its spatial derivatives retain the original
N01 estimate. The zero-order spatial identity adds back the actual
reference derivative and gives the genuine parameter recurrence at
every order, including the first derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01OriginalCoefficientSpatialJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def originalCoefficientEntry (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (i : Fin 3) (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  if i = 0 then (originalCoefficients D S C z).a else
    if i = 1 then (originalCoefficients D S C z).b else (originalCoefficients D S C z).c

theorem N01Properties.originalCoefficientSectorTower_positive_eq
    (hN : N01Properties D T S C base loss ε)
    (j : ℕ) (i : Fin 3) (p : PolarPoint) (hp : p.1 ∈ D.cells j)
    (n : ℕ) (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → StateDirections S × ℝ) :
    (hN.originalCoefficientSectorTower j i p hp).D (n + 1) x v =
      (hN.sectorCoefficientTower j i 0 0 p hp).D (n + 1) x v := by
  apply (hN.originalCoefficientSectorTower j i p hp).positive_jet_eq_of_constant_shift
    (hN.sectorCoefficientTower j i 0 0 p hp)
    (originalCoefficientEntry D S C i (C.referenceState, 0) p) _ n x hx v
  intro y hy
  simp only [coefficientFamily, mixedDerivative, iteratedDeriv_zero,
    originalCoefficientEntry, ite_apply]
  split_ifs <;> ring

def N01Properties.originalComponentCoefficientScalarJet
    (hN : N01Properties D T S C base loss ε)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (n : ℕ) (x : StateDirections S × ℝ)
    (v : Fin n → StateDirections S × ℝ) : PolarPoint → ℝ :=
  localScalarJet
    (fun p (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) =>
      hN.originalCoefficientSectorTower j i p (hcell hp.1)) n x v

theorem N01Properties.originalComponentCoefficientScalarJet_zero
    (hN : N01Properties D T S C base loss ε)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (v : Fin 0 → StateDirections S × ℝ) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    hN.originalComponentCoefficientScalarJet m j hcell i 0 x v p =
      originalCoefficientEntry D S C i (liftSectorParameter S C x) p := by
  have hlocal := localScalarJet_of_mem
    (fun q (hq : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) =>
      hN.originalCoefficientSectorTower j i q (hcell hq.1)) 0 x v hp
  have hv : v = Fin.elim0 := Subsingleton.elim _ _
  have hzero := (hN.originalCoefficientSectorTower j i p (hcell hp.1)).zero x hx
  exact hlocal.trans ((congrArg (fun vs =>
    (hN.originalCoefficientSectorTower j i p (hcell hp.1)).D 0 x vs) hv).trans
      (hzero.trans (by simp only [originalCoefficientEntry, ite_apply])))

theorem N01Properties.originalComponentCoefficientScalarJet_positive_eq
    (hN : N01Properties D T S C base loss ε)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (n : ℕ) (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → StateDirections S × ℝ) :
    hN.originalComponentCoefficientScalarJet m j hcell i (n + 1) x v =
      hN.componentCoefficientScalarJet m j hcell i (n + 1) x v := by
  classical
  funext p
  by_cases hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
  · have hlocal := localScalarJet_of_mem
      (fun q (hq : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) =>
        hN.originalCoefficientSectorTower j i q (hcell hq.1)) (n + 1) x v hp
    exact hlocal.trans ((hN.originalCoefficientSectorTower_positive_eq j i p
      (hcell hp.1) n x hx v).trans
        (hN.componentCoefficientScalarJet_of_mem m j hcell i (n + 1) x v hp).symm)
  · simp only [originalComponentCoefficientScalarJet, componentCoefficientScalarJet,
      localScalarJet, dif_neg hp]

private theorem original_component_subset_annular
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) ⊆ annularOpen D := by
  intro p hp
  have hends := hN.2.2.2.1.1 m
  exact ⟨⟨hends.1.trans hp.1.1, hp.1.2.trans hends.2.2⟩, mem_univ _⟩

theorem N01Properties.originalComponentCoefficientScalarJet_contDiffOn
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (n : ℕ) (x : StateDirections S × ℝ)
    (hx : x ∈ sectorNeighborhood S base ε ε) (v : Fin n → StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (hN.originalComponentCoefficientScalarJet m j hcell i n x v)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  cases n with
  | zero =>
      have h := (hN.original_coefficient_contDiffOn hS hT
        (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
        (hN.2.2.1.liftSectorParameter_sector x) i).mono
          (original_component_subset_annular hN m)
      apply h.congr
      intro p hp
      exact hN.originalComponentCoefficientScalarJet_zero m j hcell i x hx v hp
  | succ n =>
      have heq := hN.originalComponentCoefficientScalarJet_positive_eq m j hcell i n x hx v
      exact (congrArg (fun f : PolarPoint → ℝ => ContDiffOn ℝ ∞ f
        (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))) heq).mpr
          (hN.componentCoefficientScalarJet_contDiffOn hS hT m j hcell i (n + 1) x hx v)

theorem N01Properties.originalComponentCoefficientScalarJet_mixedDerivative_zero
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (a b : ℕ) (x : StateDirections S × ℝ)
    (hx : x ∈ sectorNeighborhood S base ε ε) (v : Fin 0 → StateDirections S × ℝ)
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    mixedDerivative a b (hN.originalComponentCoefficientScalarJet m j hcell i 0 x v) p =
      coefficientFamily D S C i a b p (liftSectorParameter S C x) +
        mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p := by
  have hlocal := mixedDerivative_congr_on_open (isOpen_Ioo.prod isOpen_univ)
    (fun q hq => hN.originalComponentCoefficientScalarJet_zero m j hcell i x hx v hq) a b hp
  have hcurrent := hN.original_coefficient_contDiffOn hS hT
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (hN.2.2.1.liftSectorParameter_sector x) i
  have href := hN.original_coefficient_contDiffOn hS hT hN.reference_mem_stateNeighborhood
    hN.2.2.1.stateSector i
  have hdiff := mixedDerivative_sub_of_contDiffOn
    (isOpen_Ioo.prod isOpen_univ) hcurrent href a b (original_component_subset_annular hN m hp)
  have hdiff' : coefficientFamily D S C i a b p (liftSectorParameter S C x) =
      mixedDerivative a b (originalCoefficientEntry D S C i (liftSectorParameter S C x)) p -
        mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p := hdiff
  exact hlocal.trans (eq_add_of_sub_eq hdiff'.symm)

theorem N01Properties.originalComponentCoefficientScalarJet_mixedDerivative_positive
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (a b n : ℕ) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → StateDirections S × ℝ) :
    mixedDerivative a b (hN.originalComponentCoefficientScalarJet m j hcell i (n + 1) x v) p =
      (hN.sectorCoefficientTower j i a b p (hcell hp.1)).D (n + 1) x v :=
  (congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
    (hN.originalComponentCoefficientScalarJet_positive_eq m j hcell i n x hx v)).trans
      (hN.componentCoefficientScalarJet_mixedDerivative hS hT m j hcell i a b (n + 1) hp x hx v)

theorem N01Properties.originalComponentCoefficientScalarJet_hasDerivAt_line
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (a b n : ℕ) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (x w : StateDirections S × ℝ) {t : ℝ}
    (ht : x + t • w ∈ sectorNeighborhood S base ε ε) (v : Fin n → StateDirections S × ℝ) :
    HasDerivAt
      (fun s => mixedDerivative a b
        (hN.originalComponentCoefficientScalarJet m j hcell i n (x + s • w) v) p)
      (mixedDerivative a b (hN.originalComponentCoefficientScalarJet m j hcell i (n + 1)
        (x + t • w) (Fin.cons w v)) p) t := by
  have hnear : ∀ᶠ s in 𝓝 t, x + s • w ∈ sectorNeighborhood S base ε ε :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
      ((sectorNeighborhood_isOpen S base ε ε).mem_nhds ht)
  cases n with
  | zero =>
      let J := hN.sectorCoefficientTower j i a b p (hcell hp.1)
      let c := mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p
      have hd := (J.hasDerivAt_line x w ht).add_const c
      have hv : (fun _ : Fin 1 => w) = Fin.cons w v := by
        funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i => exact Fin.elim0 i
      have hvalue : J.D 1 (x + t • w) (fun _ => w) =
          mixedDerivative a b (hN.originalComponentCoefficientScalarJet m j hcell i 1
            (x + t • w) (Fin.cons w v)) p :=
        (congrArg (fun vs => J.D 1 (x + t • w) vs) hv).trans
          (hN.originalComponentCoefficientScalarJet_mixedDerivative_positive hS hT
            m j hcell i a b 0 hp (x + t • w) ht (Fin.cons w v)).symm
      apply (hd.congr_deriv hvalue).congr_of_eventuallyEq
      filter_upwards [hnear] with s hs
      exact hN.originalComponentCoefficientScalarJet_mixedDerivative_zero hS hT
        m j hcell i a b (x + s • w) hs v hp
  | succ n =>
      have hd := hN.componentCoefficientScalarJet_hasDerivAt_line hS hT
        m j hcell i a b (n + 1) hp x w ht v
      have hvalue := congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
        (hN.originalComponentCoefficientScalarJet_positive_eq m j hcell i (n + 1)
          (x + t • w) ht (Fin.cons w v))
      apply (hd.congr_deriv hvalue.symm).congr_of_eventuallyEq
      filter_upwards [hnear] with s hs
      exact congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
        (hN.originalComponentCoefficientScalarJet_positive_eq m j hcell i n (x + s • w) hs v)

end ContinuousFlexibility.Statements
