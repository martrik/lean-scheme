/-
    Stalk (of types) on basis.

    https://stacks.math.columbia.edu/tag/009H
-/

import preliminaries.opens
import sheaves.presheaf_on_basis

open topological_space

universe u 

section stalk_on_basis

variables {α : Type u} [topological_space α] 
variables {B : set (opens α )} {HB : opens.is_basis B}

variables (Bstd : (⟨set.univ, is_open_univ⟩ : opens α) ∈ B 
                ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

variables (F : presheaf_on_basis α HB) (x : α)

include Bstd
structure stalk_on_basis.elem :=
(U  : opens α)
(BU : U ∈ B)
(Hx : x ∈ U)
(s  : F BU)

#check stalk_on_basis.elem Bstd F x

def stalk_of_rings_elem_add [∀ {U} (BU : U ∈ B), comm_ring (F BU)]:
stalk_on_basis.elem Bstd F x → 
stalk_on_basis.elem Bstd F x → 
stalk_on_basis.elem Bstd F x :=
λ s t, 
{U := s.U ∩ t.U, 
BU := Bstd.2 s.BU t.BU,
Hx := ⟨s.Hx, t.Hx⟩, 
s := F.res s.BU _ (set.inter_subset_left _ _) s.s + 
     F.res t.BU _ (set.inter_subset_right _ _) t.s}

variables [∀ {U} (BU : U ∈ B), comm_ring (F BU)]

instance : has_add (stalk_on_basis.elem Bstd F x) :=
{add := stalk_of_rings_elem_add Bstd F x }

-- Equivalence relation on the set of pairs. (U,s) ~ (V,t) iff there exists W 
-- open s.t. x ∈ W ⊆ U ∩ V, and s|W = t|W.

def stalk_on_basis.relation : stalk_on_basis.elem Bstd F x → stalk_on_basis.elem Bstd F x → Prop :=
λ Us Vt,
    ∃ W (BW : W ∈ B) (HxW : x ∈ W) (HWU : W ⊆ Us.U) (HWV : W ⊆ Vt.U),
    F.res Us.BU BW HWU Us.s = F.res Vt.BU BW HWV Vt.s

#check stalk_on_basis.relation Bstd F x

lemma stalk_on_basis.relation.reflexive : reflexive (stalk_on_basis.relation Bstd F x) :=
λ ⟨U, OU, HxU, s⟩, begin end --⟨U, OU, HxU, set.subset.refl _, set.subset.refl _, rfl⟩

lemma stalk_on_basis.relation.symmetric : symmetric (stalk_on_basis.relation Bstd F x) :=
λ Us Vt ⟨W, OW, HxW, HWU, HWV, Hres⟩, ⟨W, OW, HxW, HWV, HWU, Hres.symm⟩

lemma stalk_on_basis.relation.transitive : transitive (stalk_on_basis.relation Bstd F x) :=
λ ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
λ ⟨R, BR, HxR, HRU, HRV, HresR⟩ ⟨S, BS, HxS, HSV, HSW, HresS⟩,
have HxRS : x ∈ R ∩ S := ⟨HxR, HxS⟩,
let ⟨T, BT, HxT, HTRS⟩ := opens.is_basis_iff_nbhd.1 HB HxRS in
⟨T, BT, HxT, λ y Hy, HRU (HTRS Hy).1, λ y Hy, HSW (HTRS Hy).2,
have HTR : T ⊆ R := λ y Hy, (HTRS Hy).1,
have HTS : T ⊆ S := λ y Hy, (HTRS Hy).2,
have HURRS : _ := F.Hcomp BU BR BT HTR HRU,
have HVRRS : _ := F.Hcomp BV BR BT HTR HRV,
have HVSRS : _ := F.Hcomp BV BS BT HTS HSV,
have HWSRS : _ := F.Hcomp BW BS BT HTS HSW,
calc  F.res BU BT _ sU 
    = F.res BR BT _ (F.res BU BR _ sU) : congr_fun HURRS sU 
... = F.res BR BT _ (F.res BV BR _ sV) : congr_arg _ HresR
... = F.res BV BT _ sV                 : congr_fun HVRRS.symm sV
... = F.res BS BT _ (F.res BV BS _ sV) : congr_fun HVSRS sV
... = F.res BS BT _ (F.res BW BS _ sW) : congr_arg _ HresS
... = F.res BW BT _ sW                 : congr_fun HWSRS.symm sW⟩

lemma stalk_on_basis.relation.equivalence : equivalence (stalk_on_basis.relation F x) :=
⟨stalk_on_basis.relation.reflexive F x, 
stalk_on_basis.relation.symmetric F x,
stalk_on_basis.relation.transitive F x⟩

instance stalk_on_basis.setoid : setoid (stalk_on_basis.elem F x) :=
{ r := stalk_on_basis.relation F x,
  iseqv := stalk_on_basis.relation.equivalence F x }

-- We define a stalk as the set of stalk elements under the defined relation.

definition stalk_on_basis := quotient (stalk_on_basis.setoid F x)

end stalk_on_basis
