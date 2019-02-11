/-
    Stalk of rings on basis.

    https://stacks.math.columbia.edu/tag/007L
    (just says that the category of rings is a type of algebraic structure)
-/

import preliminaries.opens
import topology.basic
import sheaves.stalk_on_basis
import sheaves.presheaf_of_rings_on_basis

universe u 

open topological_space

section stalk_of_rings_on_standard_basis

variables {α : Type u} [topological_space α] 
variables {B : set (opens α )} {HB : opens.is_basis B}

-- Standard basis. TODO: Move somewhere else?

--def opens.univ : opens α := ⟨set.univ, is_open_univ⟩
variables (Bstd : (⟨set.univ, is_open_univ⟩ : opens α) ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

variables (F : presheaf_of_rings_on_basis α HB) (x : α)

definition stalk_of_rings_on_standard_basis := 
stalk_on_basis F.to_presheaf_on_basis x

-- TODO: Is this useful??

protected def mka (a) : stalk_of_rings_on_standard_basis F x := ⟦ a ⟧

theorem mk_eq_mk_iff_associated : ∀ (a b),
mka F x a = mka F x b ↔ stalk_on_basis.relation F.to_presheaf_on_basis x a b :=
λ a b, iff.intro quotient.exact quot.sound

theorem quotient_mk_eq_mk (a) : ⟦ a ⟧ = mka F x a := rfl

theorem quot_mk_eq_mk (a) : quot.mk setoid.r a = mka F x a := rfl

-- TODO: This is not working...

instance : has_coe (presheaf_of_rings_on_basis α HB) (presheaf_on_basis α HB) :=
{ coe := λ F, F.to_presheaf_on_basis }

section stalk_is_ring

-- One.

private def stalk_of_rings_one : stalk_of_rings_on_standard_basis F x := 
⟦{U := ⟨set.univ, is_open_univ⟩, BU := Bstd.1, Hx := trivial, s:= 0}⟧

instance stalk_of_rings_has_one : has_one (stalk_of_rings_on_standard_basis F x) := 
{one := stalk_of_rings_one Bstd F x}

-- Add.

-- def stalk_of_rings_elem_add :
-- stalk_on_basis.elem F.to_presheaf_on_basis x → 
-- stalk_on_basis.elem F.to_presheaf_on_basis x → 
-- stalk_on_basis.elem F.to_presheaf_on_basis x :=
-- λ s t, 
-- {U := s.U ∩ t.U, 
-- BU := Bstd.2 s.BU t.BU,
-- Hx := ⟨s.Hx, t.Hx⟩, 
-- s := F.res s.BU _ (set.inter_subset_left _ _) s.s + 
--      F.res t.BU _ (set.inter_subset_right _ _) t.s}

-- instance : has_add (stalk_on_basis.elem F.to_presheaf_on_basis x) :=
-- {add := stalk_of_rings_elem_add Bstd F x }

set_option pp.notation false

lemma stalk : ∀ (a b c : stalk_on_basis.elem F.to_presheaf_on_basis x),
a + b + c = a + (b + c) :=
begin 
    rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
    unfold has_add.add,
    unfold stalk_of_rings_elem_add,
    dsimp,
    have HUVW1 : U ∩ V ∩ W ⊆ U ∩ (V ∩ W) := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
    have HUVW2 : U ∩ (V ∩ W) ⊆ U ∩ V ∩ W := λ x ⟨HxU, ⟨HxV, HxW⟩⟩, ⟨⟨HxU, HxV⟩, HxW⟩, 
    have HUVW : U ∩ V ∩ W = U ∩ (V ∩ W) := opens.ext (set.eq_of_subset_of_subset HUVW1 HUVW2),
    rw stalk_on_basis.elem.mk.inj_eq,
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf_on_basis.Hcomp' },
    repeat { rw ←add_assoc },
    let F' := F.to_presheaf_on_basis,
    show F'.res _ _ _ sW + F'.res _ _ _ sU + F'.res _ _ _ sV ==
         F'.res _ _ _ sU + F'.res _ _ _ sV + F'.res _ _ _ sW,
    rw add_comm (F'.res _ _ _ sW) (F'.res _ _ _ sU),
    repeat { rw add_assoc },
    rw add_comm (F'.res _ _ _ sW) (F'.res _ _ _ sV),
    
end

@[reducible] def stalk_of_rings_add_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s t, 
⟦stalk_of_rings_elem_add F x s t⟧

include Bstd
@[reducible] def stalk_of_rings_add :
stalk_on_basis F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
quotient.lift₂ (stalk_of_rings_add_aux F x) $
begin
    intros a1 a2 b1 b2 H1 H2, 
    let F' := F.to_presheaf_on_basis,
    rcases H1 with ⟨U1, ⟨BU1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩⟩,
    rcases H2 with ⟨U2, ⟨BU2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩⟩,
    have BU1U2 := Bstd.2 BU1 BU2,
    apply quotient.sound,
    use [U1 ∩ U2, BU1U2, ⟨HxU1, HxU2⟩],
    use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    have HresU1' : 
        (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res a1.BU BU1 HU1a1U) (a1.s))) =
        (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res b1.BU BU1 HU1b1U) (b1.s)))
    := by rw HresU1,
    have HresU2' :
        (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res a2.BU BU2 HU2a2U) (a2.s))) =
        (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res b2.BU BU2 HU2b2U) (b2.s)))
    := by rw HresU2,
    repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU1' },
    repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU2' },
    repeat { rw ←(presheaf_on_basis.Hcomp' F') },
    rw [HresU1', HresU2'],
end

@[reducible, priority 10000] def evoc : has_add (stalk_of_rings_on_standard_basis F x) := 
{add := stalk_of_rings_add Bstd F x }


include Bstd
@[simp] lemma stalk_of_rings_mk_add_aux
: ∀ (a b), mka F x (stalk_of_rings_elem_add Bstd F x a b) = 
stalk_of_rings_add Bstd F x (mka F x a) (mka F x b) :=
λ a b, 
begin 
    repeat { rw ←quotient_mk_eq_mk  },
    unfold stalk_of_rings_add,
    apply quotient.sound,
    simp,
end  


@[simp] lemma stalk_of_rings_mk_add
: ∀ (a b : stalk_on_basis.elem F.to_presheaf_on_basis x), mka F x (a + b) = (mka F x a) + (mka F x b) :=
λ a b, 
begin 
    apply stalk_of_rings_mk_add_aux,
end  

lemma stalk_of_rings_add_assoc 
[has_add (stalk_of_rings_on_standard_basis F x)] 
: ∀ (a b c : stalk_of_rings_on_standard_basis F x), a + b + c = a + (b + c) := 
begin
    intros a b c,
    refine quotient.induction_on₃ a b c _,
    rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
    have BUVW := Bstd.2 (Bstd.2 BU BV) BW,
    have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W) 
    := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
    apply quotient.sound,
    use [U ∩ V ∩ W, BUVW, ⟨⟨HxU, HxV⟩, HxW⟩],
    use [set.subset.refl _, HUVWsub],
    dsimp,
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf_on_basis.Hcomp' },
    rw add_assoc,
end

-- Zero.

private def stalk_of_rings_zero : stalk_of_rings_on_standard_basis F x := 
⟦{U := opens.univ, BU := Bstandard.1, Hx := trivial, s:= 0}⟧

instance stalk_of_rings_has_zero : has_zero (stalk_of_rings_on_standard_basis F x) := 
{zero := stalk_of_rings_zero F x}

instance stalk_of_rings_add_monoid : add_monoid (stalk_of_rings_on_standard_basis F x) :=
{add := stalk_of_rings_add F x,
add_assoc := stalk_of_rings_add_assoc F x,
zero := stalk_of_rings_zero F x,
zero_add :=
begin
    intros a,
    refine quotient.induction_on a _,
    rintros ⟨U, BU, HxU, sU⟩,
    apply quotient.sound,
    have HUsub : U ⊆ opens.univ ∩ U := λ x HxU, ⟨trivial, HxU⟩,
    use [U, BU, HxU, HUsub, set.subset.refl U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf_on_basis.Hcomp' },
    erw (is_ring_hom.map_zero ((F.to_presheaf_on_basis).res _ _ _));
    try { apply_instance },
    rw zero_add,
    refl,
end,
add_zero := 
begin
    intros a,
    refine quotient.induction_on a _,
    rintros ⟨U, BU, HxU, sU⟩,
    apply quotient.sound,
    have HUsub : U ⊆ U ∩ opens.univ := λ x HxU, ⟨HxU, trivial⟩,
    use [U, BU, HxU, HUsub, set.subset.refl U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf_on_basis.Hcomp' },
    dsimp, -- TODO: Can I get rid of this???
    erw (is_ring_hom.map_zero ((F.to_presheaf_on_basis).res _ _ _));
    try { apply_instance },
    rw add_zero,
    refl,
end}

def stalk_of_rings_zero_add := (stalk_of_rings_add_monoid F x).zero_add

def stalk_of_rings_add_zero := (stalk_of_rings_add_monoid F x).add_zero

-- Neg.

private def stalk_of_rings_neg_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s, ⟦{U := s.U, BU := s.BU, Hx := s.Hx, s := -s.s}⟧

def stalk_of_rings_neg :
stalk_on_basis F.to_presheaf_on_basis x →
stalk_on_basis F.to_presheaf_on_basis x :=
quotient.lift (stalk_of_rings_neg_aux F x) $ 
begin
    intros a b H,
    rcases H with ⟨U, ⟨BU, ⟨HxU, ⟨HUaU, HUbU, HresU⟩⟩⟩⟩,
    apply quotient.sound,
    use [U, BU, HxU, HUaU, HUbU],
    repeat { rw @is_ring_hom.map_neg _ _ _ _ _ (F.res_is_ring_hom _ _ _) },
    rw HresU,
end

instance stalk_of_rings_has_neg : has_neg (stalk_of_rings_on_standard_basis F x) :=
{neg := stalk_of_rings_neg F x}

instance stalk_of_rings_add_group : add_group (stalk_of_rings_on_standard_basis F x) :=
{add := stalk_of_rings_add F x,
add_assoc := stalk_of_rings_add_assoc F x,
zero := stalk_of_rings_zero F x,
zero_add := stalk_of_rings_zero_add F x,
add_zero := stalk_of_rings_add_zero F x,
neg := sorry,
add_left_neg := sorry}

-- Mul. TODO: Basically the same as add, what can be done about this?

private def stalk_of_rings_mul_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s t, 
⟦{U := s.U ∩ t.U, 
BU := Bstandard.2 s.BU t.BU,
Hx := ⟨s.Hx, t.Hx⟩, 
s := F.res s.BU _ (set.inter_subset_left _ _) s.s * 
     F.res t.BU _ (set.inter_subset_right _ _) t.s}⟧

instance stalk_of_rings_has_mul : has_mul (stalk_of_rings_on_standard_basis F x) := 
{mul := quotient.lift₂ (stalk_of_rings_mul_aux F x) $ 
begin
    intros a1 a2 b1 b2 H1 H2, 
    let F' := F.to_presheaf_on_basis,
    rcases H1 with ⟨U1, ⟨BU1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩⟩,
    rcases H2 with ⟨U2, ⟨BU2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩⟩,
    have BU1U2 := Bstandard.2 BU1 BU2,
    apply quotient.sound,
    use [U1 ∩ U2, BU1U2, ⟨HxU1, HxU2⟩],
    use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    have HresU1' : 
        (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res a1.BU BU1 HU1a1U) (a1.s))) =
        (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res b1.BU BU1 HU1b1U) (b1.s)))
    := by rw HresU1,
    have HresU2' :
        (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res a2.BU BU2 HU2a2U) (a2.s))) =
        (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res b2.BU BU2 HU2b2U) (b2.s)))
    := by rw HresU2,
    repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU1' },
    repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU2' },
    repeat { rw ←(presheaf_on_basis.Hcomp' F') },
    rw [HresU1', HresU2'],
end}

-- Stalks are rings.

instance stalk_of_rings_is_ring : comm_ring (stalk_of_rings_on_standard_basis F x) :=
{   add := stalk_of_rings_add F x,
    add_assoc := stalk_of_rings_add_assoc F x,
    zero := stalk_of_rings_zero F x,
    zero_add := stalk_of_rings_zero_add F x,
    add_zero := stalk_of_rings_add_zero F x,
    neg := has_neg.neg,
    add_left_neg := 
    begin
        intros a,
        refine quotient.induction_on a _,
        rintros ⟨U, BU, HxU, sU⟩,
        apply quotient.sound,
        have HUUU : U ⊆ U ∩ U := λ x HxU, ⟨HxU, HxU⟩,
        have HUuniv : U ⊆ opens.univ := λ x HxU, trivial,
        use [U, BU, HxU, HUUU, HUuniv],
        repeat { rw (F.res_is_ring_hom _ _ _).map_add },
        repeat { rw ←presheaf_on_basis.Hcomp' },
        erw (is_ring_hom.map_neg ((F.to_presheaf_on_basis).res _ _ _));
        try { apply_instance },
        rw add_left_neg,
        erw (is_ring_hom.map_zero ((F.to_presheaf_on_basis).res _ _ _));
        try { apply_instance },
    end,
    add_comm := sorry,
    mul := (stalk_of_rings_has_mul F x).mul,
    mul_assoc := sorry,
    mul_one := sorry,
    one := (stalk_of_rings_has_one F x).one,
    one_mul := sorry,
    left_distrib := sorry,
    right_distrib := sorry,
    mul_comm := sorry,
}

end stalk_is_ring

end stalk_of_rings_on_standard_basis
