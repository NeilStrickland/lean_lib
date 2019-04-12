import order.basic
import data.equiv.basic
import data.fintype
import logic.relation
import data.pos_list

universes uP uQ uR uS

variables (P : Type uP) [partial_order P]
variables (Q : Type uQ) [partial_order Q]
variables (R : Type uR) [partial_order R]
variables (S : Type uS) [partial_order S]

namespace poset 

def hom := { f : P → Q // monotone f } 

instance : has_coe_to_fun (hom P Q) := {
 F := λ _, P → Q,
 coe := λ f, f.val
}

def id : hom P P := ⟨_root_.id,monotone_id⟩

lemma id_val : (id P).val = _root_.id := rfl

variables {P Q R}

@[extensionality] 
lemma hom_ext (f₀ f₁ : hom P Q) (e : ∀ p, f₀ p = f₁ p) : f₀ = f₁ := 
 by {apply subtype.eq,funext p,exact e p}

instance hom_order : partial_order (hom P Q) := {
 le := λ f g, ∀ p, (f p) ≤ (g p),
 le_refl := λ f p,le_refl (f p),
 le_antisymm := λ f g f_le_g g_le_f,
  begin ext p, exact le_antisymm (f_le_g p) (g_le_f p), end,
 le_trans := λ f g h f_le_g g_le_h p,
   le_trans (f_le_g p) (g_le_h p)
}

@[simp]
lemma id_eval (p : P) : (id P) p = p := rfl

variable (P)
def const (q : Q) : hom P Q := ⟨λ p,q, λ p₀ p₁ hp, le_refl q⟩
variable {P}

def comp : (hom Q R) → (hom P Q) → (hom P R) := 
 λ g f, ⟨g.val ∘ f.val, monotone_comp f.property g.property⟩

lemma comp_val (g : hom Q R) (f : hom P Q) : 
 (comp g f).val = g.val ∘ f.val := rfl

lemma id_comp (f : hom P Q) : comp (id Q) f = f := by {ext, refl}
lemma comp_id (f : hom P Q) : comp f (id P) = f := by {ext, refl}
lemma comp_assoc (h : hom R S) (g : hom Q R) (f : hom P Q) : 
 comp (comp h g) f = comp h (comp g f) := by {ext, refl}

lemma const_comp (r : R) (f : hom P Q) :
 comp (const Q r) f = const P r := by {ext, refl}

lemma comp_const (g : hom Q R) (q : Q) :
 comp g (const P q) = const P (g q) := by {ext, refl}

lemma comp_mono₂ {g₀ g₁ : hom Q R} {f₀ f₁ : hom P Q} 
 (eg : g₀ ≤ g₁) (ef : f₀ ≤ f₁) : comp g₀ f₀ ≤ comp g₁ f₁ := 
 λ p, calc 
  g₀.val (f₀.val p) ≤ g₀.val (f₁.val p) : g₀.property (ef p)
  ... ≤ g₁.val (f₁.val p) : eg (f₁.val p)

@[simp]
lemma comp_eval (g : hom Q R) (f : hom P Q) (p : P) : 
 (comp g f) p = g (f p) := rfl

def comp' : (hom Q R) × (hom P Q) → (hom P R) := 
 λ ⟨g,f⟩, comp g f

lemma comp'_mono : monotone (@comp' P _ Q _ R _) := 
 λ ⟨g₀,f₀⟩ ⟨g₁,f₁⟩ ⟨eg,ef⟩, comp_mono₂ eg ef

def eval : (hom P Q) → P → Q := λ f p, f.val p

lemma eval_mono₂ {f₀ f₁ : hom P Q} {p₀ p₁ : P} 
 (ef : f₀ ≤ f₁) (ep : p₀ ≤ p₁) : eval f₀ p₀ ≤ eval f₁ p₁ := 
calc 
  f₀.val p₀ ≤ f₀.val p₁ : f₀.property ep
  ... ≤ f₁.val p₁ : ef p₁  

def eval' : (hom P Q) × P → Q := λ ⟨f,p⟩, eval f p

lemma eval'_mono : monotone (@eval' P _ Q _) := 
 λ ⟨f₀,p₀⟩ ⟨f₁,p₁⟩ ⟨ef,ep⟩, eval_mono₂ ef ep

def ins' : P → (hom Q (P × Q)) := 
 λ p, ⟨λ q,⟨p,q⟩, λ q₀ q₁ eq, ⟨le_refl p,eq⟩⟩ 

lemma ins_mono : monotone (@ins' P _ Q _) := 
 λ p₀ p₁ ep q, ⟨ep,le_refl q⟩

variable (P)
def π₀ : Type* := quot (has_le.le : P → P → Prop)
variable {P}

def component (p : P) : π₀ P := quot.mk _ p

def connected : P → P → Prop := λ p₀ p₁, component p₀ = component p₁ 

lemma π₀.sound {p₀ p₁ : P} (hp : p₀ ≤ p₁) : 
 component p₀ = component p₁ := quot.sound hp

lemma π₀.epi {X : Type*} (f₀ f₁ : π₀ P → X) 
 (h : ∀ p, f₀ (component p) = f₁ (component p)) : f₀ = f₁ := 
  by {apply funext, rintro ⟨p⟩, exact (h p),}

def π₀.lift {X : Type*} (f : P → X)
 (h : ∀ p₀ p₁ : P, p₀ ≤ p₁ → f p₀ = f p₁) : 
  (π₀ P) → X := @quot.lift P has_le.le X f h

lemma π₀.lift_beta {X : Type*} (f : P → X)
 (h : ∀ p₀ p₁ : P, p₀ ≤ p₁ → f p₀ = f p₁) (p : P) :
  π₀.lift f h (component p) = f p := 
   @quot.lift_beta P has_le.le X f h p 

def π₀.lift₂ {X : Type*} (f : P → Q → X)
 (h : ∀ p₀ p₁ q₀ q₁, p₀ ≤ p₁ → q₀ ≤ q₁ → f p₀ q₀ = f p₁ q₁) : 
  (π₀ P) → (π₀ Q) → X := 
begin
 let h1 := λ p q₀ q₁ hq, h p p q₀ q₁ (le_refl p) hq,
 let f1 : P → (π₀ Q) → X := λ p, π₀.lift (f p) (h1 p),
 let hf1 : ∀ p q, f1 p (component q) = f p q := λ p, π₀.lift_beta (f p) (h1 p),
 let h2 : ∀ p₀ p₁, p₀ ≤ p₁ → f1 p₀ = f1 p₁ := λ p₀ p₁ hp,
  begin
   apply π₀.epi,intro q,rw[hf1,hf1],
   exact h p₀ p₁ q q hp (le_refl q),
  end,
 exact π₀.lift f1 h2
end

lemma π₀.lift₂_beta {X : Type*} (f : P → Q → X)
 (h : ∀ p₀ p₁ q₀ q₁, p₀ ≤ p₁ → q₀ ≤ q₁ → f p₀ q₀ = f p₁ q₁)
  (p : P) (q : Q) : (π₀.lift₂ f h) (component p) (component q) = f p q := 
begin
 unfold π₀.lift₂,simp only [],rw[π₀.lift_beta,π₀.lift_beta],
end
  
variables (P Q)
def homₕ := π₀ (hom P Q)

def idₕ : homₕ P P := component (id P)

variables {P Q}

def compₕ : (homₕ Q R) → (homₕ P Q) → (homₕ P R) := 
 π₀.lift₂ (λ g f, component (comp g f)) (begin 
  intros g₀ g₁ f₀ f₁ hg hf,
  let hgf := comp_mono₂ hg hf,
  let hgf' := π₀.sound hgf,
  exact (π₀.sound (comp_mono₂ hg hf))
 end)

lemma compₕ_def (g : hom Q R) (f : hom P Q) : 
 compₕ (component g) (component f) = component (comp g f) := 
  by {simp[compₕ,π₀.lift₂_beta]}

lemma id_compₕ (f : homₕ P Q) : compₕ (idₕ Q) f = f := 
 begin 
  rcases f with f,
  change compₕ (component (id Q)) (component f) = component f,
  rw[compₕ_def,id_comp],
 end 

lemma comp_idₕ (f : homₕ P Q) : compₕ f (idₕ P) = f := 
 begin 
  rcases f with f,
  change compₕ (component f) (component (id P)) = component f,
  rw[compₕ_def,comp_id],
 end 

lemma comp_assocₕ (h : homₕ R S) (g : homₕ Q R) (f : homₕ P Q) : 
 compₕ (compₕ h g) f = compₕ h (compₕ g f) := 
 begin
  rcases h with h, rcases g with g, rcases f with f,
  change compₕ (compₕ (component h) (component g)) (component f) =
         compₕ (component h) (compₕ (component g) (component f)),
  repeat {rw[compₕ_def]},rw[comp_assoc],
 end

def π₀.map (f : hom P Q) : (π₀ P) → (π₀ Q) := 
 π₀.lift (λ p, component (f p)) (λ p₀ p₁ ep, quot.sound (f.property ep))

lemma π₀.map_def (f : hom P Q) (p : P) : π₀.map f (component p) = component (f p) := 
 by {simp[π₀.map,π₀.lift_beta]}

lemma π₀.map_congr {f₀ f₁ : hom P Q} (ef : f₀ ≤ f₁) : π₀.map f₀ = π₀.map f₁ := 
 begin 
  apply π₀.epi,intro p,rw[π₀.map_def,π₀.map_def],
  exact π₀.sound (ef p),
 end

variable (P)
lemma π₀.map_id : π₀.map (id P) = _root_.id := 
 by { apply π₀.epi, intro p, rw[π₀.map_def], refl }
variable {P}

lemma π₀.map_comp (g : hom Q R) (f : hom P Q) :
 π₀.map (comp g f) = (π₀.map g) ∘ (π₀.map f) := 
  by { apply π₀.epi, intro p, rw[π₀.map_def], refl }

def evalₕ : (homₕ P Q) → (π₀ P) → (π₀ Q) := 
 π₀.lift π₀.map (@π₀.map_congr _ _ _ _)

variables (P Q R S)

structure homₕᵢ := 
(to_fun : homₕ P Q)
(inv_fun : homₕ Q P)
(left_inv : compₕ inv_fun to_fun = idₕ P)
(right_inv : compₕ to_fun inv_fun = idₕ Q)

def idₕᵢ : homₕᵢ P P := {
 to_fun := idₕ P,
 inv_fun := idₕ P,
 left_inv := comp_idₕ _,
 right_inv := id_compₕ _,
}

end poset